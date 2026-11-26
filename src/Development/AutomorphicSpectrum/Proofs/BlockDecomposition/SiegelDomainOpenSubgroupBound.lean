module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusConjugateUnipotentBounded
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalCompactFundamentalDomain
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactModNearOfFiltration
noncomputable section

set_option linter.unusedSectionVars false

open Topology GlobalTheory.UnipFlagCore

namespace GlobalTheory.CompanionTheory.StrongUnip

section Abstract

variable {S T : Type} [Ring S] [TopologicalSpace S] [IsTopologicalRing S] [Ring T] [TopologicalSpace T]
  [IsTopologicalRing T] {st : S →+ S}

theorem map_cay (π : S →+* T) (M : ℕ) (y : S) : π (cay M y) = cay M (π y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cay, map_sum, map_pow]

theorem compact_mod_near_of_filtration (S₀ : Subring S) (h : S)
    (N : ℕ → AddSubgroup S) (p : ℕ → S →+ S) (m : ℕ) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (hp : ∀ i, Continuous (p i)) (hpN : ∀ i x, p i x ∈ N i) (hpf : ∀ i, ∀ x ∈ N i, p i x = x)
    (hp0 : ∀ i, ∀ x ∈ S₀, p i x ∈ S₀) (hle : ∀ i, N (i + 1) ≤ N i)
    (hmul : ∀ i, ∀ x ∈ N i, ∀ y ∈ N i, x * y ∈ N (i + 1)) (hst : ∀ i, ∀ x ∈ N i, st x ∈ N i)
    (hz : ∀ x ∈ N m, x = 0)
    (π : S →+* T) (stT : T →+ T) (pT : ℕ → T →+ T) (hstT : Continuous stT) (hpT : ∀ i, Continuous (pT i))
    (hπs : ∀ x, π (st x) = stT (π x)) (hπp : ∀ i x, π (p i x) = pT i (π x))
    (D : Set T) (hD : D ∈ 𝓝 (1 : T)) :
    ∃ V ∈ 𝓝 (0 : T), ∀ K : Set S, IsCompact K → (∀ x ∈ K, π x ∈ V) → (∀ x, ∃ y ∈ S₀, x - y ∈ K) →
      ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', π g ∈ D) ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0) ∧
        ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0 →
          ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ N 0) ∧ ∃ k ∈ K', g = γ * k := by
  have h1 : st 1 = 1 := GlobalTheory.TwoStepUnipotent.st_one hm hi
  have hsh : st h = h := GlobalTheory.TwoStepUnipotent.st_half hm hi hh hc
  have hhx : ∀ x, h * x + h * x = x := fun x => by rw [← add_mul, hh, one_mul]
  have hhN : ∀ i, ∀ x ∈ N i, h * x ∈ N i := fun i x hx => by
    have : h * x = p i (h * x) := by
      conv_lhs => rw [← hpf i x hx, ← hhx x, map_add (f := _), mul_add, hhx]
    rw [this]; exact hpN _ _
  have hle0 : ∀ i, N i ≤ N 0 := fun i => by
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact (hle i).trans ih
  have hnil : ∀ y ∈ N 0, y ^ 2 ^ m = 0 := fun y hy => by
    have : ∀ k, y ^ 2 ^ k ∈ N k := fun k => by
      induction k with
      | zero => simpa using hy
      | succ k ih => rw [pow_succ, pow_mul, sq]; exact hmul _ _ ih _ ih
    exact hz _ (this m)
  have umul : ∀ g g' : S, (st g * g = 1 ∧ g * st g = 1) → (st g' * g' = 1 ∧ g' * st g' = 1) →
      (st (g * g') * (g * g') = 1 ∧ g * g' * st (g * g') = 1) := fun g g' u u' => by
    rw [hm]
    exact ⟨by rw [mul_assoc, ← mul_assoc (st g), u.1, one_mul, u'.1],
      by rw [mul_assoc, ← mul_assoc g', u'.2, one_mul, u.2]⟩
  have ust : ∀ g : S, (st g * g = 1 ∧ g * st g = 1) → (st (st g) * st g = 1 ∧ st g * st (st g) = 1) :=
    fun g u => by rw [hi]; exact u.symm
  have nmul : ∀ i (g g' : S), g - 1 ∈ N i → g' - 1 ∈ N i → g * g' - 1 ∈ N i := fun i g g' u u' => by
    have : g * g' - 1 = (g - 1) * (g' - 1) + (g - 1) + (g' - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (hle i (hmul i _ u _ u')) u) u'
  have nlead : ∀ i (g g' x x' : S), g - 1 ∈ N i → g' - 1 ∈ N i → g - 1 - x ∈ N (i + 1) → g' - 1 - x' ∈ N (i + 1) →
      g * g' - 1 - (x + x') ∈ N (i + 1) := fun i g g' x x' u u' v v' => by
    have : g * g' - 1 - (x + x') = (g - 1) * (g' - 1) + (g - 1 - x) + (g' - 1 - x') := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (hmul i _ u _ u') v) v'
  have key : ∀ i ≤ m, ∀ D ∈ 𝓝 (1 : T), ∃ V ∈ 𝓝 (0 : T), ∀ K : Set S, IsCompact K → (∀ x ∈ K, π x ∈ V) →
      (∀ x, ∃ y ∈ S₀, x - y ∈ K) →
      ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', π g ∈ D) ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N 0) ∧
      ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ N i →
        ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ N 0) ∧ ∃ k ∈ K', g = γ * k := by
    intro i him
    induction him using Nat.decreasingInduction with
    | self =>
      intro D hD
      have one : (st 1 * 1 = 1 ∧ 1 * st 1 = 1) ∧ (1 : S) - 1 ∈ N 0 := by simp [h1]
      refine ⟨Set.univ, Filter.univ_mem, fun K _ _ _ => ⟨{1}, isCompact_singleton, fun g hg => ?_,
        fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact one,
        fun g hg => ⟨1, one_mem _, one, 1, rfl, ?_⟩⟩⟩
      · rw [Set.mem_singleton_iff.1 hg, map_one]; exact mem_of_mem_nhds hD
      rw [one_mul, ← sub_eq_zero]
      exact hz _ hg.2
    | of_succ i _ ih =>
      intro D hD
      obtain ⟨D₁, hD₁, hDD⟩ : ∃ D₁ ∈ 𝓝 (1 : T), ∀ a ∈ D₁, ∀ b ∈ D₁, a * b ∈ D := by
        have e : ∀ᶠ x : T × T in 𝓝 ((1 : T), (1 : T)), x.1 * x.2 ∈ D :=
          (continuous_mul.tendsto ((1 : T), (1 : T))).eventually (by simpa using hD)
        obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 e
        exact ⟨u ∩ v, Filter.inter_mem hu hv, fun a ha b hb => huv (Set.mk_mem_prod ha.1 hb.2)⟩
      obtain ⟨V₂, hV₂, ih'⟩ := ih D₁ hD₁
      obtain ⟨q, hq⟩ : ∃ q : S → S, ∀ z, q z = h * (h * (p i z - st (p i z))) := ⟨_, fun _ => rfl⟩
      have qc : Continuous q := by
        rw [show q = fun z => h * (h * (p i z - st (p i z))) from funext hq]
        have := hp i
        fun_prop
      have qN : ∀ z, q z ∈ N i := fun z => by
        rw [hq]; exact hhN _ _ (hhN _ _ (sub_mem (hpN i z) (hst _ _ (hpN i z))))
      have qs : ∀ z, st (q z) = - q z := fun z => by
        rw [hq, hm, hm, hsh, map_sub, hi, ← hc, ← hc, ← mul_neg, ← mul_neg, neg_sub]
      have q0 : ∀ z ∈ S₀, q z ∈ S₀ := fun z hz => by
        rw [hq]; exact mul_mem hh0 (mul_mem hh0 (sub_mem (hp0 i z hz) (h0 _ (hp0 i z hz))))
      have qsub : ∀ z z', q (z - z') = q z - q z' := fun z z' => by
        simp only [hq, map_sub]; noncomm_ring
      obtain ⟨c, hcd⟩ : ∃ c : S → S, ∀ z, c z = cay (2 ^ m) (q z) := ⟨_, fun _ => rfl⟩
      have cc : Continuous c := by
        rw [show c = fun z => cay (2 ^ m) (q z) from funext hcd]
        unfold cay
        fun_prop
      have cu : ∀ z, st (c z) * c z = 1 ∧ c z * st (c z) = 1 := fun z => by
        rw [hcd]; exact cay_unitary hm hi (hnil _ (hle0 i (qN z))) (qs z)
      have cl : ∀ z, c z - 1 - (q z + q z) ∈ N (i + 1) := fun z => by
        rw [hcd, cay_sub (hnil _ (hle0 i (qN z)))]
        refine hmul _ _ (add_mem (qN z) (qN z)) _ (sum_mem fun j hj => ?_)
        clear hj
        induction j with
        | zero => simpa using qN z
        | succ j ih => rw [pow_succ]; exact hle i (hmul _ _ ih _ (qN z))
      have cN : ∀ z, c z - 1 ∈ N i := fun z => by
        simpa using add_mem (hle i (cl z)) (add_mem (qN z) (qN z))
      have c0 : ∀ z ∈ S₀, c z ∈ S₀ := fun z hz => by
        rw [hcd]
        exact mul_mem (add_mem (one_mem _) (q0 z hz)) (sum_mem fun j _ => pow_mem (q0 z hz) j)
      have sN : ∀ z, st (c z) - 1 ∈ N i := fun z => by
        simpa [h1] using hst _ _ (cN z)
      have sl : ∀ z, st (c z) - 1 - -(q z + q z) ∈ N (i + 1) := fun z => by
        have := hst _ _ (cl z)
        rwa [map_sub, map_sub, map_add, h1, qs, ← neg_add] at this
      obtain ⟨cT, hcT⟩ : ∃ cT : T → T, ∀ t, cT t = cay (2 ^ m) (π h * (π h * (pT i t - stT (pT i t)))) :=
        ⟨_, fun _ => rfl⟩
      have cTc : Continuous cT := by
        rw [show cT = fun t => cay (2 ^ m) (π h * (π h * (pT i t - stT (pT i t)))) from funext hcT]
        have := hpT i
        unfold cay
        fun_prop
      have cT0 : cT 0 = 1 := by
        rw [hcT]
        simp only [map_zero, sub_zero, mul_zero]
        unfold cay
        rw [add_zero, one_mul, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (by positivity))
          (fun b _ hb => zero_pow hb), pow_zero]
      have cπ : ∀ z, π (c z) = cT (π z) := fun z => by
        rw [hcd, hq, hcT, map_cay]
        simp only [map_mul, map_sub, hπp, hπs]
      refine ⟨V₂ ∩ cT ⁻¹' D₁, Filter.inter_mem hV₂
        (cTc.continuousAt.preimage_mem_nhds (by rw [cT0]; exact hD₁)), fun K hK hKV hcov => ?_⟩
      obtain ⟨K', hK', hKD, hU, hcov'⟩ := ih' K hK (fun x hx => (hKV x hx).1) hcov
      refine ⟨(fun x : S × S => x.1 * c x.2) '' (K' ×ˢ K), (hK'.prod hK).image (by fun_prop), ?_, ?_, ?_⟩
      · rintro _ ⟨⟨k, z⟩, ⟨hk, hz'⟩, rfl⟩
        rw [map_mul, cπ]
        exact hDD _ (hKD k hk) _ (hKV z hz').2
      · rintro _ ⟨⟨k, z⟩, ⟨hk, -⟩, rfl⟩
        exact ⟨umul _ _ (hU k hk).1 (cu z), nmul _ _ _ (hU k hk).2 (hle0 i (cN z))⟩
      · rintro g ⟨u, hg⟩
        obtain ⟨y, hy, hyK⟩ := hcov (g - 1)
        have gl : g - 1 - (q (g - 1) + q (g - 1)) ∈ N (i + 1) := by
          have e : g - 1 - (q (g - 1) + q (g - 1)) = -(h * (st (g - 1) * (g - 1))) := by
            rw [hq, hhx, hpf i _ hg, map_sub, h1]
            have : (st g - 1) * (g - 1) = -((g - 1) + (st g - 1)) := by
              rw [sub_mul, mul_sub, u.1]; noncomm_ring
            rw [this]
            generalize g - 1 = n
            generalize st g - 1 = n'
            calc n - h * (n - n') = (h * n + h * n) - h * (n - n') := by rw [hhx]
              _ = _ := by noncomm_ring
          rw [e]
          exact neg_mem (hhN _ _ (hmul _ _ (hst _ _ hg) _ hg))
        have t := nlead i _ _ _ _ (nmul i _ _ (sN y) hg) (sN (g - 1 - y)) (nlead i _ _ _ _ (sN y) hg (sl y) gl) (sl (g - 1 - y))
        have e : -(q y + q y) + (q (g - 1) + q (g - 1)) + -(q (g - 1 - y) + q (g - 1 - y)) = 0 := by
          rw [qsub (g - 1) y]; abel
        rw [e, sub_zero] at t
        obtain ⟨γ, hγ, uγ, k, hk, hgk⟩ := hcov' _ ⟨umul _ _ (umul _ _ (ust _ (cu y)) u) (ust _ (cu (g - 1 - y))), t⟩
        refine ⟨c y * γ, mul_mem (c0 y hy) hγ, ⟨umul _ _ (cu y) uγ.1, nmul _ _ _ (hle0 i (cN y)) uγ.2⟩,
          _, ⟨(k, g - 1 - y), ⟨hk, hyK⟩, rfl⟩, ?_⟩
        calc g = (c y * st (c y)) * g * (st (c (g - 1 - y)) * c (g - 1 - y)) := by rw [(cu _).1, (cu _).2, one_mul, mul_one]
          _ = c y * (st (c y) * g * st (c (g - 1 - y))) * c (g - 1 - y) := by simp only [mul_assoc]
          _ = _ := by rw [hgk]; simp only [mul_assoc]
  obtain ⟨V, hV, H⟩ := key 0 (Nat.zero_le m) D hD
  exact ⟨V, hV, H⟩

variable {ι : Type} [Fintype ι] {ε : ι → S} {w : ι → ℤ}

theorem compact_mod_near_of_weights (S₀ : Subring S) (h : S)
    (hcont : Continuous st) (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (he : CompleteOrthogonalIdempotents ε)
    (he0 : ∀ a, ε a ∈ S₀) (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a)
    (π : S →+* T) (stT : T →+ T) (hstT : Continuous stT) (hπs : ∀ x, π (st x) = stT (π x))
    (D : Set T) (hD : D ∈ 𝓝 (1 : T)) :
    ∃ V ∈ 𝓝 (0 : T), ∀ K : Set S, IsCompact K → (∀ x ∈ K, π x ∈ V) → (∀ x, ∃ y ∈ S₀, x - y ∈ K) →
      ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', π g ∈ D) ∧
        (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0) ∧
        ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0 →
          ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ raise ε w 0) ∧ ∃ k ∈ K', g = γ * k := by
  classical
  obtain ⟨m, hmb⟩ : ∃ m : ℕ, ∀ a b, w a ≤ w b + m := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun ab : ι × ι => (w ab.1 - w ab.2).toNat).bddAbove
    refine ⟨M, fun a b => ?_⟩
    have : (w a - w b).toNat ≤ M := hM ⟨(a, b), rfl⟩
    omega
  have hall : ∀ x, ∑ ab : ι × ι, ε ab.1 * x * ε ab.2 = x := fun x => by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, mul_one, one_mul]
  let p : ℕ → S →+ S := fun i =>
    { toFun := fun x => ∑ ab ∈ Finset.univ.filter (fun ab : ι × ι => ¬ w ab.1 ≤ w ab.2 + i), ε ab.1 * x * ε ab.2
      map_zero' := by simp
      map_add' := fun x y => by simp only [mul_add, add_mul, Finset.sum_add_distrib] }
  let pT : ℕ → T →+ T := fun i =>
    { toFun := fun x => ∑ ab ∈ Finset.univ.filter (fun ab : ι × ι => ¬ w ab.1 ≤ w ab.2 + i), π (ε ab.1) * x * π (ε ab.2)
      map_zero' := by simp
      map_add' := fun x y => by simp only [mul_add, add_mul, Finset.sum_add_distrib] }
  refine compact_mod_near_of_filtration S₀ h (raise ε w) p m hcont hm hi h0 hh0 hh hc (fun i => ?_) (fun i x => ?_)
    (fun i x hx => ?_) (fun i x hx => ?_) raise_le (fun i x hx y hy => raise_mul he i hx hy)
    (fun i x hx => raise_st hm hi hs i hx) (fun x hx => ?_) π stT pT hstT (fun i => ?_) hπs (fun i x => ?_) D hD
  · exact continuous_finsetSum _ fun ab _ => by fun_prop
  · refine sum_mem fun ab hab a b h' => ?_
    have hab' := (Finset.mem_filter.1 hab).2
    by_cases ea : a = ab.1
    · have eb : ab.2 ≠ b := fun eb => hab' (by rw [eb, ← ea]; exact h')
      rw [mul_assoc, mul_assoc _ (ε ab.2), he.ortho eb, mul_zero, mul_zero]
    · rw [← mul_assoc, ← mul_assoc, he.ortho ea, zero_mul, zero_mul, zero_mul]
  · refine Eq.trans ?_ (hall x)
    exact Finset.sum_filter_of_ne fun ab _ hne h' => hne (hx _ _ h')
  · exact sum_mem fun ab _ => mul_mem (mul_mem (he0 _) hx) (he0 _)
  · rw [← hall x]
    exact Finset.sum_eq_zero fun ab _ => hx _ _ (hmb _ _)
  · exact continuous_finsetSum _ fun ab _ => by fun_prop
  · show π (∑ ab ∈ _, _) = ∑ ab ∈ _, _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]

end Abstract

section Adelic

open scoped TensorProduct
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT cT_mul)

theorem exists_entry_nhds {B : Type} [TopologicalSpace B] [Zero B] {n : ℕ} (V : Set (Matrix (Fin n) (Fin n) B))
    (hV : V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) B)) : ∃ W ∈ 𝓝 (0 : B), ∀ X : Matrix (Fin n) (Fin n) B, (∀ i j, X i j ∈ W) → X ∈ V := by
  have h1 : V ∈ 𝓝 (fun (_ : Fin n) (_ : Fin n) => (0 : B)) := hV
  rw [nhds_pi] at h1
  obtain ⟨I, -, t, ht, hs⟩ := Filter.mem_pi.1 h1
  have h2 : ∀ i, ∃ t' : Fin n → Set B, (∀ j, t' j ∈ 𝓝 (0 : B)) ∧ ∀ x : Fin n → B, (∀ j, x j ∈ t' j) → x ∈ t i := fun i => by
    have h3 := ht i
    rw [nhds_pi] at h3
    obtain ⟨I', -, t', ht', hs'⟩ := Filter.mem_pi.1 h3
    exact ⟨t', ht', fun x hx => hs' fun j _ => hx j⟩
  choose t' ht' hs' using h2
  refine ⟨⋂ i, ⋂ j, t' i j, Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => ht' i j, fun X hX => ?_⟩
  exact hs fun i _ => hs' i _ fun j => Set.mem_iInter.1 (Set.mem_iInter.1 (hX i j) i) j

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev finT : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)

theorem continuous_finT : Continuous (finT (F := F) (E := E)) :=
  GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (sndA F).toLinearMap (map_mul (sndA F)) continuous_snd

theorem fine_cover (W : Set (Af F ⊗[F] E)) (hW : W ∈ 𝓝 (0 : Af F ⊗[F] E)) :
    ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ (∀ x ∈ K, finT x ∈ W) ∧
      ∀ z, ∃ x : E, z - inclR (F := F) (AF F) x ∈ K := by
  obtain ⟨K₀, hK₀, hs⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have hKf : IsCompact (finT '' K₀) := hK₀.image continuous_finT
  obtain ⟨μ, hμd⟩ : ∃ μ : Af F × (Af F ⊗[F] E) → Af F ⊗[F] E, ∀ x, μ x = x.1 • x.2 := ⟨_, fun _ => rfl⟩
  have hμ : Continuous μ := by rw [funext hμd]; exact continuous_smul
  obtain ⟨u, v, hu, hv, h0u, hKv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : Af F))) hKf
    (n := μ ⁻¹' interior W)
    (isOpen_interior.preimage hμ) (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = 0 := ha
      rw [Set.mem_preimage, hμd, ha', zero_smul]
      exact mem_interior_iff_mem_nhds.2 hW)
  obtain ⟨N, hN, hNu⟩ := Formalism.L2.SG.Pf.top_nhds_basis F u (hu.mem_nhds (h0u rfl))
  have hNu' : (N : Af F) ∈ u := by simpa using hNu 1 (one_mem _)
  have hNF : (N : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hN)
  refine ⟨(fun k => (N : F) • k) '' K₀, hK₀.image (by
      have : (fun k : AF F ⊗[F] E => (N : F) • k) = fun k => (algebraMap F (AF F) (N : F)) • k :=
        funext fun k => (algebraMap_smul (AF F) (N : F) k).symm
      rw [this]; fun_prop), ?_, fun z => ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    have h1 : finT ((N : F) • k) = μ ((N : Af F), finT k) := by
      rw [hμd, map_smul, ← algebraMap_smul (Af F) (N : F), map_natCast]
    rw [h1]
    have h3 : ((N : Af F), finT k) ∈ u ×ˢ v := Set.mk_mem_prod hNu' (hKv (Set.mem_image_of_mem _ hk))
    exact interior_subset (huv h3)
  · obtain ⟨x, hx⟩ := hs ((N : F)⁻¹ • z)
    refine ⟨(N : F) • x, _, hx, ?_⟩
    show (N : F) • _ = _
    have h2 : inclR (F := F) (AF F) ((N : F) • x) = (N : F) • inclR (F := F) (AF F) x := by
      exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (N : F) x
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hNF, one_smul, h2]

end Adelic

end GlobalTheory.CompanionTheory.StrongUnip

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalCompactFundamentalDomain
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.StrongUnip

open GlobalTheory.UnipFlagCore (fam wt raise fam_st)
open GlobalTheory.UAut

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def adjF : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) →+ Matrix (Fin n) (Fin n) (Af F ⊗[F] E) where
  toFun X := J⁻¹.map (inclR (F := F) (Af F)) * cT (sigR (Af F) σ) X * J.map (inclR (F := F) (Af F))
  map_zero' := by simp [cT]
  map_add' X Y := by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

def finM : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+* Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  RingHom.mapMatrix (finT (F := F) (E := E)).toRingHom

omit [NumberField E] in
theorem finM_apply (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (i j : Fin n) : finM X i j = finT (X i j) := rfl

omit [NumberField E] in
theorem finT_inclR (x : E) : finT (inclR (F := F) (AF F) x) = inclR (F := F) (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  simp

omit [NumberField E] in
theorem finT_sigR (x : AF F ⊗[F] E) : finT (sigR (AF F) σ x) = sigR (Af F) σ (finT x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem finM_adjA (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : finM (adjA σ J X) = adjF σ J (finM X) := by
  have a : ∀ M : Matrix (Fin n) (Fin n) E, finM (M.map (inclR (F := F) (AF F))) = M.map (inclR (F := F) (Af F)) :=
    fun M => by
      ext i j
      rw [finM_apply, Matrix.map_apply, Matrix.map_apply, finT_inclR]
  have b : finM (cT (sigR (AF F) σ) X) = cT (sigR (Af F) σ) (finM X) := by
    ext i j
    simp only [finM_apply, cT, Matrix.transpose_apply, Matrix.map_apply, finT_sigR]
  rw [adjA_apply, map_mul, map_mul, a, a, b]
  rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = finM (matHom _ σ J g).1 := by
  ext r s
  exact GlobalTheory.AutFunCompare.mat_mapH σ J (sndA F) g r s

end SlopeTestRemainingChoices

theorem strong_approx_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ W ∈ 𝓝 (1 : GFin σ J), ∃ Q : Set (GAd σ J), IsCompact Q ∧ ∀ m ∈ unipRad σ J Cc, ∃ γ ∈ ratPts σ J, ∃ q ∈ Q, q ∈ unipRad σ J Cc ∧ projFin σ J q ∈ W ∧ m = γ * q := by
  intro F E _ _ _ _ _ σ hcm n J hJ k Cc hC W hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.UnipFlagCore.conj_invol hcm
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨d, hdd⟩ : ∃ d : Fin k → ℕ, d = fun _ => 0 := ⟨_, rfl⟩
  have hd : ∀ j, d j < 1 := fun j => by rw [hdd]; exact Nat.one_pos
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idemA_complete hJ Cc L hL hC.2 hLL
  have hs := fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) Cc L) d 1
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hcontF : Continuous (adjF σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin n)).range, adjA σ J x ∈ (φ.mapMatrix (m := Fin n)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adjA_map X).symm⟩
  have hmem := mem_unipFlag_iff_raise hJ hσ Cc L hL hC.2 hLL hd
  have hadj1 : adjF σ J 1 = 1 := by
    have h1 := finM_adjA σ J (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    rw [GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ), map_one] at h1
    exact h1.symm
  let fF : GFin σ J → _ := fun g => Units.embedProduct _ (matHom _ σ J g)
  have hfF : Topology.IsInducing fF := Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  obtain ⟨O, hO, hOW⟩ := Filter.mem_comap.1 (hfF.nhds_eq_comap 1 ▸ hW)
  let G : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → _ := fun x => (x, MulOpposite.op (adjF σ J x))
  have hG : Continuous G := continuous_id.prodMk (MulOpposite.continuous_op.comp hcontF)
  have hD : G ⁻¹' O ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    hG.continuousAt.preimage_mem_nhds (by
      have : G 1 = fF 1 := Prod.ext rfl (by
        show MulOpposite.op (adjF σ J 1) = MulOpposite.op 1
        rw [hadj1])
      rw [this]; exact hO)
  have hproj : ∀ g : GAd σ J, finM (matHom _ σ J g).1 ∈ G ⁻¹' O → projFin σ J g ∈ W := fun g hg => hOW (by
    have e : fF (projFin σ J g) = G (finM (matHom _ σ J g).1) := by
      refine Prod.ext (mat_projFin σ J g) ?_
      show MulOpposite.op (matHom _ σ J (projFin σ J g)⁻¹).1 = MulOpposite.op (adjF σ J _)
      rw [← map_inv, mat_projFin, ← finM_adjA]
      congr 2
      exact (adjA_mat hJ g).symm
    show fF (projFin σ J g) ∈ O
    rw [e]; exact hg)
  obtain ⟨V, hV, H⟩ := compact_mod_near_of_weights (st := adjA σ J) (w := wt d 1)
    (ε := fam (adjA σ J) (idemA Cc L)) (φ.mapMatrix (m := Fin n)).range
    (Matrix.scalar _ (φ (1 / 2))) hcont (adjA_mul hJ) (adjA_adjA hJ hσ) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add (f := _), ← map_add (f := _), add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq) he
    (by
      have hu : ∀ j, idemA (F := F) Cc L j ∈ (φ.mapMatrix (m := Fin n)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin k ⊕ Fin k, Sum.elim (idemA (F := F) Cc L) (fun j => adjA σ J (idemA Cc L j)) j ∈
          (φ.mapMatrix (m := Fin n)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
    finM (adjF σ J) hcontF (finM_adjA σ J) _ hD
  obtain ⟨W₀, hW₀, hW₀V⟩ := exists_entry_nhds V hV
  obtain ⟨K, hK, hKW, hKs⟩ := fine_cover (E := E) W₀ hW₀
  obtain ⟨K', hK', hKD, k1, k2⟩ := H (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun x hx => hW₀V _ fun i j => hKW _ (hx i trivial j trivial))
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩)
  let lift : ∀ x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (adjA σ J x * x = 1 ∧ x * adjA σ J x = 1) ∧
      x - 1 ∈ raise (fam (adjA σ J) (idemA Cc L)) (wt d 1) 0 → unipFlag σ J Cc d := fun x hx =>
    ⟨⟨⟨x, adjA σ J x, hx.1.2, hx.1.1⟩, (adjA_mul_self_iff hJ _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : unipFlag σ J Cc d → _ := fun m => Units.embedProduct _ (matHom _ σ J m.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have hconst : unipFlag σ J Cc d = unipRad σ J Cc := by rw [hdd]; exact unipFlag_const Cc 0
  refine ⟨Subtype.val '' (f ⁻¹' ((fun x => (x, MulOpposite.op (adjA σ J x))) '' K')),
    (hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_).image
      continuous_subtype_val, fun m hm => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · rw [← hconst] at hm
    have hu := (adjA_mul_self_iff hJ _).2 m.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (matHom _ σ J m).1 ⟨⟨hu, mul_eq_one_comm.1 hu⟩, (hmem _).1 hm⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    have e : (⟨m, hm⟩ : unipFlag σ J Cc d) = lift γ p1 * lift k (k1 k hk) := Subtype.ext (Subtype.ext (Units.ext p2))
    refine ⟨(lift γ p1).1, ?_, (lift k (k1 k hk)).1, ⟨lift k (k1 k hk), ⟨k, hk, rfl⟩, rfl⟩,
      hconst ▸ (lift k (k1 k hk)).2, hproj _ (hKD k hk), congrArg Subtype.val e⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin n)) := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
    have hγ' : cT (sigR (AF F) σ) γ * J.map φ * γ = J.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * J.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen σ a).symm).trans hγ'

end GlobalTheory.CompanionTheory.StrongUnip

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalCompactFundamentalDomainStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_compact_fundamental_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ W ∈ 𝓝 (1 : GFin σ J), ∃ Q : Set (GAd σ J), IsCompact Q ∧ ∀ m ∈ unipRad σ J Cc, ∃ γ ∈ ratPts σ J, ∃ q ∈ Q, q ∈ unipRad σ J Cc ∧ projFin σ J q ∈ W ∧ m = γ * q := by
  first | exact @GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad | exact GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad | (intros; apply GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicMemPartialFlag
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicMemPartialFlag
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem mul_firstCols_eq {R : Type} [CommRing R] {n r : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (Z : Matrix (Fin n) (Fin r) R) (B : Matrix (Fin r) (Fin r) R) (hB : B.BlockTriangular id)
    (e : M * Z = Z * B) (s : Fin r) :
    M * Z.submatrix id (Fin.castLE s.2) =
      Z.submatrix id (Fin.castLE s.2) * B.submatrix (Fin.castLE s.2) (Fin.castLE s.2) := by
  ext i j
  have h := congrFun (congrFun e i) (Fin.castLE s.2 j)
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq] at h ⊢
  rw [h]
  refine (Fintype.sum_of_injective (Fin.castLE s.2) (Fin.castLE_injective s.2) _ _ ?_ ?_).symm
  · intro l hl
    have hlt : Fin.castLE s.2 j < l := by
      by_contra hc
      apply hl
      have hj := j.isLt
      have hc' : l.val ≤ j.val := not_lt.mp hc
      exact ⟨⟨l.val, by omega⟩, Fin.ext rfl⟩
    have h0 : B l (Fin.castLE s.2 j) = 0 := hB hlt
    rw [h0, mul_zero]
  · intro l
    rfl

theorem mem_parFlag_first_of_minParOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E), ∀ p ∈ minParOne σ J X, ∀ s : Fin r, p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := by
  intro F E _ _ _ _ _ σ n J r X p hp s
  obtain ⟨B, hB, e, hu⟩ := hp
  choose u hu1 _ using hu
  have e1 := mul_firstCols_eq _ _ B hB e s
  have hBs : (B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)).BlockTriangular id := by
    intro i j hij
    exact hB hij
  have hdet : IsUnit (B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)).det := by
    rw [Matrix.det_of_isUpperTriangular hBs]
    refine ⟨∏ i, u (Fin.castLE s.2 i), ?_⟩
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.submatrix_apply, hu1]
  have hZ : GlobalTheory.SiegelSet.adMat F (pre X s) =
      (GlobalTheory.SiegelSet.adMat F X).submatrix id (Fin.castLE s.2) := rfl
  refine ⟨⟨B.submatrix (Fin.castLE s.2) (Fin.castLE s.2), ?_, ?_⟩,
    ⟨(B.submatrix (Fin.castLE s.2) (Fin.castLE s.2))⁻¹, ?_, ?_⟩⟩
  · intro i j h
    exact absurd h (lt_irrefl 0)
  · rw [hZ]
    exact e1
  · intro i j h
    exact absurd h (lt_irrefl 0)
  · rw [hZ, map_inv]
    set g := GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J p
    set Z := (GlobalTheory.SiegelSet.adMat F X).submatrix id (Fin.castLE s.2)
    set Bs := B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)
    have h1 : Bs * Bs⁻¹ = 1 := Matrix.mul_nonsing_inv Bs hdet
    have h2 : (g⁻¹).val * g.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹).val * Z
        = (g⁻¹).val * Z * (Bs * Bs⁻¹) := by rw [h1, Matrix.mul_one]
      _ = (g⁻¹).val * (g.val * Z) * Bs⁻¹ := by
          rw [e1]
          simp only [Matrix.mul_assoc]
      _ = Z * Bs⁻¹ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicMemPartialFlagStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_mem_partial_flag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E), ∀ p ∈ minParOne σ J X, ∀ s : Fin r, p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.mem_parFlag_first_of_minParOne | exact GlobalTheory.CompanionTheory.RapidDecay.mem_parFlag_first_of_minParOne | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.mem_parFlag_first_of_minParOne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay.NearCusp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem conj_mem_nhds {C : Set (GFin σ J)} (hC : IsCompact C) {V : Set (GFin σ J)} (hV : V ∈ 𝓝 (1 : GFin σ J)) :
    {x : GFin σ J | ∀ h ∈ C, h⁻¹ * x * h ∈ V} ∈ 𝓝 (1 : GFin σ J) := by
  refine hC.eventually_forall_of_forall_eventually (P := fun x h => h⁻¹ * x * h ∈ V) fun y _ => ?_
  have hc : Continuous fun z : GFin σ J × GFin σ J => z.2⁻¹ * z.1 * z.2 :=
    (continuous_snd.inv.mul continuous_fst).mul continuous_snd
  have ht := hc.tendsto ((1 : GFin σ J), y)
  simp only [mul_one, inv_mul_cancel] at ht
  exact ht hV

theorem exists_bound_archMat {Cm : Set (GAd σ J)} (hCm : IsCompact Cm) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ k ∈ Cm, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ∑ a, ∑ b, ‖archMat σ J τ (projArch σ J w k⁻¹) i a‖ * ‖archMat σ J τ (projArch σ J w k) b j‖ ≤ C₀ := by
  let T : GAd σ J → ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℝ := fun k w τ i j =>
    ∑ a, ∑ b, ‖archMat σ J τ (projArch σ J w k⁻¹) i a‖ * ‖archMat σ J τ (projArch σ J w k) b j‖
  let f : GAd σ J → ℝ := fun k => ∑ w, ∑ τ : EmbOver E w, ∑ i, ∑ j, T k w τ i j
  have hm : ∀ (w : InfinitePlace F) (τ : EmbOver E w), Continuous fun k : GAd σ J => archMat σ J τ (projArch σ J w k) :=
    fun w τ => (GlobalTheory.Orb.continuous_archMat σ J τ).comp (continuous_projArch σ J w)
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    exact (((hm w τ).comp continuous_inv).matrix_elem i a).norm.mul (((hm w τ).matrix_elem b j).norm)
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn hf.continuousOn
  have hT : ∀ k w τ i j, 0 ≤ T k w τ i j := fun k w τ i j => by positivity
  refine ⟨max C 0, le_max_right _ _, fun k hk w τ i j => ?_⟩
  have h1 : T k w τ i j ≤ f k := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ i, ∑ j, T k w τ i j)
      (fun w _ => by positivity) (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, T k w τ i j) (fun τ _ => by positivity)
      (Finset.mem_univ τ))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, T k w τ i j) (fun i _ => by positivity)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => T k w τ i j) (fun j _ => hT k w τ i j) (Finset.mem_univ j)
  exact h1.trans ((Real.le_norm_self _).trans ((hC k hk).trans (le_max_left _ _)))

end GlobalTheory.CompanionTheory.RapidDecay.NearCusp

noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay.NearCusp

theorem near_cusp_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (Ω Cm : Set (GAd σ J)) (c : ℝ)
    (U : Subgroup (GAd σ J)) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X) (hCm : IsCompact Cm) (hc : 0 < c)
    (hU : IsOpen (U : Set (GAd σ J))) (s : Fin r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm,
      ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧
        κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  have hσ := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2

  let Cf : Set (GFin σ J) := (fun z : GAd σ J × GAd σ J => projFin σ J z.1 * projFin σ J z.2) '' (Ω ×ˢ Cm)
  have hCf : IsCompact Cf := (hΩ.prod hCm).image
    (((continuous_projFin σ J).comp continuous_fst).mul ((continuous_projFin σ J).comp continuous_snd))
  let Uf : Set (GFin σ J) := ofFin σ J ⁻¹' (U : Set (GAd σ J))
  have hUf : Uf ∈ 𝓝 (1 : GFin σ J) :=
    (hU.preimage (continuous_ofFin σ J)).mem_nhds (by simp only [Uf, Set.mem_preimage, map_one]; exact U.one_mem)
  let Wn : Set (GFin σ J) := {x | ∀ h ∈ Cf, h⁻¹ * x * h ∈ Uf}
  have hWn : Wn ∈ 𝓝 (1 : GFin σ J) := conj_mem_nhds hCf hUf
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.T.unipotent_radical_compact_fundamental_domain F E σ hCM n J hJ _ (pre X s) hC Wn hWn
  let Q' : Set (GAd σ J) := (fun z : GAd σ J × GAd σ J => z.1⁻¹ * z.2 * z.1) '' (Ω ×ˢ Q)
  have hQ' : IsCompact Q' := (hΩ.prod hQ).image ((continuous_fst.inv.mul continuous_snd).mul continuous_fst)
  obtain ⟨M₁, hM₁, hM₁b⟩ := GlobalTheory.T.torus_conjugate_unipotent_bounded F E σ hCM n J hJ r X Y hW Q' c hQ' hc s
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_archMat (σ := σ) (J := J) hCm
  refine ⟨C₀ * M₁, mul_nonneg hC₀ hM₁, ?_⟩
  intro p hp t ht a ha k hk m hm
  obtain ⟨γ, hγ, q, hqQ, hqU, hqW, rfl⟩ := hQm m hm
  have hfa : projFin σ J a = 1 := mem_infPts.1 ha.1
  refine ⟨γ, hγ, ofInf σ J (projInf σ J ((p * a * k)⁻¹ * q * (p * a * k))),
    ofFin σ J (projFin σ J ((p * a * k)⁻¹ * q * (p * a * k))), ⟨mem_infPts.2 (projFin_ofInf σ J _), ?_⟩, ?_,
    mem_finPts.2 (projInf_ofFin σ J _), ?_⟩
  · intro w τ i j

    have hpar : p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := GlobalTheory.T.minimal_parabolic_mem_partial_flag F E σ n J r X p (hΩP hp) s
    have hq' : q ∈ GlobalTheory.UAut.unipFlag σ J (pre X s) fun _ => 0 := by rw [GlobalTheory.UAut.unipFlag_const]; exact hqU
    have hnU : p⁻¹ * q * p ∈ unipRad σ J (pre X s) := by
      have := GlobalTheory.UAut.conj_mem_unipFlag hJ hσ hC (fun _ => 0) (inv_mem hpar) hq'
      rwa [inv_inv, GlobalTheory.UAut.unipFlag_const] at this
    have hnQ : p⁻¹ * q * p ∈ Q' := ⟨(p, q), ⟨hp, hqQ⟩, rfl⟩
    have hN := hM₁b _ hnQ hnU t ht a ha w τ
    have ev : (p * a * k)⁻¹ * q * (p * a * k) = k⁻¹ * (a⁻¹ * (p⁻¹ * q * p) * a) * k := by group
    have hB : archMat σ J τ (projArch σ J w k⁻¹) * archMat σ J τ (projArch σ J w k) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have key : archMat σ J τ (projArch σ J w (ofInf σ J (projInf σ J ((p * a * k)⁻¹ * q * (p * a * k))))) - 1 =
        archMat σ J τ (projArch σ J w k⁻¹) * (archMat σ J τ (projArch σ J w (a⁻¹ * (p⁻¹ * q * p) * a)) - 1) *
          archMat σ J τ (projArch σ J w k) := by
      rw [projArch_ofInf, projInfArch_projInf, ev, map_mul (projArch σ J w) _ k, map_mul (projArch σ J w) k⁻¹,
        map_mul (archMat σ J τ), map_mul (archMat σ J τ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB]
    rw [key]
    refine (GlobalTheory.CuspGeo.norm_mul_mul_apply_le _ _ _ _ hN i j).trans ?_
    rw [mul_div_assoc C₀]
    exact mul_le_mul_of_nonneg_right (hC₀b k hk w τ i j) (div_nonneg hM₁ (ratio_pos ht s).le)
  ·
    have hh : projFin σ J p * projFin σ J k ∈ Cf := ⟨(p, k), ⟨hp, hk⟩, rfl⟩
    have e : projFin σ J ((p * a * k)⁻¹ * q * (p * a * k)) =
        (projFin σ J p * projFin σ J k)⁻¹ * projFin σ J q * (projFin σ J p * projFin σ J k) := by
      simp only [map_mul, map_inv, hfa, mul_one]
    have := hqW _ hh
    rw [← e] at this
    exact this
  · rw [mul_assoc (γ * (p * a * k)), ofInf_projInf_mul_ofFin_projFin]
    group

end GlobalTheory.CompanionTheory.RapidDecay.NearCusp

namespace GlobalTheory.CompanionTheory.RapidDecay


open NearCusp in
theorem near_cusp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω Cm : Set (GAd σ J)) (c : ℝ) (U : Subgroup (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ s : Fin r, ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  choose M hM0 hM using near_cusp_one F E σ hCM n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  refine ⟨∑ s, M s, Finset.sum_nonneg fun s _ => hM0 s, ?_⟩
  intro p hp t ht a ha k hk s m hm
  obtain ⟨γ, hγ, u, κ, ⟨hu1, hu2⟩, h2, h3, h4⟩ := hM s p hp t ht a ha k hk m hm
  refine ⟨γ, hγ, u, κ, ⟨hu1, fun w τ i j => (hu2 w τ i j).trans ?_⟩, h2, h3, h4⟩
  exact div_le_div_of_nonneg_right (Finset.single_le_sum (fun s _ => hM0 s) (Finset.mem_univ s)) (ratio_pos ht s).le

end GlobalTheory.CompanionTheory.RapidDecay
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBoundStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_domain_open_subgroup_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω Cm : Set (GAd σ J)) (c : ℝ) (U : Subgroup (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ s : Fin r, ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.near_cusp | exact GlobalTheory.CompanionTheory.RapidDecay.near_cusp | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.near_cusp <;> assumption)
end
