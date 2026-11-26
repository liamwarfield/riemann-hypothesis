module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowSurjOfGenus
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOrthogonalUnitVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PairUnitLoc
open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

def PairUnitLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (p : Ideal (𝓞 K)), p.IsMaximal →
    ∀ (V : Type) [AddCommGroup V] [Module K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ w y : V, h y w = 1 → h w w ∈ locRing p → h y y ∈ locRing p →
      ∃ c ∈ locRing p, ∃ d ∈ locRing p, IsUnitIn (locRing p) (h (c • w + d • y) (c • w + d • y))

end PI.UnitaryGroupMassFormula.CntFormula.UG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodularOneGenus
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsTraceNotMem
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private lemma not_mem_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : s ∉ p ∧ conjO K s ∉ p := by
  rw [hcompl_eq_closure] at hs
  let M : Submonoid (𝓞 K) :=
    { carrier := {s | s ∉ p ∧ conjO K s ∉ p}
      mul_mem' := by
        intro x y hx hy
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨hy1, hy2⟩ := hy
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases hp.mem_or_mem h with h | h
          exacts [hx1 h, hy1 h]
        · rw [map_mul] at h
          rcases hp.mem_or_mem h with h | h
          exacts [hx2 h, hy2 h]
      one_mem' := by
        refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), fun h => ?_⟩
        rw [map_one] at h
        exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr h) }
  have hle : Submonoid.closure {s : 𝓞 K | s ∉ p ∧ conjO K s ∉ p} ≤ M :=
    Submonoid.closure_le.mpr (fun x hx => hx)
  exact hle hs

theorem num_mem_both {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) (hst : star a = a)
    (hna : ¬ IsUnitIn (locRing p) a) :
    ∃ a₁ : 𝓞 K, ∃ s₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K a₁ / algebraMap (𝓞 K) K s₁ ∧ a₁ ∈ p ∧ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  have hinj := IsFractionRing.injective (𝓞 K) K
  have hloc : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := ha
  obtain ⟨s, hs, hsa⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) p a).mp hloc
  obtain ⟨a₀, ha₀⟩ := Submodule.mem_one.mp hsa
  obtain ⟨hs1, hs2⟩ := not_mem_of_mem_hcompl hp hs
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h
    apply hs1
    have : s = 0 := hinj (by rw [h, map_zero])
    rw [this]
    exact p.zero_mem
  have hcs0 : star (algebraMap (𝓞 K) K s) ≠ 0 := by
    rw [← algebraMap_conjO]
    intro h
    apply hs2
    have : conjO K s = 0 := hinj (by rw [h, map_zero])
    rw [this]
    exact p.zero_mem
  obtain ⟨a₁, ha₁d⟩ : ∃ x : 𝓞 K, x = a₀ * conjO K s := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁d⟩ : ∃ x : 𝓞 K, x = s * conjO K s := ⟨_, rfl⟩
  have hs₁ : s₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [hs₁d]
    exact mul_mem hs (conjO_mem_hcompl hs)
  have hA : algebraMap (𝓞 K) K a₁ = algebraMap (𝓞 K) K s₁ * a := by
    rw [ha₁d, hs₁d, map_mul, map_mul, algebraMap_conjO, ha₀]
    ring
  have hAs : star (algebraMap (𝓞 K) K s₁) = algebraMap (𝓞 K) K s₁ := by
    rw [hs₁d, map_mul, algebraMap_conjO, star_mul, star_star]
  have hc : conjO K a₁ = a₁ := hinj (by rw [algebraMap_conjO, hA, star_mul, hst, hAs, mul_comm])
  have hs₁0 : algebraMap (𝓞 K) K s₁ ≠ 0 := by
    rw [hs₁d, map_mul, algebraMap_conjO]
    exact mul_ne_zero hs0 hcs0
  have hp1 : a₁ ∈ p := by
    by_contra hn
    have hmem : a₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
      rw [hcompl_eq_closure]
      exact Submonoid.subset_closure ⟨hn, by rw [hc]; exact hn⟩
    have ha0 : a ≠ 0 := by
      intro h0
      apply hn
      have : a₁ = 0 := hinj (by rw [hA, h0, mul_zero, map_zero])
      rw [this]
      exact p.zero_mem
    apply hna
    refine ⟨ha0, ha, ?_⟩
    change a⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    refine ⟨a₁, hmem, Submodule.mem_one.mpr ⟨s₁, ?_⟩⟩
    rw [hA, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  refine ⟨a₁, s₁, hs₁, ?_, hp1, ?_⟩
  · rw [hA, eq_div_iff hs₁0, mul_comm]
  · rw [mem_conjIdeal_iff, hc]
    exact hp1

theorem exists_trace_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ l : 𝓞 K, l + conjO K l ∉ p := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hp
  by_cases h2 : (2 : 𝓞 K) ∈ p
  · refine ⟨θ, fun h => hθ ?_⟩
    have e : θ - conjO K θ = (θ + conjO K θ) - 2 * conjO K θ := by ring
    rw [e]
    exact p.sub_mem h (p.mul_mem_right _ h2)
  · refine ⟨1, ?_⟩
    rw [map_one, one_add_one_eq_two]
    exact h2

theorem pair_unit_local : PairUnitLoc := by
  intro K _ _ _ hK p hp V _ _ h hh w y hyw ha hb
  have hpp : p.IsPrime := hp.isPrime
  have hinj := IsFractionRing.injective (𝓞 K) K
  by_cases hua : IsUnitIn (locRing p) (h w w)
  · exact ⟨1, (locRing p).one_mem, 0, (locRing p).zero_mem, by simpa using hua⟩
  by_cases hub : IsUnitIn (locRing p) (h y y)
  · exact ⟨0, (locRing p).zero_mem, 1, (locRing p).one_mem, by simpa using hub⟩
  obtain ⟨l, hl⟩ := exists_trace_notMem hK hp
  have hwy : h w y = 1 := by rw [← hh.eq y w, hyw, map_one]
  have hsa : star (h w w) = h w w := by
    have := hh.eq w w
    rwa [starRingEnd_apply] at this
  have hsb : star (h y y) = h y y := by
    have := hh.eq y y
    rwa [starRingEnd_apply] at this
  obtain ⟨a₁, s₁, hs₁, hae, ha₁, -⟩ := num_mem_both hpp ha hsa hua
  obtain ⟨b₁, s₂, hs₂, hbe, hb₁, -⟩ := num_mem_both hpp hb hsb hub
  have hAmem : ∀ r : 𝓞 K, algebraMap (𝓞 K) K r ∈ locRing p := by
    intro r
    change algebraMap (𝓞 K) K r ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
  refine ⟨1, (locRing p).one_mem, algebraMap (𝓞 K) K l, hAmem l, ?_⟩
  have hv : h ((1 : K) • w + algebraMap (𝓞 K) K l • y) ((1 : K) • w + algebraMap (𝓞 K) K l • y) =
      h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y := by
    simp only [one_smul, map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, RingHom.id_apply, map_smul, hyw, hwy, map_mul,
      algebraMap_conjO, star_one]
    ring
  rw [hv]
  by_contra hnu
  have hvmem : h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y ∈ locRing p :=
    add_mem (add_mem ha (hAmem _)) (mul_mem (hAmem _) hb)
  have hvs : star (h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y) =
      h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y := by
    rw [star_add, star_add, star_mul, hsa, hsb, ← algebraMap_conjO, ← algebraMap_conjO,
      map_add, map_mul, Formalism.HermitianLattices.Ext.L3.conjO_conjO]
    ring
  obtain ⟨n, t, ht, hve, hn, -⟩ := num_mem_both hpp hvmem hvs hnu
  have hnz : ∀ {u : 𝓞 K}, u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p → algebraMap (𝓞 K) K u ≠ 0 := by
    intro u hu h0
    apply (not_mem_of_mem_hcompl hpp hu).1
    have : u = 0 := hinj (by rw [h0, map_zero])
    rw [this]
    exact p.zero_mem
  have ht0 := hnz ht
  have h10 := hnz hs₁
  have h20 := hnz hs₂
  have key : n * (s₁ * s₂) = (a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁) * t := by
    apply hinj
    have e1 : algebraMap (𝓞 K) K n = (h w w + algebraMap (𝓞 K) K (l + conjO K l) + algebraMap (𝓞 K) K (conjO K l * l) * h y y) * algebraMap (𝓞 K) K t := by
      rw [hve, div_mul_cancel₀ _ ht0]
    simp only [map_mul, map_add (f := _)]
    rw [e1, hae, hbe]
    simp only [map_mul, map_add (f := _)]
    field_simp
  have hN : a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁ ∈ p := by
    have hmem : (a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁) * t ∈ p := by
      rw [← key]
      exact p.mul_mem_right _ hn
    rcases hpp.mem_or_mem hmem with h1 | h1
    · exact h1
    · exact absurd h1 (not_mem_of_mem_hcompl hpp ht).1
  have hT : (l + conjO K l) * (s₁ * s₂) ∈ p := by
    have e : (l + conjO K l) * (s₁ * s₂) =
        (a₁ * s₂ + (l + conjO K l) * (s₁ * s₂) + conjO K l * l * b₁ * s₁) - a₁ * s₂ -
          conjO K l * l * b₁ * s₁ := by ring
    rw [e]
    refine p.sub_mem (p.sub_mem hN (p.mul_mem_right _ ha₁)) ?_
    have e2 : conjO K l * l * b₁ * s₁ = (conjO K l * l) * (b₁ * s₁) := by ring
    rw [e2]
    exact p.mul_mem_left _ (p.mul_mem_right _ hb₁)
  rcases hpp.mem_or_mem hT with h1 | h1
  · exact hl h1
  · rcases hpp.mem_or_mem h1 with h2 | h2
    · exact (not_mem_of_mem_hcompl hpp hs₁).1 h2
    · exact (not_mem_of_mem_hcompl hpp hs₂).1 h2

end PI.UnitaryGroupMassFormula.CntFormula.UG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsIsomSelfDual
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsIsomMove
open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem star_h (hs : h.IsSymm) (u v : V) : star (h u v) = h v u := by
  first | exact hs u v | exact hs.eq u v

theorem exists_pair (hS : IsHermSemilocal S) (hM : IsSelfDualMod S h M) {ι : Type} [Fintype ι]
    (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} (hr : ∃ v, h v r ≠ 0) (hrx : ∀ i, h (x i) r = 0) :
    ∃ α : K, α ≠ 0 ∧ α⁻¹ • r ∈ M ∧ ∃ w ∈ M, h w (α⁻¹ • r) = 1 ∧ ∀ i, h (x i) w = 0 := by
  classical
  obtain ⟨v, hv⟩ := hr
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ M, h m r = a}
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', M.add_mem hm hm', by simp⟩
      zero_mem' := ⟨0, M.zero_mem, by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, M.neg_mem hm, by simp⟩ }
  have h1 : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    refine ⟨star s • m, hM.smul_mem _ (hS.star_mem s hs) m hm, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  have h2 : ∃ a ∈ A, a ≠ 0 := by
    obtain ⟨t, ht, htv⟩ := hM.span v
    refine ⟨h (t • v) r, ⟨_, htv, rfl⟩, ?_⟩
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    exact mul_ne_zero (star_ne_zero.mpr ht) hv
  have h3 : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    obtain ⟨t, ht, htr⟩ := hM.span r
    refine ⟨t, ht, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    have := hM.int m hm _ htr
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨m₀, hm₀, hα⟩, hα0, hαS⟩ := hS.principal A h1 h2 h3
  have hrM : α⁻¹ • r ∈ M := hM.dual _ fun m hm => by
    rw [map_smul, smul_eq_mul, mul_comm]
    exact hαS _ ⟨m, hm, rfl⟩
  refine ⟨α, hα0, hrM, m₀ - ∑ i, (h (x i) m₀ * (h (x i) (x i))⁻¹) • x i, ?_, ?_, ?_⟩
  · refine M.sub_mem hm₀ (M.sum_mem fun i _ => hM.smul_mem _ ?_ _ (hxM i))
    exact S.mul_mem (hM.int _ (hxM i) _ hm₀) (hxu i).2.2
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
        map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, hrx, mul_zero,
        Finset.sum_const_zero, sub_zero]
    rw [hα, inv_mul_cancel₀ hα0]
  · intro j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hxo j i (Ne.symm hij), mul_zero])
      (by simp), mul_assoc, inv_mul_cancel₀ (hxu j).1, mul_one, sub_self]

theorem isSymm_smul (hs : h.IsSymm) {u : K} (hus : star u = u) : (u⁻¹ • h).IsSymm := by
  have H : ∀ a b : V, star ((u⁻¹ • h) a b) = (u⁻¹ • h) b a := by
    intro a b
    simp only [LinearMap.smul_apply, smul_eq_mul, star_mul', star_inv₀, hus, star_h hs]
  first | exact H | exact ⟨H⟩

theorem exists_of_ref (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M) {ι : Type}
    [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i)))
    (hxM : ∀ i, x i ∈ M) {r : V} {u : K} (hu : IsUnitIn S u) (hus : star u = u) (hrr : h r r = u)
    (hrx : ∀ i, h (x i) r = 0) :
    ∃ z ∈ M, h z z = u ∧ ∀ i, h (x i) z = 0 := by
  have hu0 : u ≠ 0 := hu.1
  obtain ⟨α, hα0, hαM, w, hwM, hw1, hwx⟩ :=
    exists_pair hS hM x hxo hxu hxM ⟨r, by rw [hrr]; exact hu0⟩ hrx
  have hyy : h (α⁻¹ • r) (α⁻¹ • r) = star α⁻¹ * α⁻¹ * u := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, hrr, RingHom.id_apply]
    ring
  have hsa : star α⁻¹ * α⁻¹ ∈ S := by
    have h1 := S.mul_mem (hM.int _ hαM _ hαM) hu.2.2
    rw [hyy, mul_assoc, mul_inv_cancel₀ hu0, mul_one] at h1
    exact h1
  obtain ⟨b, hb, hab⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem hS hsa
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have hs' := isSymm_smul hs hus
  have hyw0 : h (α⁻¹ • r) w = 1 := by rw [← star_h hs, hw1, star_one]
  have hy' : (u⁻¹ • h) (α⁻¹ • r) (α⁻¹ • r) = star (α⁻¹ * b) * (α⁻¹ * b) := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hyy, star_mul']
    rw [mul_comm u⁻¹, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
    linear_combination (-(star α⁻¹ * α⁻¹)) * hb
  have hyw' : (u⁻¹ • h) (α⁻¹ • r) (u • w) = 1 := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, hyw0, mul_one,
      inv_mul_cancel₀ hu0]
  have hww : (u⁻¹ • h) (u • w) (u • w) = u * h w w := by
    simp only [LinearMap.smul_apply, map_smulₛₗ, map_smul, smul_eq_mul, starRingEnd_apply, hus, RingHom.id_apply]
    field_simp
  obtain ⟨c, hc, d, hd, hcd⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_of_pair hS hs'
    (y := α⁻¹ • r) (w := u • w) (a := α⁻¹ * b) hab (mul_ne_zero (inv_ne_zero hα0) hb0) hy' hyw'
    (hww ▸ S.mul_mem hu.2.1 (hM.int w hwM w hwM))
  refine ⟨c • (u • w) + d • (α⁻¹ • r),
    M.add_mem (hM.smul_mem c hc _ (hM.smul_mem u hu.2.1 w hwM)) (hM.smul_mem d hd _ hαM), ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at hcd
    exact ((inv_mul_eq_one₀ (inv_ne_zero hu0 |> fun _ => hu0)).1 hcd).symm
  · intro i
    simp [map_add (f := _), map_smul, hwx i, hrx i]

theorem exists_quasi (hs : h.IsSymm) (w : V) {a : K} (ha : a + star a = a * star a * h w w) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, τ v = v - (a * h w v) • w := by
  let f : K → V →ₗ[K] V := fun b =>
    { toFun := fun v => v - (b * h w v) • w
      map_add' := fun x y => by
        simp only [map_add (f := _), mul_add, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply, smul_sub, smul_smul]
        rw [mul_left_comm] }
  have hf : ∀ b v, f b v = v - (b * h w v) • w := fun _ _ => rfl
  have hcomp : ∀ b c : K, b + c = b * c * h w w → ∀ v : V,
      (v - (c * h w v) • w) - (b * h w (v - (c * h w v) • w)) • w = v := by
    intro b c hbc v
    rw [map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have : c * h w v + b * (h w v - c * h w v * h w w) = 0 := by
      linear_combination (h w v) * hbc
    rw [this, zero_smul, sub_zero]
  have ha' : star a + a = star a * a * h w w := by linear_combination ha
  let τ : V ≃ₗ[K] V := LinearEquiv.ofLinear (f a) (f (star a))
    (LinearMap.ext fun v => hcomp a (star a) ha v)
    (LinearMap.ext fun v => hcomp (star a) a ha' v)
  refine ⟨τ, ?_, fun v => rfl⟩
  intro x y
  change h (x - (a * h w x) • w) (y - (a * h w y) • w) = h x y
  have hsx : star (h w x) = h x w := star_h hs w x
  simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, star_mul', hsx]
  linear_combination (-(h w y * h x w)) * ha

theorem exists_isom_move (hS : IsHermSemilocal S) (hs : h.IsSymm) {x z : V} {u : K} (hu0 : u ≠ 0)
    (hus : star u = u) (hx : h x x = u) (hz : h z z = u) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = z ∧ ∀ v, h x v = 0 → h z v = 0 → τ v = v := by
  have hsy : ∀ a b : V, star (h a b) = h b a := star_h hs
  have key : ∀ y : V, h y y = u → h z y ≠ u →
      ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ y = z ∧ ∀ v, h y v = 0 → h z v = 0 → τ v = v := by
    intro y hy hne
    have hp : u - h z y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hsp : star (u - h z y) ≠ 0 := star_ne_zero.mpr hp
    have hww : h (y - z) (y - z) = (u - h z y) + star (u - h z y) := by
      simp only [map_sub, LinearMap.sub_apply]
      rw [hy, hz, star_sub, hus, hsy]
      ring
    obtain ⟨τ, hτ, hf⟩ := exists_quasi hs (y - z) (a := (u - h z y)⁻¹) (by
      rw [hww, star_inv₀]
      field_simp
      ring)
    refine ⟨τ, hτ, ?_, ?_⟩
    · have hyz : h (y - z) y = u - h z y := by
        simp only [map_sub, LinearMap.sub_apply, hy]
      rw [hf, hyz, inv_mul_cancel₀ hp, one_smul]
      abel
    · intro v hyv hzv
      rw [hf]
      simp only [map_sub, LinearMap.sub_apply, hyv, hzv, sub_zero, mul_zero, zero_smul]
  by_cases hne : h z x = u
  · obtain ⟨θ, -, hθ⟩ := hS.unram
    have hd : θ - star θ ≠ 0 := hθ.1
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      simp at hd
    have hsθ : star θ ≠ 0 := star_ne_zero.mpr hθ0
    have hcc : θ * (star θ)⁻¹ * (star θ * θ⁻¹) = 1 := by field_simp
    have hc1 : θ * (star θ)⁻¹ ≠ 1 := by
      intro h1
      apply hd
      field_simp at h1
      exact sub_eq_zero.mpr h1
    obtain ⟨τ₁, hτ₁, hf₁⟩ := exists_quasi hs x (a := (1 - θ * (star θ)⁻¹) * u⁻¹) (by
      rw [hx]
      simp only [star_mul', star_sub, star_one, star_inv₀, star_star, hus]
      field_simp
      ring)
    have h1x : τ₁ x = (θ * (star θ)⁻¹) • x := by
      rw [hf₁, hx, mul_assoc, inv_mul_cancel₀ hu0, mul_one, sub_smul, one_smul]
      abel
    have hyy : h (τ₁ x) (τ₁ x) = u := by
      have hcx : ∀ c : K, h (c • x) (c • x) = star c * c * u := by
        intro c
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, hx]
        ring
      rw [h1x, hcx, star_mul', star_inv₀, star_star]
      have e1 : star θ * (star θ)⁻¹ = 1 := mul_inv_cancel₀ hsθ
      have e2 : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ0
      linear_combination (θ * θ⁻¹ * u) * e1 + u * e2
    have hzy : h z (τ₁ x) ≠ u := by
      rw [h1x, map_smul, smul_eq_mul, hne]
      intro h2
      apply hc1
      have := mul_right_cancel₀ hu0 (h2.trans (one_mul u).symm)
      exact this
    obtain ⟨τ₂, hτ₂, h2y, h2v⟩ := key _ hyy hzy
    refine ⟨τ₂ * τ₁, (Formalism.HermitianLatticesTheory.isom h).mul_mem hτ₂ hτ₁, ?_, ?_⟩
    · exact h2y
    · intro v hxv hzv
      have h1v : τ₁ v = v := by
        rw [hf₁, hxv, mul_zero, zero_smul, sub_zero]
      change τ₂ (τ₁ v) = v
      rw [h1v]
      refine h2v v ?_ hzv
      rw [h1x, map_smulₛₗ, LinearMap.smul_apply, hxv, smul_zero]
  · exact key x hx hne

end Abs

end PI.UnitaryGroupMassFormula.CntFormula.UG
end
end

open NumberField Module

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

section Abs

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}

def PairUnit (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ w y : V, h y w = 1 → h w w ∈ S → h y y ∈ S →
    ∃ c ∈ S, ∃ d ∈ S, IsUnitIn S (h (c • w + d • y) (c • w + d • y))

theorem linIndep_orth {ι : Type} [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hx0 : ∀ i, h (x i) (x i) ≠ 0) : LinearIndependent K x := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (h (x j)) hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (hx0 j)
  · intro i _ hij
    rw [map_smul, hxo j i (Ne.symm hij), smul_zero]
  · simp

theorem orth_sub_proj {ι : Type} [Fintype ι] (x : ι → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hx0 : ∀ i, h (x i) (x i) ≠ 0) (v : V) (j : ι) :
    h (x j) (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, Finset.sum_eq_single j]
  · rw [map_smul, smul_eq_mul, mul_right_comm, inv_mul_cancel₀ (hx0 j), one_mul, sub_self]
  · intro i _ hij
    rw [map_smul, hxo j i (Ne.symm hij), smul_zero]
  · simp

theorem exists_ortho_unit [FiniteDimensional K V] (hS : IsHermSemilocal S) (hs : h.IsSymm)
    (hnd : h.Nondegenerate) (hPU : PairUnit S h) {L : AddSubgroup V} (hL : IsSelfDualMod S h L) :
    ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) ∧ (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
      ∀ i, IsUnitIn S (h (x i) (x i)) :=
  _root_.UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit hS hs hnd hPU hL

theorem exists_isom_frameU (hS : IsHermSemilocal S) (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {n : ℕ} (x : Fin n → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (x i) ∈ M := by
  classical
  have P : ∀ k, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, i.val < k → g (x i) ∈ M := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (by omega)
      have hg' : ∀ a b, h (g a) (g b) = h a b := hg
      have hne : ∀ i : Fin n, i.val < k → i ≠ ⟨k, hk⟩ := by
        intro i hi e
        rw [e] at hi
        exact lt_irrefl _ hi
      let y : {i : Fin n // i.val < k} → V := fun i => g (x i.1)
      have hyo : ∀ i j : {i : Fin n // i.val < k}, i ≠ j → h (y i) (y j) = 0 := by
        intro i j hij
        simp only [y]
        rw [hg']
        exact hxo _ _ (fun e => hij (Subtype.ext e))
      have hyu : ∀ i : {i : Fin n // i.val < k}, IsUnitIn S (h (y i) (y i)) := by
        intro i
        simp only [y]
        rw [hg']
        exact hxu _
      have hyM : ∀ i : {i : Fin n // i.val < k}, y i ∈ M := fun i => hgM i.1 i.2
      have hu := hxu ⟨k, hk⟩
      have hus : star (h (x ⟨k, hk⟩) (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := star_h hs _ _
      have hrr : h (g (x ⟨k, hk⟩)) (g (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := hg' _ _
      have hrx : ∀ i : {i : Fin n // i.val < k}, h (y i) (g (x ⟨k, hk⟩)) = 0 := by
        intro i
        simp only [y]
        rw [hg']
        exact hxo _ _ (hne i.1 i.2)
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_of_ref hS hs hM y hyo hyu hyM hu hus hrr hrx
      obtain ⟨τ, hτ, hτr, hτfix⟩ := exists_isom_move hS hs hu.1 hus hrr hzz
      refine ⟨τ * g, mul_mem hτ hg, fun i hi => ?_⟩
      show τ (g (x i)) ∈ M
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
      · rw [hτfix]
        · exact hgM i h1
        · rw [hg']
          exact hxo _ _ (fun e => hne i h1 e.symm)
        · rw [← star_h hs]
          have := hzo ⟨i, h1⟩
          simp only [y] at this
          rw [this, star_zero]
      · have : i = ⟨k, hk⟩ := Fin.ext h1
        rw [this, hτr]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := P n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩

theorem exists_isom_selfDual [FiniteDimensional K V] (hS : IsHermSemilocal S) (hs : h.IsSymm)
    (hnd : h.Nondegenerate) (hPU : PairUnit S h) {L M : AddSubgroup V} (hL : IsSelfDualMod S h L)
    (hM : IsSelfDualMod S h M) : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, v ∈ L ↔ g v ∈ M := by
  classical
  obtain ⟨x, hxL, hxo, hxu⟩ := exists_ortho_unit hS hs hnd hPU hL
  obtain ⟨g, hg, hgM⟩ := exists_isom_frameU hS hs hM x hxo hxu
  have hg' : ∀ a b, h (g a) (g b) = h a b := hg
  have hli := linIndep_orth x hxo (fun i => (hxu i).1)
  have hspan : Submodule.span K (Set.range x) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hexp : ∀ v, v = ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i := by
    intro v
    have hxv' := orth_sub_proj x hxo (fun i => (hxu i).1) v
    have hall : ∀ y, h y (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0 := by
      intro y
      have hy : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨j, rfl⟩ := ha
        exact hxv' j
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul c a _ ha => simp [ha]
    exact sub_eq_zero.1 (hnd.2 _ hall)
  have hfwd : ∀ v, v ∈ L → g v ∈ M := by
    intro v hv
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hexp v, map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul]
    exact hM.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hv)) _ (hgM i)
  refine ⟨g, hg, fun v => ⟨hfwd v, fun hv => hL.dual v fun m hm => ?_⟩⟩
  rw [← hg']
  exact hM.int _ (hfwd m hm) _ hv

end Abs

end PI.UnitaryGroupMassFormula.CntFormula.UG
end
end

open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

theorem unimodOneGenus_of (hP : PairUnitLoc) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus := by
  intro K _ _ _ V _ _ _ _ _ h hK hs hnd L M hLl hMl hLu hMu p hp
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    PI.UG.W.star_mem_range K
  have huL := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar L hLl.fg).2.mp hLu p hp
  have huM := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar M hMl.fg).2.mp hMu p hp
  have hS := isHermSemilocal_locRing hK hp
  have hLfull : Submodule.IsFullLattice K L :=
    { toIsLattice := hLl
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs hnd hLl hLu }
  have hMfull : Submodule.IsFullLattice K M :=
    { toIsLattice := hMl
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs hnd hMl hMu }
  have hL' := isSelfDualMod_loc hLfull hp.isPrime huL
  have hM' := isSelfDualMod_loc hMfull hp.isPrime huM
  obtain ⟨g, hg, hiff⟩ := exists_isom_selfDual hS hs hnd
    (fun w y hyw hw hy => hP K hK p hp V h hs w y hyw hw hy) hL' hM'
  refine ⟨g, hg, ?_⟩
  ext w
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hiff v).1 hv
  · intro hw
    refine ⟨g.symm w, (hiff _).2 ?_, by simp⟩
    simpa using hw

theorem unimodular_one_genus : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus :=
  unimodOneGenus_of pair_unit_local

end PI.UnitaryGroupMassFormula.CntFormula.UG
end
end

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem row_surjective : RowSurj := rowSurj_of_genus PI.UnitaryGroupMassFormula.CntFormula.UG.unimodular_one_genus

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
