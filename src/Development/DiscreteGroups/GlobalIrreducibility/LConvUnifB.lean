module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import ReciprocityTheory.BurnsideSurjectivity.Burnside

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvUnifA
noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

include hρ hKc hKo

theorem fixedProj_eq_avg {L : Subgroup G} (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) :
    ∃ (N : ℕ) (r : Fin N → G), 0 < N ∧ (∀ i, r i ∈ K) ∧
      ∀ v : V, v ∈ fixedVectors ρ L →
        (fixedProj ρ hρ hKc hKo v : V) = (N : ℂ)⁻¹ • ∑ i, ρ (r i) v := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hLo.preimage continuous_subtype_val
  have : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  have hNpos : 0 < Fintype.card (K ⧸ L.subgroupOf K) :=
    Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk (1 : K)⟩
  let eQ := Fintype.equivFin (K ⧸ L.subgroupOf K)
  refine ⟨Fintype.card (K ⧸ L.subgroupOf K), fun i => ((Quotient.out (eQ.symm i) : K) : G), hNpos,
    fun i => (Quotient.out (eQ.symm i)).2, ?_⟩
  intro v hv
  obtain ⟨s, hs⟩ : ∃ s : V, s = ∑ q : K ⧸ L.subgroupOf K, ρ ((Quotient.out q : K) : G) v := ⟨_, rfl⟩
  have hreidx : ∑ i, ρ ((Quotient.out (eQ.symm i) : K) : G) v = s := by
    rw [hs]
    exact Fintype.sum_equiv eQ.symm _ _ (fun _ => rfl)
  have hsK : s ∈ fixedVectors ρ K := by
    intro k hk
    have key : ∀ q : K ⧸ L.subgroupOf K, ρ k (ρ ((Quotient.out q : K) : G) v) =
        ρ ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : G) v := by
      intro q
      rw [← Module.End.mul_apply, ← map_mul]
      have h1 : (((⟨k, hk⟩ : K) * Quotient.out q : K) : G) = k * ((Quotient.out q : K) : G) := rfl
      rw [← h1]
      apply act_eq_of_mk_eq ρ hv
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum, Finset.sum_congr rfl (fun q _ => key q)]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun _ => rfl)
  have hsub : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v ∈ coinvariantsKer ρ K := by
    have h1 : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v =
        ∑ q : K ⧸ L.subgroupOf K, (ρ ((Quotient.out q : K) : G) v - v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, hs]
    rw [h1]
    exact Submodule.sum_mem _ fun q _ => sub_mem_coinvariantsKer (Quotient.out q).2 v
  have h1 : (fixedProj ρ hρ hKc hKo s : V) = s := fixedProj_apply_of_mem hρ hKc hKo hsK
  have h2 := fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo hsub
  rw [map_sub, map_smul, sub_eq_zero] at h2
  have h3 : ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • (fixedProj ρ hρ hKc hKo v : V) = s := by
    rw [← h1, h2, Submodule.coe_smul]
  rw [hreidx, ← h3, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_smul]

theorem map_fixedProj_of_invariant {U : Type*} [AddCommGroup U] [Module ℂ U] (f : V →ₗ[ℂ] U)
    (v : V) (hf : ∀ k ∈ K, f (ρ k v) = f v) : f (fixedProj ρ hρ hKc hKo v : V) = f v := by
  have hLo : IsOpen ((K ⊓ stabilizerOf ρ v : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter (hρ v)
  obtain ⟨N, r, hN, hr, h⟩ := fixedProj_eq_avg hρ hKc hKo (L := K ⊓ stabilizerOf ρ v) inf_le_left hLo
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h v (fun l hl => hl.2), map_smul, map_sum, Finset.sum_congr rfl (fun i _ => hf (r i) (hr i)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]


variable (ρ) in
def hop (g : G) : Module.End ℂ (fixedVectors ρ K) :=
  (fixedProj ρ hρ hKc hKo) ∘ₗ (ρ g) ∘ₗ (fixedVectors ρ K).subtype

theorem hop_apply (g : G) (w : fixedVectors ρ K) :
    hop ρ hρ hKc hKo g w = fixedProj ρ hρ hKc hKo (ρ g w) := rfl

theorem hop_of_mem {κ : G} (hκ : κ ∈ K) : hop ρ hρ hKc hKo κ = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [hop_apply, fixedProj_apply_act hρ hKc hKo hκ, Module.End.one_apply,
    fixedProj_apply_of_mem hρ hKc hKo w.2]

theorem hop_one : hop ρ hρ hKc hKo 1 = 1 := hop_of_mem hρ hKc hKo K.one_mem

theorem hop_mul {g h : G}
    (H : ∀ w ∈ fixedVectors ρ K, ∀ κ ∈ K,
      fixedProj ρ hρ hKc hKo (ρ (g * κ * h) w) = fixedProj ρ hρ hKc hKo (ρ (g * h) w)) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h = hop ρ hρ hKc hKo (g * h) := by
  refine LinearMap.ext fun w => ?_
  show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) =
    fixedProj ρ hρ hKc hKo (ρ (g * h) w)
  have key := map_fixedProj_of_invariant hρ hKc hKo ((fixedProj ρ hρ hKc hKo) ∘ₗ ρ g) (ρ h w)
    (fun κ hκ => by
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, H w w.2 κ hκ,
        map_mul, Module.End.mul_apply])
  simp only [LinearMap.comp_apply] at key
  rw [key, map_mul, Module.End.mul_apply]

theorem hop_mul_mem_span (g h : G) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  let L : Subgroup G := K ⊓ K.comap (MulAut.conj h⁻¹).toMonoidHom
  have hLo : IsOpen (L : Set G) := by
    have hc : Continuous fun x : G => h⁻¹ * x * h⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hKo.inter (hKo.preimage hc)
  obtain ⟨N, r, hN, -, hav⟩ := fixedProj_eq_avg hρ hKc hKo (L := L) inf_le_left hLo
  have hfix : ∀ w : fixedVectors ρ K, ρ h (w : V) ∈ fixedVectors ρ L := by
    intro w l hl
    have hl2 : h⁻¹ * l * h ∈ K := by
      have := hl.2
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
    calc ρ l (ρ h w) = ρ h (ρ (h⁻¹ * l * h) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; congr 2; group
      _ = ρ h w := by rw [w.2 _ hl2]
  have heq : hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h =
      (N : ℂ)⁻¹ • ∑ i, hop ρ hρ hKc hKo (g * r i * h) := by
    refine LinearMap.ext fun w => ?_
    show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hav _ (hfix w), map_smul, map_smul, map_sum, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = fixedProj ρ hρ hKc hKo (ρ (g * r i * h) w)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩)

theorem span_hop_mul_mem {a b : Module.End ℂ (fixedVectors ρ K)}
    (ha : a ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)))
    (hb : b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo))) :
    a * b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      exact hop_mul_mem_span hρ hKc hKo g h
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem span_hop_eq_top [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    [Nontrivial (fixedVectors ρ K)] :
    Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) = ⊤ := by
  have hone : (1 : Module.End ℂ (fixedVectors ρ K)) ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
    rw [← hop_one hρ hKc hKo]; exact Submodule.subset_span ⟨1, rfl⟩
  let A : Subalgebra ℂ (Module.End ℂ (fixedVectors ρ K)) :=
    Submodule.toSubalgebra _ hone (fun a b ha hb => span_hop_mul_mem hρ hKc hKo ha hb)
  have hirr : ∀ U : Submodule ℂ (fixedVectors ρ K),
      (∀ a : A, ∀ w ∈ U, A.val a w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hT : ∀ g, hop ρ hρ hKc hKo g u ∈ U := fun g =>
      hU ⟨hop ρ hρ hKc hKo g, Submodule.subset_span ⟨g, rfl⟩⟩ u huU
    rw [eq_top_iff]
    intro w _
    have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hw := HeckeAlgebra.mem_span_orbit (ρ := ρ) hu0' (w : V)
    have hww : w = fixedProj ρ hρ hKc hKo (w : V) :=
      Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2).symm
    rw [hww]
    have hle : Submodule.map (fixedProj ρ hρ hKc hKo)
        (Submodule.span ℂ (Set.range fun g => ρ g (u : V))) ≤ U := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hT g
    exact hle ⟨_, hw, rfl⟩
  have hsurj := ReciprocityTheory.GC.burnside_surj_of_irred (k := ℂ) A.val hirr
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := hsurj x
  rw [← ha]
  exact a.2

end DiscreteGroups.sglob.LConvU
end
end

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic GroundTheory.Automorphic.Cartan
  GroundTheory.Automorphic.Parabolic ValuativeRel Matrix

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem diagPow_add (μ ν : Fin n → ℤ) : diagPow F n (μ + ν) = diagPow F n μ * diagPow F n ν := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_diagPow, coe_diagPow, coe_diagPow, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, zpow_add₀ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero F)]

theorem diagPow_zero : diagPow F n 0 = 1 := by
  refine Units.ext ?_
  rw [coe_diagPow, Units.val_one]
  simp

theorem diagPow_neg (μ : Fin n → ℤ) : diagPow F n (-μ) = (diagPow F n μ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← diagPow_add, neg_add_cancel, diagPow_zero]

theorem diagPow_conj_apply (c : Fin n → ℤ) (x : GL (Fin n) F) (i j : Fin n) :
    ((diagPow F n c * x * (diagPow F n c)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (GLnLocal.uniformizer F : F) ^ c i * x i j * (GLnLocal.uniformizer F : F) ^ (-c j) := by
  rw [Units.val_mul, Units.val_mul, coe_diagPow]
  change (diagonal (fun i => (GLnLocal.uniformizer F : F) ^ c i) * (x : Matrix (Fin n) (Fin n) F) *
    diagonal fun i => (GLnLocal.uniformizer F : F) ^ (-c i)) i j = _
  rw [mul_diagonal, diagonal_mul]

theorem conj_mem_congruenceSubgroup_of_zero {r : ℕ} (c : Fin n → ℤ) (H : Subgroup (GL (Fin n) F))
    (hH : H ≤ GLnLocal.congruenceSubgroup F n r) (hz : ∀ x ∈ H, ∀ i j, c i < c j → x i j = 0)
    {x : GL (Fin n) F} (hx : x ∈ H) :
    diagPow F n c * x * (diagPow F n c)⁻¹ ∈ GLnLocal.congruenceSubgroup F n r := by
  have hb : ∀ y ∈ H, ∀ i j, valuation F
      (((diagPow F n c * y * (diagPow F n c)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F (GLnLocal.uniformizer F : F) ^ r := by
    intro y hy i j
    have hyK := ((GLnLocal.mem_congruenceSubgroup_iff F n).1 (hH hy)).2 i j
    rw [diagPow_conj_apply]
    by_cases hij : i = j
    · subst hij
      rw [mul_comm ((GLnLocal.uniformizer F : F) ^ c i), mul_assoc,
        ← zpow_add₀ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero F), add_neg_cancel, zpow_zero,
        mul_one]
      exact hyK
    · rw [one_apply_ne hij, sub_zero] at hyK ⊢
      by_cases hlt : c i < c j
      · rw [hz y hy i j hlt, mul_zero, zero_mul, map_zero]
        exact zero_le
      · rw [not_lt] at hlt
        obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hlt)
        have he : (GLnLocal.uniformizer F : F) ^ c i * y i j * (GLnLocal.uniformizer F : F) ^ (-c j) =
            (GLnLocal.uniformizer F : F) ^ d * y i j := by
          rw [mul_comm _ (y i j), mul_assoc,
            ← zpow_add₀ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero F), ← sub_eq_add_neg, hd,
            zpow_natCast, mul_comm]
        rw [he, map_mul, map_pow]
        calc valuation F (GLnLocal.uniformizer F : F) ^ d * valuation F (y i j)
            ≤ 1 * valuation F (y i j) := by
              gcongr
              exact pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le d
          _ = valuation F (y i j) := one_mul _
          _ ≤ _ := hyK
  have h2 : ∀ i j, valuation F (((diagPow F n c * x * (diagPow F n c)⁻¹)⁻¹ : GL (Fin n) F) i j -
      (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F (GLnLocal.uniformizer F : F) ^ r := by
    have he : (diagPow F n c * x * (diagPow F n c)⁻¹)⁻¹ = diagPow F n c * x⁻¹ * (diagPow F n c)⁻¹ := by
      group
    rw [he]
    exact hb x⁻¹ (H.inv_mem hx)
  have hle : valuation F (GLnLocal.uniformizer F : F) ^ r ≤ 1 :=
    pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le r
  have hint : ∀ (z : F) (i j : Fin n),
      valuation F (z - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F (GLnLocal.uniformizer F : F) ^ r → z ∈ 𝒪[F] := by
    intro z i j hz
    refine (Valuation.mem_integer_iff _ _).mpr ?_
    have he : z = (z - (1 : Matrix (Fin n) (Fin n) F) i j) +
        (1 : Matrix (Fin n) (Fin n) F) i j := by ring
    rw [he]
    apply Valuation.map_add_le _ (hz.trans hle)
    by_cases hij : i = j
    · rw [hij, one_apply_eq, map_one]
    · rw [one_apply_ne hij, map_zero]
      exact zero_le
  rw [GLnLocal.mem_congruenceSubgroup_iff F n, GLnLocal.mem_integralGL_iff F n]
  exact ⟨⟨fun i j => hint _ i j (hb x hx i j), fun i j => hint _ i j (h2 i j)⟩, hb x hx⟩

theorem diagPow_comm_of_mem_levi (c : Fin n → ℤ) {y : GL (Fin n) F}
    (hy : y ∈ levi F n (id : Fin n → Fin n)) : diagPow F n c * y = y * diagPow F n c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diagPow]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : i = j
  · subst hij
    rw [mul_comm]
  · have h0 := mem_levi.1 hy i j hij
    simp only [h0, mul_zero, zero_mul]

theorem dominant_conj {r : ℕ} (hr : 1 ≤ r) {μ ν : Fin n → ℤ} (hμ : IsDominant μ)
    (hν : IsDominant ν) {κ : GL (Fin n) F} (hκ : κ ∈ GLnLocal.congruenceSubgroup F n r) :
    ∃ a ∈ GLnLocal.congruenceSubgroup F n r, ∃ b ∈ GLnLocal.congruenceSubgroup F n r,
      ∃ c ∈ GLnLocal.congruenceSubgroup F n r,
        diagPow F n μ * κ * diagPow F n ν = a * (diagPow F n μ * diagPow F n ν) * b * c := by
  obtain ⟨z, hz, y, hy, x, hx, hk⟩ := congruenceSubgroup_iwahoriFactorization (F := F)
    (id : Fin n → Fin n) hr κ⁻¹ (inv_mem hκ)
  have hκ' : κ = x⁻¹ * y⁻¹ * z⁻¹ := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, ← hk, inv_inv]
  refine ⟨diagPow F n μ * x⁻¹ * (diagPow F n μ)⁻¹, ?_, y⁻¹, inv_mem hy.1,
    diagPow F n (-ν) * z⁻¹ * (diagPow F n (-ν))⁻¹, ?_, ?_⟩
  · refine conj_mem_congruenceSubgroup_of_zero μ
      (GLnLocal.congruenceSubgroup F n r ⊓ unipotentRadical F n (id : Fin n → Fin n)) inf_le_left ?_
      (inv_mem hx)
    intro w hw i j hij
    have hji : j < i := by
      by_contra h
      rw [not_lt] at h
      exact absurd hij (not_lt.2 (hμ h))
    exact (Iwasawa.mem_blockUpper F n).1 (mem_unipotentRadical.1 hw.2).1 hji
  · refine conj_mem_congruenceSubgroup_of_zero (-ν)
      (GLnLocal.congruenceSubgroup F n r ⊓ oppositeUnipotentRadical F n (id : Fin n → Fin n)) inf_le_left ?_
      (inv_mem hz)
    intro w hw i j hij
    have hij' : i < j := by
      by_contra h
      rw [not_lt] at h
      have := hν h
      simp only [Pi.neg_apply] at hij
      omega
    exact (mem_oppositeUnipotentRadical.1 hw.2).1 i j hij'
  · have hc : diagPow F n ν * y⁻¹ = y⁻¹ * diagPow F n ν :=
      diagPow_comm_of_mem_levi ν (inv_mem hy.2)
    have hb : y⁻¹ = diagPow F n ν * y⁻¹ * (diagPow F n ν)⁻¹ := by
      rw [hc, mul_inv_cancel_right]
    rw [diagPow_neg, hκ']
    conv_lhs => rw [hb]
    group

end Local

def gen (n : ℕ) (i : Fin (n + 1)) (j : Fin n) : ℤ :=
  if (i : ℕ) = n then -1 else if (j : ℕ) ≤ i then 1 else 0

theorem gen_dominant (n : ℕ) (i : Fin (n + 1)) : IsDominant (gen n i) := by
  intro j j' hjj'
  have h : (j : ℕ) ≤ j' := hjj'
  simp only [gen]
  split_ifs <;> omega

theorem dom_nonneg {n : ℕ} (P : (Fin n → ℤ) → Prop) (h0 : P 0) (hgen : ∀ i, P (gen n i))
    (hadd : ∀ μ ν, IsDominant μ → IsDominant ν → P μ → P ν → P (μ + ν)) :
    ∀ N : ℕ, ∀ μ : Fin n → ℤ, IsDominant μ → (∀ j, 0 ≤ μ j) → ∑ j, μ j ≤ N → P μ := by
  classical
  intro N
  induction N with
  | zero =>
    intro μ _ hμ0 hs
    have hs0 : ∑ j, μ j = 0 :=
      le_antisymm (by exact_mod_cast hs) (Finset.sum_nonneg fun j _ => hμ0 j)
    have : μ = 0 := funext fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hμ0 j)).1 hs0 j (Finset.mem_univ j)
    rw [this]; exact h0
  | succ N ih =>
    intro μ hμ hμ0 hs
    by_cases hall : ∀ j, μ j = 0
    · have : μ = 0 := funext hall
      rw [this]; exact h0
    obtain ⟨j0, hj0⟩ := not_forall.1 hall
    obtain ⟨i, hi_pos, hi_max⟩ : ∃ i : Fin n, 0 < μ i ∧ ∀ j, 0 < μ j → j ≤ i := by
      have hSne : (Finset.univ.filter fun j => 0 < μ j).Nonempty :=
        ⟨j0, Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne (hμ0 j0) (Ne.symm hj0)⟩⟩
      exact ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hSne)).2,
        fun j hj => Finset.le_max' _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
    have hle : ∀ j : Fin n, (j : ℕ) ≤ i → 1 ≤ μ j := fun j hj => by
      have := hμ (show j ≤ i from hj); omega
    have hgt : ∀ j : Fin n, ¬ (j : ℕ) ≤ i → μ j = 0 := fun j hj => by
      have h1 := hμ0 j
      by_contra hne
      exact hj (hi_max j (lt_of_le_of_ne h1 (Ne.symm hne)))
    have hin : ¬ ((i : ℕ) = n) := by have := i.2; omega
    have hν1 : ∀ j : Fin n, (j : ℕ) ≤ i → gen n (Fin.castSucc i) j = 1 := fun j hj => by
      simp only [gen, Fin.val_castSucc, if_neg hin, if_pos hj]
    have hν0 : ∀ j : Fin n, ¬ (j : ℕ) ≤ i → gen n (Fin.castSucc i) j = 0 := fun j hj => by
      simp only [gen, Fin.val_castSucc, if_neg hin, if_neg hj]
    have hdom' : IsDominant (μ - gen n (Fin.castSucc i)) := by
      intro j j' hjj'
      have h := hμ hjj'
      have hj : (j : ℕ) ≤ j' := hjj'
      simp only [Pi.sub_apply]
      by_cases h1 : (j' : ℕ) ≤ i
      · rw [hν1 j' h1, hν1 j (le_trans hj h1)]; omega
      · rw [hν0 j' h1, hgt j' h1]
        by_cases h2 : (j : ℕ) ≤ i
        · rw [hν1 j h2]; have := hle j h2; omega
        · rw [hν0 j h2]; have := hμ0 j; omega
    have hdec : μ = gen n (Fin.castSucc i) + (μ - gen n (Fin.castSucc i)) := by abel
    rw [hdec]
    refine hadd _ _ (gen_dominant n _) hdom' (hgen _) (ih _ hdom' ?_ ?_)
    · intro j
      simp only [Pi.sub_apply]
      by_cases h2 : (j : ℕ) ≤ i
      · rw [hν1 j h2]; have := hle j h2; omega
      · rw [hν0 j h2]; have := hμ0 j; omega
    · have hνsum : 1 ≤ ∑ j, gen n (Fin.castSucc i) j := by
        calc (1 : ℤ) = gen n (Fin.castSucc i) i := (hν1 i le_rfl).symm
          _ ≤ ∑ j, gen n (Fin.castSucc i) j := Finset.single_le_sum (fun j _ => by
              by_cases h2 : (j : ℕ) ≤ i
              · rw [hν1 j h2]; norm_num
              · rw [hν0 j h2]) (Finset.mem_univ i)
      have hsub : ∑ j, (μ - gen n (Fin.castSucc i)) j =
          ∑ j, μ j - ∑ j, gen n (Fin.castSucc i) j := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [hsub]
      push_cast at hs ⊢
      omega

theorem dom_induct {n : ℕ} (P : (Fin n → ℤ) → Prop) (h0 : P 0) (hgen : ∀ i, P (gen n i))
    (hadd : ∀ μ ν, IsDominant μ → IsDominant ν → P μ → P ν → P (μ + ν)) :
    ∀ μ, IsDominant μ → P μ := by
  have hnn := dom_nonneg P h0 hgen hadd
  have hneg : ∀ k : ℕ, P (fun _ => -(k : ℤ)) := by
    intro k
    induction k with
    | zero =>
      have : (fun _ : Fin n => -((0 : ℕ) : ℤ)) = 0 := by funext; simp
      rw [this]; exact h0
    | succ k ih =>
      have hl : gen n (Fin.last n) = fun _ => -1 := by funext j; simp [gen]
      have : (fun _ : Fin n => -((k + 1 : ℕ) : ℤ)) = (fun _ => -(k : ℤ)) + gen n (Fin.last n) := by
        rw [hl]; funext j; simp only [Pi.add_apply]; push_cast; ring
      rw [this]
      exact hadd _ _ (fun _ _ _ => le_rfl) (gen_dominant n _) ih (hgen _)
  intro μ hμ
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ∑ j, (μ j).natAbs := ⟨_, rfl⟩
  have hbound : ∀ j, -(d : ℤ) ≤ μ j := by
    intro j
    have h1 : (μ j).natAbs ≤ d := by
      rw [hd]
      exact Finset.single_le_sum (f := fun j => (μ j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h1' : ((μ j).natAbs : ℤ) ≤ d := by exact_mod_cast h1
    have h2 := neg_abs_le (μ j)
    rw [← Int.natCast_natAbs] at h2
    omega
  have hdec : μ = (μ + fun _ => (d : ℤ)) + fun _ => -(d : ℤ) := by
    funext j; simp only [Pi.add_apply]; ring
  rw [hdec]
  refine hadd _ _ ?_ (fun _ _ _ => le_rfl) ?_ (hneg d)
  · intro j j' hjj'; simp only [Pi.add_apply]; have := hμ hjj'; omega
  · refine hnn (∑ j, (μ j + d)).toNat _ ?_ ?_ ?_
    · intro j j' hjj'; simp only [Pi.add_apply]; have := hμ hjj'; omega
    · intro j; simp only [Pi.add_apply]; have := hbound j; omega
    · simp only [Pi.add_apply]; exact Int.self_le_toNat _

end DiscreteGroups.sglob.LConvU
