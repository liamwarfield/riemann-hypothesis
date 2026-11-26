module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem finOrb_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K K' L : Subgroup G} (hL : IsCompact (L : Set G)) (hK : K ≤ L) (hK' : IsOpen (K' : Set G)) (x : G) :
    FinOrb K K' x := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : Continuous fun g : G => ((g * x : G) : G ⧸ K') :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hL.image hc).finite_of_discrete).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g, hK g.2, rfl⟩

private theorem iwC_le_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ KO k (Fin n) := by
  refine sup_le (sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right) ?_
  rintro _ ⟨t, ht, rfl⟩
  refine iwahori_le_KO k (Fin n) (diagT_mem_iwahori fun i => ?_)
  obtain ⟨u, -, hu⟩ := ht i trivial
  rw [← hu]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit u)

theorem UpperTheory.V.AlgebraTools.heckePairIwC :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), HeckePair (iwC k n C) ∧ HeckePair (KO k (Fin n)) ∧ ∀ (C' : Subgroup 𝓀[k]ˣ), FinOrb (iwC k n C') (iwC k n C) 1 ∧ FinOrb (KO k (Fin n)) (iwC k n C) 1 := by
  intro k _ _ _ _ n C
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  exact ⟨fun x => finOrb_of_compact hc (iwC_le_KO k n C) ho x,
    fun x => finOrb_of_compact hc le_rfl GlobalTheory.SplitFlip.isOpen_KO x,
    fun C' => ⟨finOrb_of_compact hc (iwC_le_KO k n C') ho 1, finOrb_of_compact hc le_rfl ho 1⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkNorm_mem {G : Type} [Group G] (I : Subgroup G) (x y : G) :
    (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, y = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have h : (((a : G) * x : G) : G ⧸ I) = (y : G ⧸ I) := ha
    rw [QuotientGroup.eq] at h
    exact ⟨a, a.2, _, h, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [QuotientGroup.mk_mul_of_mem _ hb]
    rfl

private theorem hkNorm_reps {G : Type} [Group G] (I : Subgroup G) (x : G) (h : FinOrb I I x) :
    ∃ s : Finset G, (∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I)) ∧
      ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q := by
  classical
  refine ⟨(Set.Finite.toFinset h).image Quotient.out, fun y hy => ?_, fun q hq => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']
    exact (Set.Finite.mem_toFinset h).1 hq
  · refine ⟨q.out, ⟨Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset h).2 hq), QuotientGroup.out_eq' q⟩, ?_⟩
    rintro y ⟨hy, rfl⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [QuotientGroup.out_eq']

private theorem hkNorm_tr {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x u w : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (hw : w ∈ Subgroup.normalizer (I : Set G))
    (s : Finset G) (h1 : ∀ y ∈ s, (y : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I))
    (h2 : ∀ q ∈ MulAction.orbit I (x : G ⧸ I), ∃! y, y ∈ s ∧ (y : G ⧸ I) = q) (v : fixd ρ I) :
    (hk ρ I (u * x * w) v : M) = ∑ y ∈ s, ρ (u * y * w) v := by
  classical
  have cu : ∀ a ∈ I, u * a * u⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hu a).1 ha
  have cu' : ∀ a ∈ I, u⁻¹ * a * u ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hu a).1 ha
  have cw : ∀ a ∈ I, w * a * w⁻¹ ∈ I := fun a ha => (Subgroup.mem_normalizer_iff.1 hw a).1 ha
  have cw' : ∀ a ∈ I, w⁻¹ * a * w ∈ I := fun a ha => (Subgroup.mem_normalizer_iff''.1 hw a).1 ha
  have key := (hkApply A G M ρ I I (u * x * w) (hI _)).2.1 (s.image fun y => u * y * w) ?_ ?_ v
  · rw [Finset.sum_image (fun a _ b _ h => by simpa using h)] at key
    exact key
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I x z).1 (h1 z hz)
    exact (hkNorm_mem I _ _).2 ⟨_, cu a ha, _, cw' b hb, by group⟩
  · intro q hq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    obtain ⟨y, ⟨hy, hyq⟩, huniq⟩ := h2 ((u⁻¹ * a * u * x : G) : G ⧸ I)
      ((hkNorm_mem I _ _).2 ⟨_, cu' a ha, 1, one_mem _, by group⟩)
    refine ⟨u * y * w, ⟨Finset.mem_image_of_mem _ hy, ?_⟩, ?_⟩
    · rw [QuotientGroup.eq] at hyq ⊢
      convert mul_mem (cw' _ hyq) hb using 1
      group
    · rintro y' ⟨hy', h⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy'
      rw [huniq z ⟨hz, ?_⟩]
      rw [QuotientGroup.eq] at h ⊢
      convert cw _ (mul_mem h (inv_mem hb)) using 1
      group

private theorem hkNorm_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (v : fixd ρ I) : (hk ρ I u v : M) = ρ u v := by
  have h := hkNorm_tr ρ I hI 1 u 1 hu (one_mem _) {1} (by simp) (fun q hq => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := (hkNorm_mem I _ z).1 hq
    refine ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩
    rw [QuotientGroup.eq]
    simpa using mul_mem ha hb) v
  simpa using h

private theorem hkNorm_mul {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (u : G)
    (hu : u ∈ Subgroup.normalizer (I : Set G)) (x : G) :
    hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  obtain ⟨s, h1, h2⟩ := hkNorm_reps I x (hI x)
  have h0 := hkNorm_tr ρ I hI x 1 1 (one_mem _) (one_mem _) s h1 h2
  have hl := hkNorm_tr ρ I hI x u 1 hu (one_mem _) s h1 h2
  have hr := hkNorm_tr ρ I hI x 1 u (one_mem _) hu s h1 h2
  simp only [one_mul, mul_one] at h0 hl hr
  constructor
  · ext v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hl, Module.End.mul_apply, hkNorm_one ρ I hI u hu, h0, map_sum]
    simp only [map_mul, Module.End.mul_apply]
  · ext v
    rw [hr, Module.End.mul_apply, h0, hkNorm_one ρ I hI u hu]
    simp only [map_mul, Module.End.mul_apply]

theorem UpperTheory.V.AlgebraTools.hkNorm :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (u : G), HeckePair I → u ∈ Subgroup.normalizer (I : Set G) → (∀ v : fixd ρ I, (hk ρ I u v : M) = ρ u v) ∧ hk ρ I 1 = 1 ∧ IsUnit (hk ρ I u) ∧ ∀ x : G, hk ρ I (u * x) = hk ρ I u * hk ρ I x ∧ hk ρ I (x * u) = hk ρ I x * hk ρ I u := by
  intro A G M _ _ _ _ ρ I u hI hu
  have h1 : hk ρ I 1 = 1 := by
    ext v
    rw [hkNorm_one ρ I hI 1 (one_mem _)]
    simp
  refine ⟨hkNorm_one ρ I hI u hu, h1, ⟨⟨hk ρ I u, hk ρ I u⁻¹, ?_, ?_⟩, rfl⟩, hkNorm_mul ρ I hI u hu⟩
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).1, mul_inv_cancel, h1]
  · rw [← (hkNorm_mul ρ I hI u hu u⁻¹).2, inv_mul_cancel, h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleOrbit
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

private noncomputable def elem {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : R) : GL (Fin n) R :=
  ⟨1 + single i j a, 1 - single i j a,
    by simp [add_mul, mul_sub, single_mul_single_of_ne _ _ _ _ h.symm],
    by simp [sub_mul, mul_add, single_mul_single_of_ne _ _ _ _ h.symm]⟩

private theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b
      = (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  rw [← map_inv]
  simp only [Units.val_mul, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq]
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem res_zero (x : 𝒪[k]) : IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

private theorem pm_KO (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  show algebraMap 𝒪[k] k ((pm 𝒪[k] n w : Matrix (Fin n) (Fin n) 𝒪[k]) a b) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem conj_mem {C : Subgroup 𝓀[k]ˣ} {i j : Fin n} (hij : (j : ℕ) = i + 1) {g : GL (Fin n) k}
    (hg : g ∈ iwC k n C) :
    (pm k n (Equiv.swap i j))⁻¹ * g * pm k n (Equiv.swap i j) ∈ iwC k n C ↔
      valuation k ((g : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  have hm := (memIwC k n C).1
  obtain ⟨h1, h2⟩ := (hm g).1 hg
  obtain ⟨h3, h4⟩ := mem_iwahori.1 h1
  have hlt : i < j := by rw [Fin.lt_def]; omega
  constructor
  · intro h
    have := (mem_iwahori.1 ((hm _).1 h).1).2 j i hlt
    rwa [conj_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at this
  · intro h
    refine (hm _).2 ⟨mem_iwahori.2 ⟨mul_mem (mul_mem (inv_mem (pm_KO _)) h3) (pm_KO _), fun a b hab => ?_⟩,
      fun a => ?_⟩
    · rw [conj_apply]
      by_cases hc : a = j ∧ b = i
      · rwa [hc.1, hc.2, Equiv.swap_apply_left, Equiv.swap_apply_right]
      · apply h4
        simp only [Equiv.swap_apply_def]
        simp only [Fin.ext_iff, Fin.lt_def] at *
        split_ifs <;> omega
    · rw [conj_apply]
      exact h2 _

private theorem pick {C : Subgroup 𝓀[k]ˣ} {g : GL (Fin n) k} (hg : g ∈ iwC k n C)
    {r : 𝓀[k] → 𝒪[k]} (hr : ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) (a i j : Fin n) :
    ∃ c, valuation k ((g : Matrix (Fin n) (Fin n) k) i j
      - algebraMap 𝒪[k] k (r c) * (g : Matrix (Fin n) (Fin n) k) a a) < 1 := by
  obtain ⟨h1, h2⟩ := ((memIwC k n C).1 g).1 hg
  obtain ⟨_, ⟨u, -, rfl⟩, hu⟩ := h2 a
  obtain ⟨h, rfl⟩ := (mem_iwahori.1 h1).1
  refine ⟨IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ)), ?_⟩
  rw [← hu]
  have := (res_zero ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j -
    r (IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i j * (u⁻¹ : 𝒪[k]ˣ))) * (u : 𝒪[k]))).1 (by
      rw [map_sub, map_mul, hr, ← map_mul, Units.inv_mul_cancel_right, sub_self])
  rw [map_sub, map_mul] at this
  exact this

private theorem elem_mem {i j : Fin n} (h : i < j) (a : 𝒪[k]) :
    elem h.ne (algebraMap 𝒪[k] k a) ∈ unipO k n := by
  refine ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b _ _ hab => ?_, fun a _ _ => ?_⟩, elem h.ne a, ?_⟩
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a b = 0
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hab h.asymm
    simp [one_apply_ne hab.ne', single_apply, this]
  · show (1 + single i j _ : Matrix (Fin n) (Fin n) k) a a = _
    have : ¬ (i = a ∧ j = a) := by
      rintro ⟨rfl, rfl⟩
      exact h.ne rfl
    simp [single_apply, this]
  · ext p q
    show algebraMap 𝒪[k] k ((1 + single i j a : Matrix (Fin n) (Fin n) 𝒪[k]) p q) =
      (1 + single i j _ : Matrix (Fin n) (Fin n) k) p q
    simp only [Matrix.add_apply, Matrix.one_apply, single_apply, map_add (f := _)]
    split_ifs <;> simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.simpleOrbit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (i j : Fin n), (j : ℕ) = i + 1 → ∀ (r : 𝓀[k] → 𝒪[k]), (∀ c, IsLocalRing.residue 𝒪[k] (r c) = c) → ∃ x : 𝓀[k] → GL (Fin n) k, (∀ c, (x c : Matrix (Fin n) (Fin n) k) = 1 + Matrix.single i j (algebraMap 𝒪[k] k (r c))) ∧ (∀ c, x c ∈ unipO k n) ∧ (∀ q : GL (Fin n) k ⧸ iwC k n C, q ∈ MulAction.orbit (iwC k n C) ((pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) ↔ ∃! c, ((x c * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = q) ∧ ∀ g ∈ iwC k n C, ∃ c, ∃ b ∈ iwC k n C, pm k n (Equiv.swap i j) * g = b * (pm k n (Equiv.swap i j) * x c) := by
  intro k _ _ _ _ n C i j hij r hr
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have hle : unipO k n ≤ iwC k n C := le_sup_of_le_left le_sup_right
  have hx : ∀ c, elem hlt.ne (algebraMap 𝒪[k] k (r c)) ∈ iwC k n C := fun c => hle (elem_mem hlt _)
  have hL : ∀ (a : k) (g : GL (Fin n) k), (((elem hlt.ne a)⁻¹ * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) j j := by
    intro a g
    show ((1 - single i j a) * (g : Matrix (Fin n) (Fin n) k)) i j = _
    simp [sub_mul]
  have hR : ∀ (a : k) (g : GL (Fin n) k), ((g * (elem hlt.ne a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (g : Matrix (Fin n) (Fin n) k) i j - a * (g : Matrix (Fin n) (Fin n) k) i i := by
    intro a g
    show ((g : Matrix (Fin n) (Fin n) k) * (1 - single i j a)) i j = _
    simp [mul_sub, mul_comm]
  have hs : (pm k n (Equiv.swap i j))⁻¹ = pm k n (Equiv.swap i j) := by rw [← map_inv, Equiv.swap_inv]
  refine ⟨fun c => elem hlt.ne (algebraMap 𝒪[k] k (r c)), fun c => rfl, fun c => elem_mem hlt _, fun q => ?_,
    fun g hg => ?_⟩
  · constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨c, hc⟩ := pick hg hr j i j
      have h1 : ((elem hlt.ne (algebraMap 𝒪[k] k (r c)) * pm k n (Equiv.swap i j) : GL (Fin n) k) :
          GL (Fin n) k ⧸ iwC k n C) = ((g * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) := by
        rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ g, ← mul_assoc]
        exact (conj_mem hij (mul_mem (inv_mem (hx c)) hg)).2 (by rwa [hL])
      refine ⟨c, h1, fun d hd => ?_⟩
      have h2 := h1.trans (Eq.symm hd)
      rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, ← mul_assoc _ (elem _ _), ← mul_assoc,
        conj_mem hij (mul_mem (inv_mem (hx c)) (hx d)), hL] at h2
      have h3 : valuation k (algebraMap 𝒪[k] k (r d - r c)) < 1 := by
        convert h2 using 2
        simp [elem, one_apply_ne hlt.ne, single_apply, hlt.ne]
      have h4 := (res_zero _).2 h3
      rwa [map_sub, hr, hr, sub_eq_zero] at h4
    · rintro ⟨c, rfl, -⟩
      exact ⟨⟨_, hx c⟩, rfl⟩
  · obtain ⟨c, hc⟩ := pick hg hr i i j
    refine ⟨c, _, (conj_mem hij (mul_mem hg (inv_mem (hx c)))).2 (by rwa [hR]), ?_⟩
    rw [mul_assoc, ← mul_assoc (pm k n _) (pm k n _), ← map_mul, Equiv.swap_mul_self, map_one, one_mul, hs,
      mul_assoc, inv_mul_cancel_right]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkTrace
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem double_coset_operator_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (K K' : Subgroup G) (x : G) (h : (MulAction.orbit K (x : G ⧸ K')).Finite) (v : fixd ρ K') :
    (hk2 ρ K K' x v : M) = ∑ q ∈ Set.Finite.toFinset h, ρ q.out v := by
  rw [(hkApply A G M ρ K K' x h).1 v, dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ K' => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ h,
    LinearMap.sum_apply]

private theorem mem_orb {G : Type} [Group G] (K K' : Subgroup G) (x g : G) :
    (g : G ⧸ K') ∈ MulAction.orbit K (x : G ⧸ K') ↔ ∃ a ∈ K, ∃ b ∈ K', g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ K') = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ K') = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

theorem UpperTheory.V.AlgebraTools.hkTrace :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I K : Subgroup G) (h : I ≤ K) (ι : Type) [Fintype ι] (w : ι → G), HeckePair I → (∀ i, w i ∈ K) → (∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) → FinOrb K I 1 ∧ ∑ i, hk ρ I (w i) = inc ρ h ∘ₗ trc ρ K I ∧ ∀ v : fixd ρ K, trc ρ K I (inc ρ h v) = (I.relIndex K : A) • v := by
  intro A G M _ _ _ _ ρ I K h ι _ w hI hw hu
  classical
  replace hI : ∀ x : G, (MulAction.orbit I (x : G ⧸ I)).Finite := hI
  have hK : ∀ g : G, (g : G ⧸ I) ∈ MulAction.orbit K ((1 : G) : G ⧸ I) ↔ g ∈ K := fun g => by
    rw [mem_orb]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem ha (one_mem _)) (h hb),
      fun hg => ⟨g, hg, 1, one_mem _, by simp⟩⟩
  have hU : MulAction.orbit K ((1 : G) : G ⧸ I) = ⋃ i, MulAction.orbit I (w i : G ⧸ I) := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [Set.mem_iUnion, hK, mem_orb]
    exact ⟨fun hg => (hu g hg).exists,
      fun ⟨i, a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem (h ha) (hw i)) (h hb)⟩
  have hF : (MulAction.orbit K ((1 : G) : G ⧸ I)).Finite := by
    rw [hU]
    exact Set.finite_iUnion fun i => hI (w i)
  refine ⟨hF, ?_, fun v => ?_⟩
  · ext v
    change _ = (hk2 ρ K I 1 v : M)
    rw [LinearMap.sum_apply, Submodule.coe_sum, double_coset_operator_sum ρ K I 1 hF]
    have e : Set.Finite.toFinset hF = Finset.univ.biUnion fun i => Set.Finite.toFinset (hI (w i)) := by
      ext q
      simp [hU]
    rw [e, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun i _ => double_coset_operator_sum ρ I I (w i) (hI _) v
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro q hi hj
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [Set.Finite.mem_toFinset] at hi hj
      have hg : g ∈ K := (hK g).1 (hU ▸ Set.mem_iUnion.2 ⟨i, hi⟩)
      exact hij ((hu g hg).unique ((mem_orb _ _ _ _).1 hi) ((mem_orb _ _ _ _).1 hj))
  · ext
    change (hk2 ρ K I 1 (inc ρ h v) : M) = _
    rw [double_coset_operator_sum ρ K I 1 hF, Finset.sum_congr rfl (g := fun _ => (v : M))]
    · have hs : MulAction.stabilizer K ((1 : G) : G ⧸ I) = I.subgroupOf K := by
        ext k
        rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
        change (((k : G) * 1 : G) : G ⧸ I) = _ ↔ _
        rw [eq_comm, QuotientGroup.eq]
        simp
      rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hF, ← MulAction.index_stabilizer, hs,
        Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
      rfl
    · intro q hq
      rw [Set.Finite.mem_toFinset, ← q.out_eq'] at hq
      exact v.2 _ ((hK _).1 hq)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplSpec
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.exists_prime_over :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      (∀ q : Ideal R, q.IsPrime → q ≤ p → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap (algebraMap R B) = q) ∧
      (∀ a : R, algebraMap R B a = 0 → ∃ s : R, s ∉ p ∧ s * a = 0) := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI := IsCplAt.flat R p B h
  refine ⟨fun q hq hqp => ?_, fun a ha => ?_⟩
  · haveI := hq
    haveI : (maximalIdeal B).LiesOver p := ⟨h.comap_eq.symm⟩
    obtain ⟨P, -, hP, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal B) hqp
    exact ⟨P, hP, hlo.over.symm⟩
  · let Rp := Localization.AtPrime p
    haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
    have hmem : ∀ n : ℕ, algebraMap R Rp a ∈ (maximalIdeal Rp) ^ n := by
      intro n
      obtain ⟨s, hs, hsa⟩ := h.strict n a (by rw [ha]; exact zero_mem _)
      have hu : IsUnit (algebraMap R Rp s) := IsLocalization.map_units Rp (⟨s, hs⟩ : p.primeCompl)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      have := Ideal.mem_map_of_mem (algebraMap R Rp) hsa
      rw [map_mul] at this
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal Rp) (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top
    have h0 : algebraMap R Rp a = 0 := by
      have : algebraMap R Rp a ∈ ⨅ i, (maximalIdeal Rp) ^ i := Ideal.mem_iInf.mpr hmem
      rw [hbot] at this
      exact (Ideal.mem_bot).mp this
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rp a).mp h0
    exact ⟨s, hs, hsa⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkMul
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hkMul_out {G : Type} [Group G] (I : Subgroup G) (g : G) :
    ∃ i ∈ I, (g : G ⧸ I).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I g
  exact ⟨h, h.2, hh⟩

private theorem hkMul_mem {G : Type} [Group G] (I : Subgroup G) (x : G) (p : G ⧸ I) :
    p ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, p = ((a * x : G) : G ⧸ I) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem UpperTheory.V.AlgebraTools.hkMul :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (x y : G), HeckePair I → (∀ b ∈ I, ∃ a ∈ I, ∃ c ∈ I, x * b * y = a * (x * y) * c) → (MulAction.orbit I ((x * y : G) : G ⧸ I)).ncard = (MulAction.orbit I (x : G ⧸ I)).ncard * (MulAction.orbit I (y : G ⧸ I)).ncard → hk ρ I x * hk ρ I y = hk ρ I (x * y) := by
  intro A G M _ _ _ _ ρ I x y hI hb hc
  classical
  haveI fx : Fintype (MulAction.orbit I (x : G ⧸ I)) := (hI x).fintype
  haveI fy : Fintype (MulAction.orbit I (y : G ⧸ I)) := (hI y).fintype
  haveI fxy : Fintype (MulAction.orbit I ((x * y : G) : G ⧸ I)) := (hI (x * y)).fintype
  have hmem : ∀ (p : MulAction.orbit I (x : G ⧸ I)) (q : MulAction.orbit I (y : G ⧸ I)),
      (((p : G ⧸ I).out * (q : G ⧸ I).out : G) : G ⧸ I) ∈ MulAction.orbit I ((x * y : G) : G ⧸ I) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I x p).1 hp
    obtain ⟨b, hb', rfl⟩ := (hkMul_mem I y q).1 hq
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (b * y)
    obtain ⟨a', ha', c, hc', e3⟩ := hb (i * b) (mul_mem hi hb')
    refine (hkMul_mem I _ _).2 ⟨a * a', mul_mem ha ha', ?_⟩
    simp only [e1, e2]
    have : a * x * i * (b * y * j) = a * a' * (x * y) * (c * j) := by
      calc a * x * i * (b * y * j) = a * (x * (i * b) * y) * j := by group
        _ = _ := by rw [e3]; group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem hc' hj)
  let f : MulAction.orbit I (x : G ⧸ I) × MulAction.orbit I (y : G ⧸ I) →
      MulAction.orbit I ((x * y : G) : G ⧸ I) := fun pq => ⟨_, hmem pq.1 pq.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, rfl⟩ := (hkMul_mem I _ r).1 hr
    obtain ⟨i, hi, e1⟩ := hkMul_out I (a * x)
    obtain ⟨j, hj, e2⟩ := hkMul_out I (i⁻¹ * y)
    refine ⟨(⟨_, (hkMul_mem I _ _).2 ⟨a, ha, rfl⟩⟩, ⟨_, (hkMul_mem I _ _).2 ⟨i⁻¹, inv_mem hi, rfl⟩⟩), Subtype.ext ?_⟩
    simp only [f, e1, e2]
    have : a * x * i * (i⁻¹ * y * j) = a * (x * y) * j := by group
    rw [this]
    exact QuotientGroup.mk_mul_of_mem _ hj
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, ?_⟩
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hc]
  refine LinearMap.ext fun v => Subtype.ext ?_
  have h1 := (hkApply A G M ρ I I x (hI x)).1
  have h2 := (hkApply A G M ρ I I y (hI y)).1
  have h3 := (hkApply A G M ρ I I (x * y) (hI _)).1
  rw [Module.End.mul_apply]
  unfold hk
  rw [h1, h2, h3]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  rw [← hbij.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨i, hi, e⟩ := hkMul_out I ((p : G ⧸ I).out * (q : G ⧸ I).out)
  simp only [f, e, map_mul, Module.End.mul_apply]
  rw [v.2 i hi]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFundNorm
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unif_lt {x : kˣ} (hx : IsUnif x) (y : k) :
    valuation k y < 1 ↔ valuation k y ≤ valuation k (x : k) := by
  obtain ⟨p, hp, e⟩ := hx
  have hI := Valuation.integer.integers (valuation k)
  have h1 : valuation k (x : k) < 1 := by
    rw [← e]
    refine lt_of_le_of_ne p.2 fun h => hp.not_isUnit (hI.isUnit_iff_valuation_eq_one.2 h)
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  let z : 𝒪[k] := ⟨y, h.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] := fun hu => h.ne (hI.isUnit_iff_valuation_eq_one.1 hu)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  rw [← e]
  exact hI.le_of_dvd hz

private def Bd (x : kˣ) (g : GL (Fin n) k) : Prop :=
  ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (x : k) ^ (if j < i then 1 else 0 : ℤ)

private theorem mem_iw_iff {x : kˣ} (hx : IsUnif x) (g : GL (Fin n) k) :
    g ∈ iwahori k (Fin n) ↔ Bd x g ∧ Bd x g⁻¹ := by
  have h1 : valuation k (x : k) ≤ 1 := ((unif_lt hx x).2 le_rfl).le
  have A : ∀ g ∈ iwahori k (Fin n), Bd x g := by
    intro g hg i j
    have hg' := mem_iwahori.1 hg
    split_ifs with h
    · simpa using (unif_lt hx _).1 (hg'.2 i j h)
    · rw [zpow_zero]
      exact ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg'.1).1 i j
  have B : ∀ g : GL (Fin n) k, Bd x g → ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have := hg i j
    split_ifs at this with h
    · exact le_trans (by simpa using this) h1
    · simpa using this
  refine ⟨fun hg => ⟨A g hg, A _ (inv_mem hg)⟩, fun ⟨ha, hb⟩ => mem_iwahori.2
    ⟨(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨B _ ha, B _ hb⟩, fun i j h => (unif_lt hx _).2 ?_⟩⟩
  simpa [h] using ha i j

private theorem conj_entry (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (w i) (w j) =
      (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
  have e : pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ =
      pm k n w * (pw x a * g * diagT k (Fin n) (fun i => x ^ a i)⁻¹) * pm k n w⁻¹ := by
    rw [map_inv, map_inv, pw]; group
  rw [e]
  simp only [Units.val_mul, pw, val_diagT]
  generalize hM : (diagonal (fun i => ((x ^ a i : kˣ) : k)) * (g : Matrix (Fin n) (Fin n) k) *
    diagonal fun i => (((fun i => x ^ a i)⁻¹ i : kˣ) : k)) = M
  have hM' : M i j = (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
    rw [← hM, mul_diagonal, diagonal_mul, zpow_sub₀ x.ne_zero]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    ring
  rw [← hM']
  simp only [Matrix.mul_apply, pm_apply]
  simp

private theorem bd_conj (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) (g : GL (Fin n) k) :
    Bd x (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹) ↔ Bd x g := by
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
  unfold Bd
  rw [w.surjective.forall₂]
  refine forall₂_congr fun i j => ?_
  rw [conj_entry, hw, map_mul, map_zpow₀, zpow_add₀ h0.ne', mul_le_mul_iff_right₀ (zpow_pos h0 _)]

private theorem exists_rot (n m : ℕ) (hm : m ≤ n) : ∃ w : Equiv.Perm (Fin n),
    ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (fund n m i - fund n m j) + (if j < i then 1 else 0) := by
  let f : Fin n → Fin n := fun i => ⟨if (i : ℕ) < m then n - m + i else i - m, by
    have := i.2; split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Fin.val h
    have := i.2; have := j.2
    simp only [f] at h'
    ext
    split_ifs at h' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i j => ?_⟩
  have := i.2; have := j.2
  simp only [Equiv.ofBijective_apply, f, fund, Fin.lt_def]
  split_ifs <;> omega

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.fundNorm :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (x : kˣ), IsUnif x → ∀ m ≤ n, ∃ w : Equiv.Perm (Fin n), pm k n w * pw x (fund n m) ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n C x hx m hm
  obtain ⟨w, hw⟩ := exists_rot n m hm
  refine ⟨w, Subgroup.mem_normalizer_iff.2 fun g => ?_⟩
  have e : (pm k n w * pw x (fund n m) * g * (pm k n w * pw x (fund n m))⁻¹)⁻¹ =
      pm k n w * pw x (fund n m) * g⁻¹ * (pm k n w * pw x (fund n m))⁻¹ := by group
  rw [(memIwC k n C).1, (memIwC k n C).1, mem_iw_iff hx, mem_iw_iff hx, e, bd_conj x _ w hw, bd_conj x _ w hw]
  refine and_congr Iff.rfl ?_
  conv_rhs => rw [w.surjective.forall]
  simp only [conj_entry, sub_self, zpow_zero, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplQuot
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem prec_of_surj {B C : Type} [CommRing B] [CommRing C] (g : B →+* C)
    (I : Ideal B) [hB : IsPrecomplete I B] (hg : Function.Surjective g) :
    IsPrecomplete (I.map g) C := by
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  have h1 : ∀ n, ∃ d ∈ I ^ n, g d = f (n + 1) - f n := by
    intro n
    have := (((I.map g) ^ n).neg_mem (hf (Nat.le_succ n)))
    rw [neg_sub, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective g hg] at this
    exact this
  choose d hd hgd using h1
  obtain ⟨b0, hb0⟩ := hg (f 0)
  let u : ℕ → B := fun n => b0 + ∑ i ∈ Finset.range n, d i
  have hu : ∀ n, g (u n) = f n := by
    intro n
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, map_add (f := _), map_sum, hgd, hb0, Finset.sum_range_sub]
    ring
  have hc : ∀ {m n}, m ≤ n → u m ≡ u n [SMOD (I ^ m • ⊤ : Submodule B B)] := by
    intro m n hmn
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have e : u m - u (k + 1) = (u m - u k) - d k := by
        simp only [u, Finset.sum_range_succ]; ring
      rw [e]
      exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hk (hd k))
  obtain ⟨L, hL⟩ := hB.prec hc
  refine ⟨g L, fun n => ?_⟩
  have := hL n
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← hu, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ this

private theorem approx_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (I : Ideal R) (n : ℕ) (x : B)
    (hx : x ∈ I.map (algebraMap R B)) :
    ∃ i ∈ I, ∃ s : R, s ∉ p ∧ algebraMap R B s * x - algebraMap R B i ∈ maximalIdeal B ^ n := by
  have hp := h.isPrime
  have h1 : (1 : R) ∉ p := (Ideal.ne_top_iff_one _).1 hp.ne_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, 1, h1, by simp⟩
  | zero => exact ⟨0, I.zero_mem, 1, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨j, hj, t, ht, hy⟩ := hy
    refine ⟨t * i + s * j, I.add_mem (I.mul_mem_left _ hi) (I.mul_mem_left _ hj), s * t,
      fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t) hx)
      (Ideal.mul_mem_left _ (algebraMap R B s) hy)
    convert this using 1
    simp only [map_add (f := _), map_mul]; ring
  | smul b x _ hx =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨a, t, ht, hb⟩ := h.dense n b
    refine ⟨a * i, I.mul_mem_left _ hi, s * t, fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t * b) hx)
      (Ideal.mul_mem_left _ (algebraMap R B i) hb)
    convert this using 1
    simp only [map_mul, smul_eq_mul]; ring

theorem UpperTheory.V.AlgebraTools.IsCplAt.quotient :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (S : Type) [CommRing S] [Algebra R S] (q : Ideal S) (C : Type) [CommRing C] [IsLocalRing C]
      [Algebra S C] [Algebra B C] [Algebra R C] [IsScalarTower R S C] [IsScalarTower R B C],
      IsCplAt R p B → Function.Surjective (algebraMap R S) → q.comap (algebraMap R S) = p →
      Function.Surjective (algebraMap B C) →
      RingHom.ker (algebraMap B C) = (RingHom.ker (algebraMap R S)).map (algebraMap R B) → IsCplAt S q C := by
  intro R _ _ p B _ _ _ S _ _ q C _ _ _ _ _ _ _ h hRS hq hBC hker
  haveI := h.noeth
  haveI := h.complete
  have hp := h.isPrime
  have hN : IsNoetherianRing C := isNoetherianRing_of_surjective B C (algebraMap B C) hBC
  haveI hloc : IsLocalHom (algebraMap B C) := IsLocalHom.of_surjective _ hBC
  have hm : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hBC
  have hsq : ∀ r : R, algebraMap S C (algebraMap R S r) = algebraMap B C (algebraMap R B r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hqp : ∀ r : R, algebraMap R S r ∈ q ↔ r ∈ p := by
    intro r; rw [← hq, Ideal.mem_comap]
  have hpre : IsPrecomplete (maximalIdeal C) C := hm ▸ prec_of_surj (algebraMap B C) _ hBC
  refine ⟨hN, {}, ?_, ?_, ?_⟩
  · ext x
    obtain ⟨r, rfl⟩ := hRS x
    rw [hqp, ← h.comap_eq, Ideal.mem_comap, Ideal.mem_comap, hsq, mem_maximalIdeal,
      mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
  · intro n c
    obtain ⟨b, rfl⟩ := hBC c
    obtain ⟨a, s, hs, hab⟩ := h.dense n b
    refine ⟨algebraMap R S a, algebraMap R S s, fun hh => hs ((hqp s).1 hh), ?_⟩
    rw [hsq, hsq, ← map_mul, ← map_sub, ← hm, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hab
  · intro n x hx
    obtain ⟨a, rfl⟩ := hRS x
    rw [hsq, ← hm, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hBC] at hx
    obtain ⟨y, hy, hya⟩ := hx
    have hk : algebraMap R B a - y ∈ RingHom.ker (algebraMap B C) := by
      rw [RingHom.mem_ker, map_sub, hya, sub_self]
    rw [hker] at hk
    obtain ⟨i, hi, s, hs, hsi⟩ := approx_map h _ n _ hk
    have h2 : algebraMap R B (s * a - i) ∈ maximalIdeal B ^ n := by
      have := Ideal.add_mem _ hsi (Ideal.mul_mem_left _ (algebraMap R B s) hy)
      convert this using 1
      simp only [map_sub, map_mul]; ring
    obtain ⟨t, ht, hta⟩ := h.strict n _ h2
    refine ⟨algebraMap R S (t * s), fun hh => (hp.mem_or_mem ((hqp _).1 hh)).elim ht hs, ?_⟩
    have h3 : algebraMap R S (t * (s * a - i)) ∈ q ^ n := by
      have := Ideal.mem_map_of_mem (algebraMap R S) hta
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ n this
      rw [Ideal.map_le_iff_le_comap, hq]
    rw [RingHom.mem_ker] at hi
    convert h3 using 1
    simp only [map_sub, map_mul, hi]; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkEv
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

private theorem hkEv_coe (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x : G)
    (v : fixd ρ I) : (hk ρ I x v : M) = dc ρ I I x v := by
  have h := (UpperTheory.V.Hi.dcSum A G M ρ I I x (hI x)).2.1
  unfold hk hk2
  rw [dite_eq_left h]
  rfl

private noncomputable def hkEv_phi (ρ : Representation A G M) (I : Subgroup G) (m : M) :
    MonoidAlgebra A (G ⧸ I) →ₗ[A] M :=
  Finsupp.linearCombination A (fun q : G ⧸ I => ρ q.out m) ∘ₗ (MonoidAlgebra.coeffLinearEquiv A).toLinearMap

private theorem hkEv_phi_single (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (g : G) (c : A) :
    hkEv_phi ρ I m (MonoidAlgebra.single (g : G ⧸ I) c) = c • ρ g m := by
  have h1 : g⁻¹ * (g : G ⧸ I).out ∈ I := QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  have h2 : ρ (g⁻¹ * (g : G ⧸ I).out) m = m := m.2 _ h1
  have h3 : ρ (g : G ⧸ I).out m = ρ g m := by
    calc ρ (g : G ⧸ I).out m = ρ (g * (g⁻¹ * (g : G ⧸ I).out)) m := by rw [mul_inv_cancel_left]
      _ = ρ g (ρ (g⁻¹ * (g : G ⧸ I).out) m) := by rw [map_mul ρ g]; rfl
      _ = ρ g m := by rw [h2]
  rw [← h3]
  simp [hkEv_phi]

private theorem hkEv_phi_equiv (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (h : G)
    (a : MonoidAlgebra A (G ⧸ I)) : hkEv_phi ρ I m (permRep A I h a) = ρ h (hkEv_phi ρ I m a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single q c =>
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Representation.ofMulAction_single]
    have : h • (g : G ⧸ I) = ((h * g : G) : G ⧸ I) := rfl
    rw [this, hkEv_phi_single, hkEv_phi_single, map_smul, map_mul]
    rfl

private noncomputable def hkEv_psi (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    fixd (permRep A I) I →ₗ[A] fixd ρ I :=
  (hkEv_phi ρ I m).restrict (fun a ha u hu => by rw [← hkEv_phi_equiv, ha u hu])

private theorem hkEv_psi_hk (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (m : fixd ρ I)
    (x : G) (a : fixd (permRep A I) I) :
    hkEv_psi ρ I m (hk (permRep A I) I x a) = hk ρ I x (hkEv_psi ρ I m a) := by
  apply Subtype.ext
  rw [hkEv_coe ρ I hI]
  change hkEv_phi ρ I m (hk (permRep A I) I x a : MonoidAlgebra A (G ⧸ I)) = dc ρ I I x (hkEv_phi ρ I m a)
  rw [hkEv_coe _ I hI]
  exact (UpperTheory.V.Hi.dcSum A G _ (permRep A I) I I x (hI x)).2.2.2 A M ρ
    (hkEv_phi ρ I m).toAddMonoidHom (hkEv_phi_equiv ρ I m) a

private theorem hkEv_psi_surj (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    ∃ a, hkEv_psi ρ I m a = m := by
  refine ⟨⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => ?_⟩, Subtype.ext ?_⟩
  · rw [Representation.ofMulAction_single]
    congr 1
    change ((u * 1 : G) : G ⧸ I) = _
    exact QuotientGroup.eq.mpr (by simpa using hu)
  · change hkEv_phi ρ I m (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = m
    rw [hkEv_phi_single]
    simp

private def hkEv_R (ρ : Representation A G M) (I : Subgroup G)
    (T : Module.End A (fixd (permRep A I) I)) (E : Module.End A (fixd ρ I)) : Prop :=
  ∀ m a, hkEv_psi ρ I m (T a) = E (hkEv_psi ρ I m a)

private theorem hkEv_uniq {ρ : Representation A G M} {I : Subgroup G}
    {T : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T E') : E = E' := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨a, ha⟩ := hkEv_psi_surj ρ I m
  rw [← ha, ← h, ← h']

private theorem hkEv_alg (ρ : Representation A G M) (I : Subgroup G) (c : A) :
    hkEv_R ρ I (algebraMap A _ c) (algebraMap A _ c) := fun m a => by
  simp only [Module.algebraMap_end_apply, map_smul]

private theorem hkEv_add {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T + T') (E + E') := fun m a => by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), h, h']

private theorem hkEv_mul {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T * T') (E * E') := fun m a => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h, h']

private theorem hkEv_ex (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (T : HkAlg A I) :
    ∃ E, hkEv_R ρ I T.1 E := by
  obtain ⟨T, hT⟩ := T
  induction hT using Algebra.adjoin_induction with
  | mem T h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨hk ρ I x, fun m a => hkEv_psi_hk ρ I hI m x a⟩
  | algebraMap c => exact ⟨_, hkEv_alg ρ I c⟩
  | add T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_add h h'⟩
  | mul T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_mul h h'⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.hkEv :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G), HeckePair I → ∃ ev : HkAlg A I →ₐ[A] Module.End A (fixd ρ I), ∀ x : G, ev (hT A I x) = hk ρ I x := by
  intro A G M _ _ _ _ ρ I hI
  choose f hf using hkEv_ex ρ I hI
  have halg : ∀ c : A, f (algebraMap A _ c) = algebraMap A _ c := fun c =>
    hkEv_uniq (hf _) (hkEv_alg ρ I c)
  refine ⟨{ toFun := f
            map_one' := by simpa using halg 1
            map_mul' := fun T T' => hkEv_uniq (hf _) (hkEv_mul (hf T) (hf T'))
            map_zero' := by simpa using halg 0
            map_add' := fun T T' => hkEv_uniq (hf _) (hkEv_add (hf T) (hf T'))
            commutes' := halg }, fun x => ?_⟩
  exact hkEv_uniq (hf _) (fun m a => hkEv_psi_hk ρ I hI m x a)
end
