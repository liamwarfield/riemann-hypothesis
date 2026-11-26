module

public import GroundTheory.PAdicHodge.CyclotomicTower

@[expose] public section

section -- merged from GroundTheory.PAdicHodge.TateNormalizedTrace
section -- merged from GroundTheory.PAdicHodge.NormalizedTraceTower
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial Module

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def cyclotomicLayer (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ cycl p n

def cyclotomicLimit : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n, cyclotomicLayer K n

theorem cyclotomicLayer_mono : Monotone (cyclotomicLayer K) := fun _ _ h =>
  sup_le_sup_left (cycl_mono h) K

theorem le_cyclotomicLayer (n : ℕ) : K ≤ cyclotomicLayer K n := le_sup_left

theorem cycl_le_cyclotomicLayer (n : ℕ) : cycl p n ≤ cyclotomicLayer K n := le_sup_right

theorem cyclotomicLayer_le_cyclotomicLimit (n : ℕ) : cyclotomicLayer K n ≤ cyclotomicLimit K :=
  le_iSup (cyclotomicLayer K) n

theorem mem_cyclotomicLimit {x : PadicAlgCl p} :
    x ∈ cyclotomicLimit K ↔ ∃ n, x ∈ cyclotomicLayer K n := by
  rw [← SetLike.mem_coe, cyclotomicLimit,
    coe_iSup_of_directed (cyclotomicLayer_mono K).directed_le, Set.mem_iUnion]
  rfl

theorem cyclotomicLayer_sup_cycl {n m : ℕ} (h : n ≤ m) :
    cyclotomicLayer K n ⊔ cycl p m = cyclotomicLayer K m := by
  rw [cyclotomicLayer, cyclotomicLayer, sup_assoc, sup_eq_right.2 (cycl_mono h)]

instance charZero_intermediateField (k : IntermediateField ℚ_[p] (PadicAlgCl p)) : CharZero k :=
  (algebraMap k (PadicAlgCl p)).charZero

variable [FiniteDimensional ℚ_[p] K]

instance finiteDimensional_cyclotomicLayer (n : ℕ) :
    FiniteDimensional ℚ_[p] (cyclotomicLayer K n) := by
  unfold cyclotomicLayer; infer_instance

def relDeg (n : ℕ) : ℕ := finrank (cycl p n) (extendScalars (cycl_le_cyclotomicLayer K n))

theorem finrank_cyclotomicLayer (n : ℕ) :
    finrank ℚ_[p] (cyclotomicLayer K n) = finrank ℚ_[p] (cycl p n) * relDeg K n :=
  finrank_eq_mul_finrank_extendScalars (cycl_le_cyclotomicLayer K n)

theorem relDeg_antitone : Antitone (relDeg K) := by
  intro n m h
  have c := finrank_sup_mul_le (k := cycl p n) (X := cyclotomicLayer K n) (Y := cycl p m)
    (cycl_le_cyclotomicLayer K n) (cycl_mono h)
  rw [cyclotomicLayer_sup_cycl K h, finrank_cyclotomicLayer, finrank_cyclotomicLayer] at c
  have pn : 0 < finrank ℚ_[p] (cycl p n) := Module.finrank_pos
  have pm : 0 < finrank ℚ_[p] (cycl p m) := Module.finrank_pos
  have : finrank ℚ_[p] (cycl p m) * finrank ℚ_[p] (cycl p n) * relDeg K m ≤
      finrank ℚ_[p] (cycl p m) * finrank ℚ_[p] (cycl p n) * relDeg K n := by
    calc _ = finrank ℚ_[p] (cycl p m) * relDeg K m * finrank ℚ_[p] (cycl p n) := by ring
      _ ≤ _ := c
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos pm pn)

theorem exists_relDeg_stable : ∃ N, 2 ≤ N ∧ ∀ m, N ≤ m → relDeg K m = relDeg K N := by
  classical
  have hex : ∃ v, ∃ n, relDeg K n = v := ⟨_, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec hex
  have hmin : ∀ m, relDeg K n₀ ≤ relDeg K m := fun m => hn₀ ▸ Nat.find_min' hex ⟨m, rfl⟩
  refine ⟨max n₀ 2, le_max_right _ _, fun m hm => le_antisymm (relDeg_antitone K hm) ?_⟩
  exact (relDeg_antitone K (le_max_left n₀ 2)).trans (hmin m)

def stableIndex : ℕ := Classical.choose (exists_relDeg_stable K)

theorem two_le_stableIndex : 2 ≤ stableIndex K := (Classical.choose_spec (exists_relDeg_stable K)).1

theorem relDeg_eq_of_le {m : ℕ} (h : stableIndex K ≤ m) : relDeg K m = relDeg K (stableIndex K) :=
  (Classical.choose_spec (exists_relDeg_stable K)).2 m h

theorem finrank_linearDisjoint {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) :
    finrank ℚ_[p] (cyclotomicLayer K m) * finrank ℚ_[p] (cycl p n) =
      finrank ℚ_[p] (cyclotomicLayer K n) * finrank ℚ_[p] (cycl p m) := by
  rw [finrank_cyclotomicLayer, finrank_cyclotomicLayer, relDeg_eq_of_le K hn,
    relDeg_eq_of_le K (hn.trans hnm)]
  ring

theorem normTrace_cycl_eq_of_mem {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m)
    {z : PadicAlgCl p} (hz : z ∈ cyclotomicLayer K n) :
    normTrace (cycl p m) z = normTrace (cycl p n) z := by
  refine normTrace_eq_of_finrank_sup (cycl_le_cyclotomicLayer K n) (cycl_mono hnm) ?_ hz
  rw [cyclotomicLayer_sup_cycl K hnm]
  exact finrank_linearDisjoint K hn hnm

theorem normTrace_cyclotomicLayer_eq_of_mem {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m)
    {a : PadicAlgCl p} (ha : a ∈ cycl p m) :
    normTrace (cyclotomicLayer K n) a = normTrace (cycl p n) a := by
  refine normTrace_eq_of_finrank_sup (cycl_mono hnm) (cycl_le_cyclotomicLayer K n) ?_ ha
  rw [sup_comm, cyclotomicLayer_sup_cycl K hnm, finrank_linearDisjoint K hn hnm]
  ring

theorem finiteDimensional_extendScalars {k E : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : k ≤ E)
    [FiniteDimensional ℚ_[p] E] : FiniteDimensional k (extendScalars h) := by
  apply Module.finite_of_finrank_pos
  have hE : 0 < finrank ℚ_[p] E := Module.finrank_pos
  rw [finrank_eq_mul_finrank_extendScalars h] at hE
  exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hE

instance finiteDimensional_cyclotomicLayer_cycl (n : ℕ) :
    FiniteDimensional (cycl p n) (extendScalars (cycl_le_cyclotomicLayer K n)) :=
  finiteDimensional_extendScalars _

theorem relDeg_pos (n : ℕ) : 0 < relDeg K n := Module.finrank_pos

def traceBasis : Basis (Fin (relDeg K (stableIndex K))) (cycl p (stableIndex K))
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) := by
  letI : Module.Free (cycl p (stableIndex K))
      (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) := Module.Free.of_divisionRing _ _
  exact Module.finBasis _ _

def traceDualBasis : Basis (Fin (relDeg K (stableIndex K))) (cycl p (stableIndex K))
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) :=
  (Algebra.traceForm _ _).dualBasis (traceForm_nondegenerate _ _) (traceBasis K)

def towerVec (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p := (traceBasis K i : PadicAlgCl p)

def towerDualVec (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p :=
  (traceDualBasis K i : PadicAlgCl p)

theorem towerVec_mem (i : Fin (relDeg K (stableIndex K))) :
    towerVec K i ∈ cyclotomicLayer K (stableIndex K) :=
  (traceBasis K i).2

theorem towerDualVec_mem (i : Fin (relDeg K (stableIndex K))) :
    towerDualVec K i ∈ cyclotomicLayer K (stableIndex K) :=
  (traceDualBasis K i).2

theorem normTrace_towerVec_mul (i j : Fin (relDeg K (stableIndex K))) :
    normTrace (cycl p (stableIndex K)) (towerVec K i * towerDualVec K j) =
      if i = j then ((relDeg K (stableIndex K) : PadicAlgCl p))⁻¹ else 0 := by
  have e := normTraceF_eq_trace_div (cycl p (stableIndex K)) (Ω := PadicAlgCl p)
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) (traceBasis K i * traceDualBasis K j)
  have ht : Algebra.trace (cycl p (stableIndex K)) (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K)))
      (traceBasis K i * traceDualBasis K j) = if i = j then 1 else 0 := by
    rw [mul_comm, ← Algebra.traceForm_apply, traceDualBasis,
      LinearMap.BilinForm.apply_dualBasis_left]
  rw [ht] at e
  rw [normTrace]
  change algebraMap _ _ (normTraceF _ (algebraMap (extendScalars (cycl_le_cyclotomicLayer K
    (stableIndex K))) (PadicAlgCl p) (traceBasis K i * traceDualBasis K j))) = _
  rw [e]
  split_ifs <;> simp [relDeg]

def towerCoeff (m : ℕ) (y : PadicAlgCl p) (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p :=
  (relDeg K (stableIndex K) : PadicAlgCl p) * normTrace (cycl p m) (y * towerDualVec K i)

theorem towerCoeff_mem (m : ℕ) (y : PadicAlgCl p) (i : Fin (relDeg K (stableIndex K))) :
    towerCoeff K m y i ∈ cycl p m :=
  mul_mem (IntermediateField.natCast_mem _ _) (normTrace_mem _ _)

theorem normTrace_sum_towerVec_mul {m : ℕ} (hm : stableIndex K ≤ m)
    (c : Fin (relDeg K (stableIndex K)) → PadicAlgCl p) (hc : ∀ i, c i ∈ cycl p m)
    (j : Fin (relDeg K (stableIndex K))) :
    normTrace (cycl p m) ((∑ i, c i * towerVec K i) * towerDualVec K j) =
      c j / (relDeg K (stableIndex K) : PadicAlgCl p) := by
  rw [Finset.sum_mul, normTrace_sum]
  have : ∀ i ∈ (Finset.univ : Finset (Fin (relDeg K (stableIndex K)))),
      normTrace (cycl p m) (c i * towerVec K i * towerDualVec K j) =
        c i * (if i = j then ((relDeg K (stableIndex K) : PadicAlgCl p))⁻¹ else 0) := by
    intro i _
    rw [mul_assoc, normTrace_mul_of_mem _ (hc i),
      normTrace_cycl_eq_of_mem K le_rfl hm (mul_mem (towerVec_mem K i) (towerDualVec_mem K j)),
      normTrace_towerVec_mul]
  rw [Finset.sum_congr rfl this]
  simp [div_eq_mul_inv]

theorem eq_sum_towerCoeff {m : ℕ} (hm : stableIndex K ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) : y = ∑ i, towerCoeff K m y i * towerVec K i := by
  set d := relDeg K (stableIndex K)
  let L := extendScalars (cycl_le_cyclotomicLayer K m)
  have hv : ∀ i, towerVec K i ∈ L := fun i => cyclotomicLayer_mono K hm (towerVec_mem K i)
  let v : Fin d → L := fun i => ⟨towerVec K i, hv i⟩
  have hd0 : (d : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (relDeg_pos K _).ne'
  have hli : LinearIndependent (cycl p m) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : (∑ i, (g i : PadicAlgCl p) * towerVec K i) = 0 := by
      have := congrArg (fun x : L => (x : PadicAlgCl p)) hg
      simpa [v, Algebra.smul_def] using this
    have h2 := normTrace_sum_towerVec_mul K hm (fun i => (g i : PadicAlgCl p)) (fun i => (g i).2) j
    rw [h1, zero_mul, normTrace_zero, eq_comm, div_eq_zero_iff] at h2
    exact Subtype.ext (h2.resolve_right hd0)
  have hcard : Fintype.card (Fin d) = finrank (cycl p m) L := by
    rw [Fintype.card_fin]
    exact (relDeg_eq_of_le K hm).symm
  haveI : Nonempty (Fin d) := ⟨⟨0, relDeg_pos K _⟩⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hsum := B.sum_repr ⟨y, hy⟩
  have hyexp : y = ∑ i, ((B.repr ⟨y, hy⟩ i : cycl p m) : PadicAlgCl p) * towerVec K i := by
    have := congrArg (fun x : L => (x : PadicAlgCl p)) hsum
    simpa [B, v, Algebra.smul_def] using this.symm
  have hc : ∀ j, ((B.repr ⟨y, hy⟩ j : cycl p m) : PadicAlgCl p) = towerCoeff K m y j := by
    intro j
    have := normTrace_sum_towerVec_mul K hm _ (fun i => (B.repr ⟨y, hy⟩ i).2) j
    rw [← hyexp] at this
    rw [towerCoeff, this]
    exact (mul_div_cancel₀ _ hd0).symm
  conv_lhs => rw [hyexp]
  simp_rw [hc]
  rfl

theorem norm_towerCoeff_le {m : ℕ} (hm : stableIndex K ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) (i : Fin (relDeg K (stableIndex K))) :
    ‖towerCoeff K m y i‖ ≤ ‖y * towerDualVec K i‖ := by
  let L := extendScalars (cycl_le_cyclotomicLayer K m)
  have hw : y * towerDualVec K i ∈ L :=
    mul_mem hy (cyclotomicLayer_mono K hm (towerDualVec_mem K i))
  apply norm_natCast_mul_normTrace_le
  have e := minpoly.algebraMap_eq (A := cycl p m) (algebraMap L (PadicAlgCl p)).injective
    (⟨y * towerDualVec K i, hw⟩ : L)
  change (minpoly (cycl p m) (algebraMap L (PadicAlgCl p) ⟨_, hw⟩)).natDegree ∣ _
  rw [e, ← relDeg_eq_of_le K hm]
  exact minpoly.degree_dvd (IsIntegral.of_finite _ _)

theorem norm_normTrace_cyclotomicLayer_le {cF : ℝ} (hcF : 0 ≤ cF)
    (hF : ∀ n m : ℕ, stableIndex K ≤ n → n ≤ m → ∀ x ∈ cycl p m,
      ‖normTrace (cycl p n) x‖ ≤ cF * ‖x‖)
    {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) :
    ‖normTrace (cyclotomicLayer K n) y‖ ≤
      cF * (∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖) * ‖y‖ := by
  have hexp := eq_sum_towerCoeff K (hn.trans hnm) hy
  have key : normTrace (cyclotomicLayer K n) y =
      ∑ i, towerVec K i * normTrace (cycl p n) (towerCoeff K m y i) := by
    conv_lhs => rw [hexp]
    rw [normTrace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, normTrace_mul_of_mem _ (cyclotomicLayer_mono K hn (towerVec_mem K i)),
      normTrace_cyclotomicLayer_eq_of_mem K hn hnm (towerCoeff_mem K m y i)]
  rw [key, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have h1 := hF n m hn hnm _ (towerCoeff_mem K m y i)
  have h2 := norm_towerCoeff_le K (hn.trans hnm) hy i
  rw [norm_mul] at h2
  calc ‖towerVec K i‖ * ‖normTrace (cycl p n) (towerCoeff K m y i)‖
      ≤ ‖towerVec K i‖ * (cF * ‖towerCoeff K m y i‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖towerVec K i‖ * (cF * (‖y‖ * ‖towerDualVec K i‖)) := by gcongr
    _ = cF * (‖towerVec K i‖ * ‖towerDualVec K i‖) * ‖y‖ := by ring


omit [FiniteDimensional ℚ_[p] K] in
theorem cyclotomicLayer_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : ∀ x ∈ K, σ x = x)
    (n : ℕ) :
    (cyclotomicLayer K n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cyclotomicLayer K n := by
  rw [cyclotomicLayer, IntermediateField.map_sup, cycl_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change σ y ∈ K
    rw [hσ y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hσ x hx⟩

omit [FiniteDimensional ℚ_[p] K] in
theorem map_mem_cyclotomicLayer (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cyclotomicLayer K n) :
    σ x ∈ cyclotomicLayer K n := by
  rw [← cyclotomicLayer_map K σ hσ n]
  exact ⟨x, hx, rfl⟩

omit [FiniteDimensional ℚ_[p] K] in
theorem map_mem_cyclotomicLimit (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    σ x ∈ cyclotomicLimit K := by
  obtain ⟨n, hn⟩ := (mem_cyclotomicLimit K).1 hx
  exact (mem_cyclotomicLimit K).2 ⟨n, map_mem_cyclotomicLayer K σ hσ hn⟩


omit [FiniteDimensional ℚ_[p] K] in
theorem normTrace_cyclotomicLayer_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) :=
  normTrace_map_of_map_eq _ σ (cyclotomicLayer_map K σ hσ n) y


omit [FiniteDimensional ℚ_[p] K] in
theorem normTrace_cyclotomicLayer_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) :=
  normTrace_cyclotomicLayer_map K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) n y

section Gamma

variable {n : ℕ} (γ : Gal(PadicAlgCl p/cyclotomicLayer K n))

end Gamma

end

end GroundTheory.PAdicHodge
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Module Set

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

def tateTrace (n : ℕ) : PadicAlgCl p → PadicAlgCl p := normTrace (cyclotomicLayer K n)

theorem tateTrace_add (n : ℕ) (y z : PadicAlgCl p) :
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  normTrace_add _ y z

theorem tateTrace_mem (n : ℕ) (y : PadicAlgCl p) : tateTrace K n y ∈ cyclotomicLayer K n :=
  normTrace_mem _ y

theorem tateTrace_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTrace K n a = a :=
  normTrace_of_mem _ ha

theorem tateTrace_mul_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n)
    (y : PadicAlgCl p) : tateTrace K n (a * y) = a * tateTrace K n y :=
  normTrace_mul_of_mem _ ha y

theorem tateTrace_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    tateTrace K n (σ y) = σ (tateTrace K n y) :=
  normTrace_cyclotomicLayer_gal K σ n y

theorem tateTrace_tateTrace_of_le {n n' : ℕ} (h : n ≤ n') (y : PadicAlgCl p) :
    tateTrace K n (tateTrace K n' y) = tateTrace K n y :=
  normTrace_normTrace_of_le (cyclotomicLayer_mono K h) y

theorem exists_norm_tateTrace_le_of_stableIndex_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, stableIndex K ≤ n → ∀ x ∈ cyclotomicLimit K,
      ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  refine ⟨p * ∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro n hn x hx
  obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hx
  have hm' : x ∈ cyclotomicLayer K (max m n) := cyclotomicLayer_mono K (le_max_left m n) hm
  refine norm_normTrace_cyclotomicLayer_le K (Nat.cast_nonneg p) ?_ hn (le_max_right m n) hm'
  intro n' m' hn' hnm' y hy
  exact norm_normTrace_cycl_le
    (le_trans (by norm_num) ((two_le_stableIndex K).trans hn')) hnm' hy

theorem exists_norm_tateTrace_le_on_layer (n N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ cyclotomicLayer K N, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  let S : Submodule ℚ_[p] (PadicAlgCl p) := (cyclotomicLayer K N).toSubalgebra.toSubmodule
  haveI : FiniteDimensional ℚ_[p] S :=
    inferInstanceAs (FiniteDimensional ℚ_[p] (cyclotomicLayer K N))
  let f : S →ₗ[ℚ_[p]] PadicAlgCl p :=
    ((normTraceₗ (cyclotomicLayer K n)).restrictScalars ℚ_[p]).comp S.subtype
  let f' := LinearMap.toContinuousLinearMap f
  refine ⟨‖f'‖, ContinuousLinearMap.opNorm_nonneg f', fun x hx => ?_⟩
  have := f'.le_opNorm ⟨x, hx⟩
  exact this

theorem exists_norm_tateTrace_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, ∀ x ∈ cyclotomicLimit K, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_tateTrace_le_of_stableIndex_le K
  choose c' hc'0 hc' using fun n => exists_norm_tateTrace_le_on_layer K n (stableIndex K)
  refine ⟨c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n), by
    have : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
    positivity, ?_⟩
  intro n x hx
  have hs : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
  by_cases hn : stableIndex K ≤ n
  · calc ‖tateTrace K n x‖ ≤ c * ‖x‖ := hc n hn x hx
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        nlinarith [mul_nonneg (mul_nonneg hc0 hs) (norm_nonneg x)]
  · push_neg at hn
    have hle : c' n ≤ ∑ n ∈ Finset.range (stableIndex K), c' n :=
      Finset.single_le_sum (fun n _ => hc'0 n) (Finset.mem_range.2 hn)
    rw [← tateTrace_tateTrace_of_le K hn.le x]
    calc ‖tateTrace K n (tateTrace K (stableIndex K) x)‖
        ≤ c' n * ‖tateTrace K (stableIndex K) x‖ := hc' n _ (tateTrace_mem K _ x)
      _ ≤ c' n * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hc _ le_rfl x hx) (hc'0 n)
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        have := norm_nonneg x
        nlinarith [mul_nonneg hc0 this]

def tateBound : ℝ := Classical.choose (exists_norm_tateTrace_le K)

theorem tateBound_nonneg : 0 ≤ tateBound K := (Classical.choose_spec (exists_norm_tateTrace_le K)).1

theorem norm_tateTrace_le (n : ℕ) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    ‖tateTrace K n x‖ ≤ tateBound K * ‖x‖ :=
  (Classical.choose_spec (exists_norm_tateTrace_le K)).2 n x hx

section Completion

def cyclotomicCompletion : Set ℂ_[p] := closureInCp (cyclotomicLimit K)

def tateTraceHat (n : ℕ) : ℂ_[p] → ℂ_[p] := extendToClosure (cyclotomicLimit K) (tateTrace K n)

variable {K}

theorem tateTrace_add_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K, ∀ z ∈ cyclotomicLimit K,
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  fun y _ z _ => tateTrace_add K n y z

theorem norm_tateTrace_le_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ :=
  fun _ hy => norm_tateTrace_le K n hy

theorem norm_tateTraceHat_le (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    ‖tateTraceHat K n x‖ ≤ tateBound K * ‖x‖ :=
  norm_extendToClosure_le (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx

theorem tateTraceHat_add (n : ℕ) {x x' : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K)
    (hx' : x' ∈ cyclotomicCompletion K) :
    tateTraceHat K n (x + x') = tateTraceHat K n x + tateTraceHat K n x' :=
  (extendToClosure_add (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx hx').2

theorem tateTraceHat_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n x ∈
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (cyclotomicLayer K n : Set (PadicAlgCl p)) :=
  extendToClosure_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (fun y _ => tateTrace_mem K n y) hx

theorem tateTraceHat_coe_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a :=
  extendToClosure_coe_of_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha => tateTrace_of_mem K ha) ha

theorem tateTraceHat_mul {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x :=
  extendToClosure_mul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha y _ => tateTrace_mul_of_mem K ha y) ha hx

theorem gal_mem_cyclotomicLimit (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLimit K) : σ y ∈ cyclotomicLimit K :=
  map_mem_cyclotomicLimit K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) hy

theorem smul_mem_cyclotomicCompletion (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K :=
  smul_mem_closureInCp σ (fun _ hy => gal_mem_cyclotomicLimit σ hy) hx

theorem tateTraceHat_smul (n : ℕ) (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : tateTraceHat K n (σ • x) = σ • tateTraceHat K n x :=
  extendToClosure_smul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) σ
    (fun _ hy => gal_mem_cyclotomicLimit σ hy) (fun y _ => tateTrace_gal K σ n y) hx

end Completion

section Gamma

variable {K}

end Gamma

end

end GroundTheory.PAdicHodge
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField UniformSpace

variable {p : ℕ} [hp : Fact p.Prime]

section Torsion

theorem one_add_pow_ne_one {w : PadicAlgCl p} (hw0 : w ≠ 0) (hw : ‖w‖ < (p : ℝ)⁻¹) {m : ℕ}
    (hm : m ≠ 0) : (1 + w) ^ m ≠ 1 := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hexp : (1 + w) ^ (m' + 1) - 1 = ((m' + 1 : ℕ) : PadicAlgCl p) * w +
      ∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) := by
    rw [add_comm (1 : PadicAlgCl p) w, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_one,
      Nat.choose_one_right, zero_add]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hmpos : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
    rw [norm_pos_iff]; exact_mod_cast Nat.succ_ne_zero m'
  have hlead : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rw [norm_mul]; exact mul_pos hmpos hwpos

  have hterm : ∀ k ∈ Finset.range m', ‖w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    intro k _

    have hch : ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) * ((k + 1 + 1 : ℕ) : PadicAlgCl p) =
        ((m' + 1 : ℕ) : PadicAlgCl p) * (m'.choose (k + 1) : PadicAlgCl p) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m' (k + 1)).symm
    have hk0 : (k + 1 + 1 : ℕ) ≠ 0 := by omega
    have hknorm : ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by
      rw [norm_natCast_padicAlgCl hk0, zpow_neg, zpow_natCast]
      gcongr
      exact_mod_cast Nat.le_of_dvd (by omega) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have hkpos : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hC : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ ≤
        ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ) := by
      have h1 := congrArg norm hch
      rw [norm_mul, norm_mul] at h1
      have h2 : ‖(m'.choose (k + 1) : PadicAlgCl p)‖ ≤ 1 :=
        IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) _
      have h3 : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤
          ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
        calc _ ≤ ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ *
              ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by gcongr
          _ = _ := h1
          _ ≤ ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * 1 := by gcongr
          _ = _ := mul_one _
      rwa [← div_eq_mul_inv, div_le_iff₀ hkpos] at h3

    have hpow : ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < 1 := by
      have h1 : ‖w‖ ^ (k + 1) < ((p : ℝ)⁻¹) ^ (k + 1) :=
        pow_lt_pow_left₀ hw (norm_nonneg _) (Nat.succ_ne_zero k)
      have h2 : ((k + 1 + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
        have := Nat.lt_pow_self (n := k + 1) hp.out.one_lt
        exact_mod_cast this
      calc ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < ((k + 1 + 1 : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ (k + 1) :=
            mul_lt_mul_of_pos_left h1 hkpos
        _ ≤ (p : ℝ) ^ (k + 1) * ((p : ℝ)⁻¹) ^ (k + 1) := by gcongr
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    rw [norm_mul, norm_pow, norm_mul]
    calc ‖w‖ ^ (k + 1 + 1) * ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
        ≤ ‖w‖ ^ (k + 1 + 1) * (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)) := by
          gcongr
      _ = (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * (((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1)) := by
          ring
      _ < (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * 1 :=
          mul_lt_mul_of_pos_left hpow (mul_pos hmpos hwpos)
      _ = _ := mul_one _
  have htail : ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rcases (Finset.range m').eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty, norm_zero]; exact hlead
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun k => w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p))
      exact hle.trans_lt (hterm i hi)
  intro h
  have h0 : (1 + w) ^ (m' + 1) - 1 = 0 := by rw [h, sub_self]
  rw [hexp] at h0
  have hne : ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ ≠
      ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ :=
    htail.ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [h0, norm_zero] at this
  exact hlead.ne (this.trans (max_eq_left htail.le))

end Torsion

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

section Character

theorem cycloChar_toZModPow_eq_one (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    (cycloChar K σ : ℤ_[p]).toZModPow n = 1 := by
  rw [cycloChar, MonoidHom.comp_apply, cyclotomicCharacter.toZModPow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact @Subsingleton.elim (ZMod 1) _ _ _
  refine (modularCyclotomicCharacter.unique _ _ _ ?_).symm
  intro t ht
  have hp1 : p ^ n ≠ 1 := (Nat.one_lt_pow hn.ne' hp.out.one_lt).ne'
  rw [ZMod.val_one'' hp1, pow_one]
  have ht' : (t : PadicAlgCl p) ^ p ^ n = 1 := by
    have := (mem_rootsOfUnity _ _).1 ht
    simpa using congrArg Units.val this
  exact h _ ht'

theorem norm_cycloChar_sub_one_le (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    ‖(cycloChar K σ : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, cycloChar_toZModPow_eq_one K σ n h, sub_self]

theorem cycloChar_eq_one_of_forall (σ : Gal(PadicAlgCl p/K))
    (h : ∀ n : ℕ, ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) : cycloChar K σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycloChar_toZModPow_eq_one K σ n (h n), Units.val_one, map_one]

theorem cycloChar_zpow_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : cycloChar K σ ^ j ≠ 1 := by
  intro hpow
  have hm : cycloChar K σ ^ j.natAbs = 1 := by
    rcases Int.natAbs_eq j with hj' | hj'
    · rw [hj', zpow_natCast] at hpow; exact hpow
    · rw [hj', zpow_neg, inv_eq_one, zpow_natCast] at hpow; exact hpow
  set u : ℤ_[p] := ((cycloChar K σ : ℤ_[p]ˣ) : ℤ_[p])
  set w : PadicAlgCl p := algebraMap ℚ_[p] (PadicAlgCl p) ((u - 1 : ℤ_[p]) : ℚ_[p])
  have hw0 : w ≠ 0 := by
    intro hw
    rw [map_eq_zero, PadicInt.coe_eq_zero, sub_eq_zero] at hw
    exact hne (Units.ext hw)
  have hw : ‖w‖ < (p : ℝ)⁻¹ := by
    rw [norm_algebraMap', ← PadicInt.norm_def]
    refine (norm_cycloChar_sub_one_le K σ 2 h2).trans_lt ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hp1 (by norm_num)
  apply one_add_pow_ne_one hw0 hw (Int.natAbs_ne_zero.2 hj)
  have h1 : (1 : PadicAlgCl p) + w = algebraMap ℚ_[p] (PadicAlgCl p) (u : ℚ_[p]) := by
    simp [w, u]
  rw [h1, ← map_pow, ← PadicInt.coe_pow, ← Units.val_pow_eq_pow_val, hm]
  simp

theorem twistScalar_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : twistScalar K j σ ≠ 1 := by
  intro h
  rw [twistScalar, ← map_one (algebraMap ℚ_[p] ℂ_[p]),
    (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff] at h
  have h' : ((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) = 1 := Subtype.ext h
  exact cycloChar_zpow_ne_one K σ h2 hne hj (Units.ext h')

variable [FiniteDimensional ℚ_[p] K]

theorem exists_gal_fix_cyclotomicLayer_cycloChar_ne_one (n : ℕ) :
    ∃ σ : Gal(PadicAlgCl p/K), (∀ y ∈ cyclotomicLayer K n, σ y = y) ∧ cycloChar K σ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  set E : IntermediateField K (PadicAlgCl p) := extendScalars (le_cyclotomicLayer K n)
  have hcyc : ∀ m, cycl p m ≤ cyclotomicLayer K n := by
    intro m
    refine adjoin_le_iff.2 fun ζ hζ => ?_
    have hζ' : ζ ^ p ^ m = 1 := hζ
    have hmem : ζ ∈ fixedField E.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro σ hσ
      have hσ' : ∀ y ∈ cyclotomicLayer K n, σ y = y := fun y hy =>
        (mem_fixingSubgroup_iff _ _).1 hσ y hy
      have h1 := hcon σ hσ'
      rw [cycloChar_spec K σ hζ', h1, Units.val_one, map_one]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [pow_zero, pow_one] at hζ'
        simp [hζ']
      · have hp1 : p ^ m ≠ 1 := (Nat.one_lt_pow hm.ne' hp.out.one_lt).ne'
        rw [ZMod.val_one'' hp1, pow_one]
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact hmem
  have hle := IntermediateField.finrank_le_of_le_right (hcyc (Module.finrank ℚ_[p] (cyclotomicLayer K n) + 1))
  rw [finrank_cycl, Nat.totient_prime_pow_succ hp.out] at hle
  have h1 : Module.finrank ℚ_[p] (cyclotomicLayer K n) < p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) :=
    Nat.lt_pow_self hp.out.one_lt
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) ≤
      p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) * (p - 1) := Nat.le_mul_of_pos_right _ h2
  omega

end Character

section Invariants

noncomputable abbrev cyclotomicLimitGal : Subgroup Gal(PadicAlgCl p/K) :=
  (extendScalars ((le_cyclotomicLayer K 0).trans (cyclotomicLayer_le_cyclotomicLimit K 0))).fixingSubgroup

theorem cycloChar_eq_one_of_mem_cyclotomicLimitGal {σ : Gal(PadicAlgCl p/K)}
    (hσ : σ ∈ cyclotomicLimitGal K) : cycloChar K σ = 1 := by
  refine cycloChar_eq_one_of_forall K σ fun n ζ hζ => ?_
  have hmem : ζ ∈ cyclotomicLimit K :=
    cyclotomicLayer_le_cyclotomicLimit K n (cycl_le_cyclotomicLayer K n (pow_eq_one_mem_cycl hζ))
  exact (mem_fixingSubgroup_iff _ _).1 hσ ζ hmem

theorem mem_cyclotomicCompletion_of_forall_smul_eq {x : ℂ_[p]}
    (hx : ∀ σ ∈ cyclotomicLimitGal K, σ • x = x) : x ∈ cyclotomicCompletion K := by
  have h := fixedPoints_closedSubgroup_eq_closure (cyclotomicLimitGal K)
    (InfiniteGalois.fixingSubgroup_isClosed _)
  have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ cyclotomicLimitGal K, σ • x = x} := hx
  rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
  exact hx'

variable [FiniteDimensional ℚ_[p] K]

theorem eq_zero_of_forall_twistScalar_mul_smul_eq {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), twistScalar K j σ * (σ • x) = x) : x = 0 := by

  have hxc : x ∈ cyclotomicCompletion K := by
    refine mem_cyclotomicCompletion_of_forall_smul_eq K fun σ hσ => ?_
    have h1 : twistScalar K j σ = 1 := by
      simp [twistScalar, cycloChar_eq_one_of_mem_cyclotomicLimitGal K hσ]
    simpa [h1] using hx σ

  have hR : ∀ n, stableIndex K ≤ n → tateTraceHat K n x = 0 := by
    intro n hn
    have key : ∀ σ : Gal(PadicAlgCl p/K),
        tateTraceHat K n x = twistScalar K j σ * (σ • tateTraceHat K n x) := by
      intro σ
      have hc : twistScalar K j σ =
          ((algebraMap ℚ_[p] (PadicAlgCl p) (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) :
            PadicAlgCl p) : ℂ_[p]) := rfl
      conv_lhs => rw [← hx σ]
      rw [hc, tateTraceHat_mul (IntermediateField.algebraMap_mem _ _) (smul_mem_cyclotomicCompletion σ hxc),
        tateTraceHat_smul n σ hxc]
    obtain ⟨σ, hσ, hne⟩ := exists_gal_fix_cyclotomicLayer_cycloChar_ne_one K n
    have h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ := fun ζ hζ =>
      hσ ζ (cycl_le_cyclotomicLayer K n (cycl_mono (p := p)
        ((two_le_stableIndex K).trans hn) (pow_eq_one_mem_cycl hζ)))
    obtain ⟨b, hb, hbx⟩ := tateTraceHat_mem n hxc
    have hfix : σ • tateTraceHat K n x = tateTraceHat K n x := by
      rw [← hbx, gal_smul_coe, hσ b hb]
    have h3 := key σ
    rw [hfix] at h3
    have h4 : (twistScalar K j σ - 1) * tateTraceHat K n x = 0 := by
      rw [sub_mul, one_mul, ← h3, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (twistScalar_ne_one K σ h2 hne hj))

  set c := tateBound K
  have hc0 : 0 ≤ c := tateBound_nonneg K
  have hbound : ∀ ε > 0, ‖x‖ ≤ (1 + c) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hy
    set m' := max m (stableIndex K)
    have hym : y ∈ cyclotomicLayer K m' := cyclotomicLayer_mono K (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ cyclotomicCompletion K := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ cyclotomicCompletion K := sub_mem_closureInCp hyc hxc
    have h1 : tateTraceHat K m' (y : ℂ_[p]) =
        tateTraceHat K m' ((y : ℂ_[p]) - x) + tateTraceHat K m' x := by
      rw [← tateTraceHat_add m' hsub hxc, sub_add_cancel]
    rw [tateTraceHat_coe_of_mem hym, hR m' (le_max_right _ _), add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ c * ε := by
      rw [h1]
      refine (norm_tateTraceHat_le m' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hc0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + c * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + c) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound (‖x‖ / (2 * (1 + c))) (by positivity)
  have h' : (1 + c) * (‖x‖ / (2 * (1 + c))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

theorem cpTwistRep_invariants_zero :
    (cpTwistRep K 0).invariants = LinearMap.range (Algebra.linearMap K ℂ_[p]) := by
  ext x
  rw [ContRepresentation.mem_invariants, LinearMap.mem_range]
  simp only [cpTwistRep_apply, twistScalar_zero, one_mul, Algebra.linearMap_apply]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_eq_coe_of_forall_smul_eq (K := K) h
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ σ
    exact gal_smul_algebraMap_intermediateField K σ k

theorem cpTwistRep_invariants_eq_bot {j : ℤ} (hj : j ≠ 0) : (cpTwistRep K j).invariants = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [ContRepresentation.mem_invariants] at hx
  exact (Submodule.mem_bot K).2 (eq_zero_of_forall_twistScalar_mul_smul_eq K hj hx)

end Invariants

end GroundTheory.PAdicHodge
