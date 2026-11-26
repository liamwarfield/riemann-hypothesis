module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import GroundTheory.AutomorphicForms.LocallyProfinite
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
open scoped TensorProduct
open Algebra.TensorProduct (includeRight)

namespace GlobalTheory.CompanionTheory.NormLoc

section

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O']

theorem trace_fixed (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1) (u : O') :
    τ (∑ j ∈ Finset.range ℓ, (τ ^ j) u) = ∑ j ∈ Finset.range ℓ, (τ ^ j) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have e := (Finset.sum_range_succ' (fun j => (τ ^ j) u) ℓ).symm.trans
    (Finset.sum_range_succ (fun j => (τ ^ j) u) ℓ)
  rw [hτ, pow_zero] at e
  rw [← add_right_cancel e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

theorem exists_trace_one [IsLocalRing O] [Module.Finite O O'] (ℓ : ℕ) (τ : O' ≃ₐ[O] O')
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O'))
    (hdual : ∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) :
    ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1 := by
  obtain ⟨x, y, hxy⟩ := hdual
  have hc : ∀ i, ∃ c : O, algebraMap O O' c = ∑ j ∈ Finset.range ℓ, (τ ^ j) (y i) := fun i =>
    hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ (y i))
  choose c hc using hc
  have hsum : ∑ i, x i * algebraMap O O' (c i) = 1 := by
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j hj => hxy j (Finset.mem_range.mp hj)]
    simp [hℓ]
  by_cases hunit : ∃ i, IsUnit (c i)
  · obtain ⟨i, u, hu⟩ := hunit
    refine ⟨algebraMap O O' (↑u⁻¹ : O) * y i, ?_⟩
    have h : ∀ j, (τ ^ j) (algebraMap O O' (↑u⁻¹ : O) * y i) =
        algebraMap O O' (↑u⁻¹ : O) * (τ ^ j) (y i) := by
      intro j
      rw [map_mul, AlgEquiv.commutes]
    simp_rw [h]
    rw [← Finset.mul_sum, ← hc i, ← map_mul, ← hu, Units.inv_mul, map_one]
  · push_neg at hunit
    have htop : (⊤ : Submodule O O') ≤ IsLocalRing.maximalIdeal O • ⊤ := by
      intro z _
      have hz : z = ∑ i, c i • (z * x i) := by
        simp_rw [Algebra.smul_def]
        calc z = z * 1 := (mul_one z).symm
          _ = _ := by
            rw [← hsum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      rw [hz]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hunit i
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) ⊤
      Module.Finite.fg_top htop (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have h1 : (1 : O') = 0 := by
      have : (1 : O') ∈ (⊤ : Submodule O O') := Submodule.mem_top
      rw [hbot] at this
      exact this
    haveI : Subsingleton O' := subsingleton_of_zero_eq_one h1.symm
    exact ⟨0, Subsingleton.elim _ _⟩

variable {R : Type} [CommRing R] [Algebra O R]

theorem map_pow_succ_apply (τ : O' ≃ₐ[O] O') (j : ℕ) (t : O' ⊗[O] R) :
    Algebra.TensorProduct.map ((τ ^ (j + 1) : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t =
      Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
        (Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u r => simp [Algebra.TensorProduct.map_tmul, pow_succ']
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_pow_fixed (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) (j : ℕ) :
    Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) s = s := by
  induction j with
  | zero =>
    clear hs
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy]
  | succ j ih => rw [GlobalTheory.CompanionTheory.NormLoc.map_pow_succ_apply, ih, hs]

theorem trace_tensor_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (t : O' ⊗[O] R) :
    ∑ j ∈ Finset.range ℓ,
        Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t ∈
      Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x r =>
    obtain ⟨c, hc⟩ := hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ x)
    refine ⟨c • r, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
    rw [← TensorProduct.sum_tmul, ← hc, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]⟩

theorem fixed_mem_range (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (a : O')
    (ha : ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) :
    s ∈ Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  have key : ∑ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) ((a ⊗ₜ[O] (1 : R)) * s) = s := by
    simp only [map_mul, GlobalTheory.CompanionTheory.NormLoc.map_pow_fixed τ s hs]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, map_one]
    rw [← Finset.sum_mul, ← TensorProduct.sum_tmul, ha, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← key]
  exact GlobalTheory.CompanionTheory.NormLoc.trace_tensor_mem ℓ τ hτ hfix _

theorem prod_one_add_tmul_sub_mem (J : Ideal R) (m : ℕ) (hm : 1 ≤ m) (r : R) (hr : r ∈ J ^ m)
    (S : Finset ℕ) (b : ℕ → O') :
    (∏ j ∈ S, (1 + b j ⊗ₜ[O] r)) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r) ∈
      Ideal.map (includeRight : R →ₐ[O] O' ⊗[O] R) (J ^ (m + 1)) := by
  classical
  have hrr : r * r ∈ J ^ (m + 1) := by
    have h := Ideal.mul_mem_mul hr hr
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    have h : (1 + b k ⊗ₜ[O] r) * ∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (b k + ∑ j ∈ S, b j) ⊗ₜ[O] r)
        = (1 + b k ⊗ₜ[O] r) * (∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r))
          + (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) := by
      rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h' : (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) =
        ((b k * ∑ j ∈ S, b j) ⊗ₜ[O] (1 : R)) * (includeRight : R →ₐ[O] O' ⊗[O] R) (r * r) := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul]
    rw [h']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hrr)

end

theorem fixedRing_traceOne_firstOrder : PositivityTheory.Rg.Tf.Loc.N2 := by
  unfold PositivityTheory.Rg.Tf.Loc.N2
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.NormLoc.exists_trace_one ℓ τ hℓ hτ hfix hdual
  refine ⟨fun s hs => GlobalTheory.CompanionTheory.NormLoc.fixed_mem_range ℓ τ hτ hfix a ha s hs, a, ha, ?_⟩
  intro m hm r hr
  have key := GlobalTheory.CompanionTheory.NormLoc.prod_one_add_tmul_sub_mem (O := O) (O' := O') (Ideal.jacobson (⊥ : Ideal R)) m hm r hr
    (Finset.range ℓ) (fun j => (τ ^ j) a)
  have e1 : ∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) (1 + a ⊗ₜ[O] r) = ∏ j ∈ Finset.range ℓ, (1 + (τ ^ j) a ⊗ₜ[O] r) :=
    Finset.prod_congr rfl fun j _ => by simp
  have e2 : (includeRight : R →ₐ[O] O' ⊗[O] R) (1 + r) =
      1 + (∑ j ∈ Finset.range ℓ, (τ ^ j) a) ⊗ₜ[O] r := by
    rw [ha, Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add,
      ← Algebra.TensorProduct.one_def]
  rw [← e1, ← e2] at key
  exact key

end GlobalTheory.CompanionTheory.NormLoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondPropertyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_second_property : PositivityTheory.Rg.Tf.Loc.N2 := by
  first | exact @GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | exact GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder | (intros; apply GlobalTheory.CompanionTheory.NormLoc.fixedRing_traceOne_firstOrder <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotientStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotient
open Topology Filter Set

namespace GlobalTheory.CompanionTheory.LGroupSection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cosetImage (H K : Subgroup G) (d : G) : Set (G ⧸ H) :=
  {x | ∃ k ∈ K, ((d * k : G) : G ⧸ H) = x}

theorem isClopen_cosetImage (H K : Subgroup G) [IsClosed (H : Set G)]
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (d : G) :
    IsClopen (cosetImage H K d) := by
  have himg : cosetImage H K d =
      ((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨d * k, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  rw [himg]
  have hopen : IsOpen ((fun k : G => d * k) '' (K : Set G)) :=
    (Homeomorph.mulLeft d).isOpenMap _ hKo
  have hcomp : IsCompact ((fun k : G => d * k) '' (K : Set G)) :=
    hKc.image (continuous_const.mul continuous_id)
  have hcomp' : IsCompact (((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G))) :=
    hcomp.image continuous_quotient_mk'
  exact ⟨hcomp'.isClosed, QuotientGroup.isOpenMap_coe _ hopen⟩

theorem exists_isLocallyConstant_mem {X : Type*} [TopologicalSpace X] (V : ℕ → Set X)
    (hV : ∀ n, IsClopen (V n)) (hcov : ∀ x, ∃ n, x ∈ V n) :
    ∃ f : X → ℕ, IsLocallyConstant f ∧ ∀ x, x ∈ V (f x) := by
  classical
  refine ⟨fun x => Nat.find (hcov x), ?_, fun x => Nat.find_spec (hcov x)⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨V (Nat.find (hcov x)) ∩ ⋂ j ∈ Finset.range (Nat.find (hcov x)), (V j)ᶜ,
    (hV _).isOpen.inter (isOpen_biInter_finset fun j _ => (hV j).compl.isOpen), ?_, ?_⟩
  · refine ⟨Nat.find_spec (hcov x), ?_⟩
    simp only [mem_iInter, Finset.mem_range]
    exact fun j hj => Nat.find_min (hcov x) hj
  · rintro y ⟨hy1, hy2⟩
    simp only [mem_iInter, Finset.mem_range] at hy2
    refine le_antisymm (Nat.find_min' _ hy1) ?_
    by_contra hlt
    exact hy2 _ (not_le.1 hlt) (Nat.find_spec (hcov y))

theorem exists_refine [SecondCountableTopology G] (H K L : Subgroup G) [IsClosed (H : Set G)]
    (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G))
    (t : G ⧸ H → G) (ht : IsLocallyConstant t) (h : ∀ x, x ∈ cosetImage H K (t x)) :
    ∃ t' : G ⧸ H → G, IsLocallyConstant t' ∧ (∀ x, x ∈ cosetImage H L (t' x)) ∧
      ∀ x, (t x)⁻¹ * t' x ∈ K := by
  let e : ℕ → G := TopologicalSpace.denseSeq G
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq G
  let V : ℕ → Set (G ⧸ H) := fun n =>
    (t ⁻¹' {g | g⁻¹ * e n ∈ K}) ∩ cosetImage H L (e n)
  have hV : ∀ n, IsClopen (V n) := fun n =>
    IsClopen.inter ⟨isOpen_compl_iff.1 (by simpa only [preimage_compl] using (ht ({g | g⁻¹ * e n ∈ K}ᶜ))), ht _⟩
      (isClopen_cosetImage H L hLo hLc (e n))
  have hcov : ∀ x, ∃ n, x ∈ V n := by
    intro x
    obtain ⟨k, hk, hkx⟩ := h x
    have hopen : IsOpen ((fun l : G => t x * k * l) '' (L : Set G)) :=
      (Homeomorph.mulLeft (t x * k)).isOpenMap _ hLo
    obtain ⟨n, l, hl, hn⟩ := he.exists_mem_open hopen ⟨t x * k * 1, 1, L.one_mem, rfl⟩
    refine ⟨n, ?_, l⁻¹, L.inv_mem hl, ?_⟩
    · simp only [mem_preimage, mem_setOf_eq, ← hn]
      have : (t x)⁻¹ * (t x * k * l) = k * l := by group
      rw [this]
      exact K.mul_mem hk (hLK hl)
    · rw [← hn, mul_inv_cancel_right]
      exact hkx
  obtain ⟨f, hf, hfV⟩ := exists_isLocallyConstant_mem V hV hcov
  exact ⟨fun x => e (f x), hf.comp e, fun x => (hfV x).2, fun x => (hfV x).1⟩

theorem exists_subgroup_seq [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [FirstCountableTopology G] :
    ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧ (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, IsOpen (K n : Set G)) ∧
      (∀ n, IsCompact (K (n + 1) : Set G)) ∧ ∀ W ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ W := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose L hLc hLU using fun n =>
    GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset (hU.1.mem_of_mem (i := n) trivial)
  obtain ⟨K, hK0, hsucc⟩ : ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧
      ∀ n, K (n + 1) = K n ⊓ (L n : Subgroup G) :=
    ⟨fun n => Nat.rec (motive := fun _ => Subgroup G) ⊤
      (fun n S => S ⊓ (L n : Subgroup G)) n, rfl, fun _ => rfl⟩
  have hopen : ∀ n, IsOpen (K n : Set G) := by
    intro n
    induction n with
    | zero =>
      rw [hK0]
      exact isOpen_univ
    | succ n ih =>
      rw [hsucc, Subgroup.coe_inf]
      exact ih.inter (L n).isOpen
  have hle : ∀ n, K (n + 1) ≤ L n := fun n => by
    rw [hsucc]
    exact inf_le_right
  refine ⟨K, hK0, fun n => by rw [hsucc]; exact inf_le_left, hopen, fun n => ?_, fun W hW => ?_⟩
  · have hclosed : IsClosed (K (n + 1) : Set G) :=
      (⟨K (n + 1), hopen (n + 1)⟩ : OpenSubgroup G).isClosed
    exact (hLc n).of_isClosed_subset hclosed (hle n)
  · obtain ⟨n, -, hn⟩ := hU.1.mem_iff.1 hW
    exact ⟨n + 1, fun g hg => hn (hLU n (hle n hg))⟩

theorem exists_continuous_section (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  classical
  haveI : IsClosed (H : Set G) := hH
  obtain ⟨K, hK0, hKle, hKo, hKc, hKb⟩ := exists_subgroup_seq (G := G)

  let P : ℕ → (G ⧸ H → G) → Prop := fun n t =>
    IsLocallyConstant t ∧ ∀ x, x ∈ cosetImage H (K n) (t x)
  have hstep : ∀ n (t : {t // P n t}), ∃ t' : {t // P (n + 1) t},
      ∀ x, (t.1 x)⁻¹ * t'.1 x ∈ K n := by
    rintro n ⟨t, ht, hmem⟩
    obtain ⟨t', h1, h2, h3⟩ :=
      exists_refine H (K n) (K (n + 1)) (hKle n) (hKo _) (hKc n) t ht hmem
    exact ⟨⟨t', h1, h2⟩, h3⟩
  have h0 : P 0 (fun _ => 1) := by
    refine ⟨IsLocallyConstant.const _, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, by simp [hK0], by simp⟩
  choose nxt hnxt using hstep
  let T : (n : ℕ) → {t // P n t} := fun n => Nat.rec ⟨_, h0⟩ (fun n t => nxt n t) n
  have hT : ∀ n x, ((T n).1 x)⁻¹ * (T (n + 1)).1 x ∈ K n := fun n x => hnxt n (T n) x

  let C : G ⧸ H → ℕ → Set G := fun x n => (fun k => (T (n + 1)).1 x * k) '' (K (n + 1) : Set G)
  have hCmem : ∀ x n g, g ∈ C x n ↔ ((T (n + 1)).1 x)⁻¹ * g ∈ K (n + 1) := by
    intro x n g
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
    · intro hg
      exact ⟨_, hg, by simp⟩
  have hCanti : ∀ x n, C x (n + 1) ⊆ C x n := by
    intro x n g hg
    rw [hCmem] at hg ⊢
    have h1 := hT (n + 1) x
    have : ((T (n + 1)).1 x)⁻¹ * g = (((T (n + 1)).1 x)⁻¹ * (T (n + 1 + 1)).1 x) *
        (((T (n + 1 + 1)).1 x)⁻¹ * g) := by group
    rw [this]
    exact (K (n + 1)).mul_mem h1 (hKle _ hg)
  have hCne : ∀ x, (⋂ n, C x n).Nonempty := fun x =>
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (C x) (hCanti x)
      (fun n => ⟨_, 1, (K (n + 1)).one_mem, rfl⟩)
      ((hKc 0).image (continuous_const.mul continuous_id))
      (fun n => ((hKc n).image (continuous_const.mul continuous_id)).isClosed)
  choose s hs using hCne
  have hsC : ∀ x n, ((T (n + 1)).1 x)⁻¹ * s x ∈ K (n + 1) := fun x n =>
    (hCmem x n _).1 (mem_iInter.1 (hs x) n)
  refine ⟨s, ?_, fun c => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_def]
    intro W hW

    have hW1 : (fun k => s x * k) ⁻¹' W ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW
    obtain ⟨m, hm⟩ := hKb _ hW1
    have hmm : (K (m + 1) : Set G) ⊆ (fun k => s x * k) ⁻¹' W :=
      fun g hg => hm (hKle m hg)
    have hloc : {y | (T (m + 1)).1 y = (T (m + 1)).1 x} ∈ 𝓝 x :=
      ((T (m + 1)).2.1.isOpen_fiber _).mem_nhds rfl
    filter_upwards [hloc] with y hy
    have h1 := hsC y m
    have h2 := hsC x m
    rw [hy] at h1
    have : (s x)⁻¹ * s y = (((T (m + 1)).1 x)⁻¹ * s x)⁻¹ * (((T (m + 1)).1 x)⁻¹ * s y) := by group
    have hk : (s x)⁻¹ * s y ∈ K (m + 1) := by
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) h1
    simpa using hmm hk
  · by_contra hne

    have hopen : IsOpen {g : G | (g : G ⧸ H) ≠ c} :=
      (isOpen_compl_singleton (x := c)).preimage continuous_quotient_mk'
    have hW1 : (fun k => s c * k) ⁻¹' {g : G | (g : G ⧸ H) ≠ c} ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hopen.mem_nhds hne
    obtain ⟨m, hm⟩ := hKb _ hW1
    obtain ⟨k, hk, hkc⟩ := (T (m + 1)).2.2 c
    have hk' : (s c)⁻¹ * ((T (m + 1)).1 c * k) ∈ K (m + 1) := by
      have h2 := hsC c m
      have : (s c)⁻¹ * ((T (m + 1)).1 c * k) = (((T (m + 1)).1 c)⁻¹ * s c)⁻¹ * k := by group
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) hk
    have := hm (hKle m hk')
    simp only [mem_preimage, mem_setOf_eq, mul_inv_cancel_left] at this
    exact this hkc

end GlobalTheory.CompanionTheory.LGroupSection
end

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_section_quotient : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G] (H : Subgroup G), IsClosed (H : Set G) → ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  first | exact @GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | exact GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | (intros; apply GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportConvolutionTriple
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportConvolutionTriple
namespace GlobalTheory.CompanionTheory.HeckeProduct

section Single

variable {G M V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem out_invariant (K : Subgroup G) (F : G → M) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (g : G) :
    F ((g : G ⧸ K).out) = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [hh]; exact hF g h h.2

noncomputable def heckeSum (π : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (u : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • π q.out u

variable (π : Representation ℂ G V) (K : Subgroup G) {f : G → ℂ}

theorem term_support_subset (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    (Function.support fun q : G ⧸ K => f q.out • π q.out u) ⊆ hf.toFinset := by
  intro q hq
  simp only [Set.Finite.coe_toFinset, Function.mem_support]
  intro h0
  exact hq (by simp [h0])

theorem heckeSum_eq_sum (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    heckeSum π K f u = ∑ q ∈ hf.toFinset, f q.out • π q.out u :=
  finsum_eq_sum_of_support_subset _ (term_support_subset π K hf u)

theorem map_heckeSum (hf : (Function.support fun q : G ⧸ K => f q.out).Finite)
    (T : V →ₗ[ℂ] V) (hT : ∀ g u, T (π g u) = π g (T u)) (u : V) :
    T (heckeSum π K f u) = heckeSum π K f (T u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [heckeSum_eq_sum π K hf, heckeSum_eq_sum π K hf, map_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [map_smul, hT]

noncomputable def heckeLin (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) : V →ₗ[ℂ] V :=
  ∑ q ∈ hf.toFinset, f q.out • π q.out

theorem heckeLin_apply (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    heckeLin π K hf u = heckeSum π K f u := by
  rw [heckeSum_eq_sum π K hf, heckeLin, LinearMap.sum_apply]
  rfl

theorem heckeSum_fixed (hf : (Function.support fun q : G ⧸ K => f q.out).Finite)
    (hl : ∀ k ∈ K, ∀ g, f (k * g) = f g) (hr : ∀ k ∈ K, ∀ g, f (g * k) = f g)
    (u : V) (hu : ∀ k ∈ K, π k u = u) (k : G) (hk : k ∈ K) :
    π k (heckeSum π K f u) = heckeSum π K f u := by
  have hF : ∀ g, ∀ c ∈ K, (fun g => f g • π g u) (g * c) = (fun g => f g • π g u) g := by
    intro g c hc
    simp only [map_mul, Module.End.mul_apply, hu c hc, hr c hc]
  have key : ∀ q : G ⧸ K, π k (f q.out • π q.out u)
      = (fun q : G ⧸ K => f q.out • π q.out u) ((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q) := by
    intro q
    have hq : (MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q = ((k * q.out : G) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h1 := out_invariant K (fun g => f g • π g u) hF (k * q.out)
    simp only [hq]
    rw [h1, map_smul, hl k hk, map_mul, Module.End.mul_apply]
  have h2 : π k (heckeSum π K f u) = ∑ᶠ q : G ⧸ K, π k (f q.out • π q.out u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [heckeSum_eq_sum π K hf, map_sum]
    refine (finsum_eq_sum_of_support_subset _ ?_).symm
    intro q hq
    refine term_support_subset π K hf u ?_
    intro h0
    exact hq (by simp only [h0, map_zero])
  rw [h2, finsum_congr key]
  exact finsum_comp_equiv (f := fun q : G ⧸ K => f q.out • π q.out u)
    (MulAction.toPerm k : Equiv.Perm (G ⧸ K))

end Single

section Product

variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]

noncomputable def cosetPairEquiv (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) :
    (G₁ ⧸ K₁) × (G₂ ⧸ K₂) ≃ (G₁ × G₂) ⧸ K₁.prod K₂ :=
  Equiv.ofBijective (fun p => (((p.1.out, p.2.out) : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂)) (by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' := QuotientGroup.eq.1 h
      rw [Subgroup.mem_prod] at h'
      have ha : (a.out : G₁ ⧸ K₁) = a'.out := QuotientGroup.eq.2 h'.1
      have hb : (b.out : G₂ ⧸ K₂) = b'.out := QuotientGroup.eq.2 h'.2
      simp only [QuotientGroup.out_eq'] at ha hb
      rw [ha, hb]
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        refine ⟨((g.1 : G₁ ⧸ K₁), (g.2 : G₂ ⧸ K₂)), ?_⟩
        obtain ⟨c₁, h₁⟩ := QuotientGroup.mk_out_eq_mul K₁ g.1
        obtain ⟨c₂, h₂⟩ := QuotientGroup.mk_out_eq_mul K₂ g.2
        refine QuotientGroup.eq.2 ?_
        rw [Subgroup.mem_prod]
        simp only [h₁, h₂, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
        constructor
        · simpa using K₁.inv_mem c₁.2
        · simpa using K₂.inv_mem c₂.2)

variable (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)

noncomputable abbrev left : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂)

noncomputable abbrev right : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂)

theorem left_right_comm (g : G₁) (h : G₂) (u : V) :
    left ρ g (right ρ h u) = right ρ h (left ρ g u) := by
  have e1 : left ρ g (right ρ h u) = ρ ((g, 1) * (1, h)) u := by
    rw [map_mul]; rfl
  have e2 : right ρ h (left ρ g u) = ρ ((1, h) * (g, 1)) u := by
    rw [map_mul]; rfl
  rw [e1, e2]; simp

theorem left_right_mul (g : G₁) (h : G₂) (u : V) :
    ρ (g, h) u = left ρ g (right ρ h u) := by
  have : ((g, h) : G₁ × G₂) = (g, 1) * (1, h) := by simp
  rw [this, map_mul]; rfl

variable {f : G₁ → ℂ} {f' : G₂ → ℂ}

theorem sum_left_right_comm (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite) (u : V) :
    heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u)
      = heckeSum (right ρ) K₂ f' (heckeSum (left ρ) K₁ f u) := by
  rw [← heckeLin_apply (left ρ) K₁ hf, ← heckeLin_apply (left ρ) K₁ hf]
  refine map_heckeSum (right ρ) K₂ hf' _ (fun h w => ?_) u
  rw [heckeLin_apply (left ρ) K₁ hf, heckeLin_apply (left ρ) K₁ hf]
  exact map_heckeSum (left ρ) K₁ hf (right ρ h) (fun g w => (left_right_comm ρ g h w).symm) w |>.symm

theorem product_sum (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g) (hr' : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f q.out.1 * f' q.out.2) • ρ q.out u
      = heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u) := by
  have hF : ∀ g, ∀ c ∈ K₁.prod K₂, (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) (g * c)
      = (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) g := by
    intro g c hc
    have hc' := Subgroup.mem_prod.1 hc
    simp only [map_mul, Module.End.mul_apply, hu c hc, Prod.fst_mul, Prod.snd_mul,
      hr c.1 hc'.1, hr' c.2 hc'.2]
  rw [← finsum_comp_equiv (cosetPairEquiv K₁ K₂)]
  have h1 : ∀ p : (G₁ ⧸ K₁) × (G₂ ⧸ K₂),
      (f ((cosetPairEquiv K₁ K₂ p).out.1) * f' ((cosetPairEquiv K₁ K₂ p).out.2)) •
        ρ (cosetPairEquiv K₁ K₂ p).out u = (f p.1.out * f' p.2.out) • ρ (p.1.out, p.2.out) u :=
    fun p => out_invariant (K₁.prod K₂) (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) hF
      (p.1.out, p.2.out)
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ hf'.toFinset) _ ?_,
    Finset.sum_product, heckeSum_eq_sum _ K₁ hf]
  · refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [heckeSum_eq_sum _ K₂ hf', map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [left_right_mul, map_smul, smul_smul]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.coe_product, Set.Finite.coe_toFinset, Set.mem_prod, Function.mem_support]
    constructor
    · intro h0; exact hp (by simp [h0])
    · intro h0; exact hp (by simp [h0])

theorem fixed_left (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hl : ∀ k ∈ K₁, ∀ g, f (k * g) = f g) (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (left ρ) K₁ f u) = heckeSum (left ρ) K₁ f u := by
  rintro ⟨c₁, c₂⟩ hc
  have hc' := Subgroup.mem_prod.1 hc
  have hu₁ : ∀ k ∈ K₁, left ρ k u = u := fun k hk =>
    hu (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  have hu₂ : right ρ c₂ u = u := hu (1, c₂) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hc'.2⟩)
  rw [left_right_mul, map_heckeSum (left ρ) K₁ hf (right ρ c₂)
    (fun g w => (left_right_comm ρ g c₂ w).symm), hu₂]
  exact heckeSum_fixed (left ρ) K₁ hf hl hr u hu₁ c₁ hc'.1

theorem fixed_right (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hl : ∀ k ∈ K₂, ∀ g, f' (k * g) = f' g) (hr : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (right ρ) K₂ f' u) = heckeSum (right ρ) K₂ f' u := by
  rintro ⟨c₁, c₂⟩ hc
  have hc' := Subgroup.mem_prod.1 hc
  have hu₁ : left ρ c₁ u = u := hu (c₁, 1) (Subgroup.mem_prod.2 ⟨hc'.1, K₂.one_mem⟩)
  have hu₂ : ∀ k ∈ K₂, right ρ k u = u := fun k hk =>
    hu (1, k) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hk⟩)
  rw [left_right_mul, heckeSum_fixed (right ρ) K₂ hf' hl hr u hu₂ c₂ hc'.2,
    map_heckeSum (right ρ) K₂ hf' (left ρ c₁) (fun h w => left_right_comm ρ c₁ h w), hu₁]

end Product

theorem product_operators_mul : ∀ (G₁ G₂ V : Type) [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ f₁' f₁'' : G₁ → ℂ) (f₂ f₂' f₂'' : G₂ → ℂ), (∀ f ∈ ({f₁, f₁', f₁''} : Set (G₁ → ℂ)), (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite ∧ ∀ k ∈ K₁, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ f ∈ ({f₂, f₂', f₂''} : Set (G₂ → ℂ)), (Function.support fun q : G₂ ⧸ K₂ => f q.out).Finite ∧ ∀ k ∈ K₂, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ v : V, (∀ k ∈ K₁, ρ (k, 1) v = v) → ∑ᶠ q : G₁ ⧸ K₁, f₁'' q.out • ρ (q.out, 1) v = ∑ᶠ q : G₁ ⧸ K₁, f₁ q.out • ρ (q.out, 1) (∑ᶠ q' : G₁ ⧸ K₁, f₁' q'.out • ρ (q'.out, 1) v)) → (∀ v : V, (∀ k ∈ K₂, ρ (1, k) v = v) → ∑ᶠ q : G₂ ⧸ K₂, f₂'' q.out • ρ (1, q.out) v = ∑ᶠ q : G₂ ⧸ K₂, f₂ q.out • ρ (1, q.out) (∑ᶠ q' : G₂ ⧸ K₂, f₂' q'.out • ρ (1, q'.out) v)) → ∀ v : V, (∀ k ∈ K₁.prod K₂, ρ k v = v) → ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁'' q.out.1 * f₂'' q.out.2) • ρ q.out v = ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁ q.out.1 * f₂ q.out.2) • ρ q.out (∑ᶠ q' : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁' q'.out.1 * f₂' q'.out.2) • ρ q'.out v) := by
  intro G₁ G₂ V _ _ _ _ ρ K₁ K₂ f₁ f₁' f₁'' f₂ f₂' f₂'' h1 h2 hA hB v hv
  obtain ⟨a, ai⟩ := h1 f₁ (by simp)
  obtain ⟨a', ai'⟩ := h1 f₁' (by simp)
  obtain ⟨a'', ai''⟩ := h1 f₁'' (by simp)
  obtain ⟨b, bi⟩ := h2 f₂ (by simp)
  obtain ⟨b', bi'⟩ := h2 f₂' (by simp)
  obtain ⟨b'', bi''⟩ := h2 f₂'' (by simp)
  have hA' : ∀ w : V, (∀ k ∈ K₁, left ρ k w = w) → heckeSum (left ρ) K₁ f₁'' w
      = heckeSum (left ρ) K₁ f₁ (heckeSum (left ρ) K₁ f₁' w) := hA
  have hB' : ∀ w : V, (∀ k ∈ K₂, right ρ k w = w) → heckeSum (right ρ) K₂ f₂'' w
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' w) := hB
  have hv₂ : ∀ k ∈ K₂, right ρ k v = v := fun k hk =>
    hv (1, k) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hk⟩)
  have hy := fixed_right ρ K₁ K₂ b' (fun k hk g => (bi' k hk g).1) (fun k hk g => (bi' k hk g).2) v hv
  have hx := fixed_right ρ K₁ K₂ b (fun k hk g => (bi k hk g).1) (fun k hk g => (bi k hk g).2) _ hy
  have hw := fixed_left ρ K₁ K₂ a' (fun k hk g => (ai' k hk g).1) (fun k hk g => (ai' k hk g).2) _ hy
  have hx₁ : ∀ k ∈ K₁, left ρ k (heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v))
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v) := fun k hk =>
    hx (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  rw [product_sum ρ K₁ K₂ a'' b'' (fun k hk g => (ai'' k hk g).2) (fun k hk g => (bi'' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a' b' (fun k hk g => (ai' k hk g).2) (fun k hk g => (bi' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a b (fun k hk g => (ai k hk g).2) (fun k hk g => (bi k hk g).2) _ hw,
    hB' v hv₂, hA' _ hx₁, sum_left_right_comm ρ K₁ K₂ a' b]

end GlobalTheory.CompanionTheory.HeckeProduct
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportConvolutionTripleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_support_convolution_triple : ∀ (G₁ G₂ V : Type) [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ f₁' f₁'' : G₁ → ℂ) (f₂ f₂' f₂'' : G₂ → ℂ), (∀ f ∈ ({f₁, f₁', f₁''} : Set (G₁ → ℂ)), (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite ∧ ∀ k ∈ K₁, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ f ∈ ({f₂, f₂', f₂''} : Set (G₂ → ℂ)), (Function.support fun q : G₂ ⧸ K₂ => f q.out).Finite ∧ ∀ k ∈ K₂, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ v : V, (∀ k ∈ K₁, ρ (k, 1) v = v) → ∑ᶠ q : G₁ ⧸ K₁, f₁'' q.out • ρ (q.out, 1) v = ∑ᶠ q : G₁ ⧸ K₁, f₁ q.out • ρ (q.out, 1) (∑ᶠ q' : G₁ ⧸ K₁, f₁' q'.out • ρ (q'.out, 1) v)) → (∀ v : V, (∀ k ∈ K₂, ρ (1, k) v = v) → ∑ᶠ q : G₂ ⧸ K₂, f₂'' q.out • ρ (1, q.out) v = ∑ᶠ q : G₂ ⧸ K₂, f₂ q.out • ρ (1, q.out) (∑ᶠ q' : G₂ ⧸ K₂, f₂' q'.out • ρ (1, q'.out) v)) → ∀ v : V, (∀ k ∈ K₁.prod K₂, ρ k v = v) → ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁'' q.out.1 * f₂'' q.out.2) • ρ q.out v = ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁ q.out.1 * f₂ q.out.2) • ρ q.out (∑ᶠ q' : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁' q'.out.1 * f₂' q'.out.2) • ρ q'.out v) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul | exact GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul | (intros; apply GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthProperty
open Polynomial

namespace GlobalTheory.CompanionTheory.UnitLattice

open PositivityTheory.Rg.Tf.Loc

variable {n : ℕ}

theorem mem_unitGL_of_integral {F : Type*} [Field F] [ValuativeRel F] (u : GL (Fin n) F)
    (h1 : ∀ i j, (u : Matrix (Fin n) (Fin n) F) i j ∈ intO F)
    (h2 : ∀ i j, ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) :
    u ∈ unitGL (n := Fin n) F := by
  have hinj : Function.Injective ((intO F).subtype) := Subtype.val_injective
  let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, h2 i j⟩
  have hA : A.map (intO F).subtype = (u : Matrix (Fin n) (Fin n) F) := by
    ext i j; rfl
  have hB : B.map (intO F).subtype = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    ext i j; rfl
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

theorem integral_of_mem_unitGL {F : Type*} [Field F] [ValuativeRel F] {u : GL (Fin n) F}
    (hu : u ∈ unitGL (n := Fin n) F) (i j : Fin n) :
    (u : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  obtain ⟨v, rfl⟩ := hu
  exact ((v : Matrix (Fin n) (Fin n) (intO F)) i j).2

theorem pow_entry_mem {F : Type*} [Field F] (S : Subring F) {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j, M i j ∈ S) (m : ℕ) : ∀ i j, (M ^ m) i j ∈ S := by
  induction m with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ m ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact S.sum_mem fun l _ => S.mul_mem (ih i l) (hM l j)

theorem aeval_entry_mem {F : Type*} [Field F] (S : Subring F) {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j, M i j ∈ S) {p : F[X]} (hp : ∀ i, p.coeff i ∈ S) (i j : Fin n) :
    (aeval M p) i j ∈ S := by
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  refine S.sum_mem fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact S.mul_mem (hp l) (pow_entry_mem S hM l i j)

theorem conj_aeval {F : Type*} [Field F] (u : GL (Fin n) F) (M : Matrix (Fin n) (Fin n) F)
    (p : F[X]) :
    ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * aeval M p * (u : Matrix (Fin n) (Fin n) F) =
      aeval (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M * (u : Matrix (Fin n) (Fin n) F)) p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.conj_pow', mul_smul_comm, smul_mul_assoc]

theorem conj_mem_unitGL {F : Type*} [Field F] [ValuativeRel F] {Γ c g : GL (Fin n) F} {p q : F[X]}
    (hp : (c : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) p)
    (hpi : ∀ i, p.coeff i ∈ intO F)
    (hq : ((c⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) q)
    (hqi : ∀ i, q.coeff i ∈ intO F)
    (hΓ : g⁻¹ * Γ * g ∈ unitGL (n := Fin n) F) :
    g⁻¹ * c * g ∈ unitGL (n := Fin n) F := by
  have hent := integral_of_mem_unitGL hΓ
  simp only [Units.val_mul] at hent
  apply mem_unitGL_of_integral
  · intro i j
    simp only [Units.val_mul]
    rw [hp, conj_aeval]
    exact aeval_entry_mem _ hent hpi i j
  · intro i j
    have : (g⁻¹ * c * g)⁻¹ = g⁻¹ * c⁻¹ * g := by group
    rw [this]
    simp only [Units.val_mul]
    rw [hq, conj_aeval]
    exact aeval_entry_mem _ hent hqi i j

theorem conj_eq_of_commute {F : Type*} [Field F] {Γ c g : GL (Fin n) F} {p : F[X]}
    (hp : (c : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) p)
    (hg : g * Γ = Γ * g) : g⁻¹ * c * g = c := by
  apply Units.ext
  have h1 : g⁻¹ * Γ * g = Γ := by rw [mul_assoc, ← hg]; group
  have h2 : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (Γ : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F) = Γ := by
    have := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1
    simpa only [Units.val_mul] using this
  simp only [Units.val_mul]
  rw [hp, conj_aeval, h2]

theorem twNorm_mem {G : Type*} [Group G] (θ : Monoid.End G) (K : Subgroup G)
    (hK : ∀ x ∈ K, θ x ∈ K) {u : G} (hu : u ∈ K) (m : ℕ) : twNorm θ m u ∈ K := by
  have hpow : ∀ i : ℕ, (θ ^ i) u ∈ K := by
    intro i
    induction i with
    | zero => simpa using hu
    | succ i ih => rw [pow_succ_apply']; exact hK _ ih
  induction m with
  | zero => simpa using K.one_mem
  | succ m ih => rw [twNorm_succ]; exact K.mul_mem ih (hpow m)

theorem exists_incl_of_fixed {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (g : GL (Fin n) E)
    (hg : sigmaGL σ g = g) : ∃ y : GL (Fin n) k, incl y = g := by
  have hfix : ∀ x : E, σ x = x → ∃ a : k, algebraMap k E a = x := by
    intro x hx
    have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact hx
    have hall : ∀ τ : E ≃ₐ[k] E, τ x = x := by
      intro τ
      have := (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have := (IsGalois.mem_bot_iff_fixed x).mpr hall
    rwa [IntermediateField.mem_bot] at this
  have hent : ∀ (h : GL (Fin n) E), sigmaGL σ h = h → ∀ i j,
      σ ((h : Matrix (Fin n) (Fin n) E) i j) = (h : Matrix (Fin n) (Fin n) E) i j := by
    intro h hh i j
    have := congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) hh
    exact this
  have hg' : sigmaGL σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  choose A hA using fun i j => hfix _ (hent g hg i j)
  choose B hB using fun i j => hfix _ (hent g⁻¹ hg' i j)
  have hinj : Function.Injective (algebraMap k E) := (algebraMap k E).injective
  have hAm : (Matrix.of A).map (algebraMap k E) = (g : Matrix (Fin n) (Fin n) E) := by
    ext i j; exact hA i j
  have hBm : (Matrix.of B).map (algebraMap k E) = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    ext i j; exact hB i j
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨Matrix.of A, Matrix.of B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hAm

theorem sigmaGL_incl {k E : Type*} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E)
    (y : GL (Fin n) k) : sigmaGL σ (incl y) = incl y := by
  apply Units.ext
  ext i j
  exact σ.commutes _

theorem incl_injective {k E : Type*} [Field k] [Field E] [Algebra k E] :
    Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := by
  intro a b hab
  apply Units.ext
  apply Matrix.map_injective (algebraMap k E).injective
  exact congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E)) hab

theorem cstable_iff_and_twCent : D0a → A1 → L4 := by
  intro hD _ k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n γ c _ hpc hqc hN
  obtain ⟨p, hp, hpi⟩ := hpc
  obtain ⟨q, hq, hqi⟩ := hqc
  have hσℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hσℓ, sigmaGL_one]
  have hstab : ∀ x ∈ unitGL (n := Fin n) E, sigmaGL σ x ∈ unitGL (n := Fin n) E :=
    fun x hx => ((hD k E hur σ hgen).2.2.2.1 σ n x).2 hx
  have hNc : twNorm (sigmaGL σ) (Module.finrank k E) c = incl γ := hN
  have hq' : (((c⁻¹)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p := by rw [inv_inv]; exact hp
  refine ⟨fun g => ⟨fun hu => ?_, fun h => ?_⟩, ?_⟩
  · have hγ : g⁻¹ * incl γ * g ∈ unitGL (n := Fin n) E := by
      have := twNorm_mem (sigmaGL σ) _ hstab hu (Module.finrank k E)
      rwa [twNorm_twConj_of_pow_eq_one _ hθ, hNc] at this
    refine ⟨?_, hγ⟩
    have hcg : g⁻¹ * c⁻¹ * g ∈ unitGL (n := Fin n) E := conj_mem_unitGL hq hqi hq' hpi hγ
    have he : g⁻¹ * sigmaGL σ g = (g⁻¹ * c⁻¹ * g) * twConj (sigmaGL σ) g c := by
      simp only [twConj]; group
    rw [he]
    exact mul_mem hcg hu
  · have hcg : g⁻¹ * c * g ∈ unitGL (n := Fin n) E := conj_mem_unitGL hp hpi hq hqi h.2
    have he : twConj (sigmaGL σ) g c = (g⁻¹ * c * g) * (g⁻¹ * sigmaGL σ g) := by
      simp only [twConj]; group
    rw [he]
    exact mul_mem hcg h.1
  · ext g
    constructor
    · intro hg
      have hcomm := twCent_commute_twNorm (sigmaGL σ) hθ c hg
      rw [hNc] at hcomm
      have hcg : g⁻¹ * c * g = c := conj_eq_of_commute hp hcomm
      have hg' : g⁻¹ * c * sigmaGL σ g = c := hg
      have hfix : sigmaGL σ g = g := by
        have h1 : g⁻¹ * c * sigmaGL σ g = g⁻¹ * c * g := by rw [hg', hcg]
        exact mul_left_cancel h1
      obtain ⟨y, rfl⟩ := exists_incl_of_fixed σ hgen g hfix
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply incl_injective (E := E)
      rw [map_mul, map_mul]
      exact hcomm
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
      have hcomm : incl y * incl γ = (incl γ : GL (Fin n) E) * incl y := by
        rw [← map_mul, ← map_mul, hy]
      have hcg := conj_eq_of_commute hp hcomm
      show (incl y)⁻¹ * c * sigmaGL σ (incl y) = c
      rw [sigmaGL_incl, hcg]

end GlobalTheory.CompanionTheory.UnitLattice
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthPropertyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_fourth_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.L4 := by
  first | exact @GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent | exact GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent | (intros; apply GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent <;> assumption)
end
end
