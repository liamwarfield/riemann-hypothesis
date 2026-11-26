module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveSublatticesGenusDefiniteLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountIsometryPairsWithGivenFixedSpace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscNResNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairsIsometryNoFixedVectorCountBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardEmbeddedHermDataIndexLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardEmbeddedHermDataIndexLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem finrank_sub_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) L ≤ Module.finrank K V := by
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have h := hs.map' L.subtype (Submodule.ker_subtype L)
  rw [LinearIndependent.iff_fractionRing (R := 𝓞 K) (K := K)] at h
  simpa using h.fintype_card_le_finrank

theorem sublat_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG) (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.Finite ∧
      (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) L := inferInstance
  have : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K L x hx
  have hsub : {N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x} ⊆
      (Submodule.map L.subtype) '' {N : Submodule (𝓞 K) L | N.toAddSubgroup.index = x} := by
    rintro N ⟨hN, hi⟩
    refine ⟨N.comap L.subtype, ?_, ?_⟩
    · exact hi
    · rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  refine ⟨(h1.image _).subset hsub, ?_⟩
  have h3 := (Set.ncard_le_ncard hsub (h1.image _)).trans (Set.ncard_image_le h1)
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x Module.finrank_pos hx
  have h5 : ((Module.finrank (𝓞 K) L : ℕ) : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast finrank_sub_le L
  calc (({N : Submodule (𝓞 K) V | N ≤ L ∧ idx L N = x}.ncard : ℕ) : ℝ)
      ≤ ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ Module.finrank (𝓞 K) L := by
        exact_mod_cast h3.trans h2
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) L :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ (((Module.finrank (𝓞 K) L : ℕ) : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem encard_isDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  intro K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD hG hg x hx
  have hfib := GlobalTheory.DegCnt.DatCount.main K V H hK hP L₀ g j D₀ hL hD hG hg
  obtain ⟨hfin, hcnt⟩ := sublat_count L₀ hL.1.fg x hx
  set S := {N : Submodule (𝓞 K) V | N ≤ L₀ ∧ idx L₀ N = x} with hS
  have hsub : {d | IsDat H g L₀ j x d} ⊆
      ⋃ La ∈ hfin.toFinset, {d | IsDat H g L₀ j x d ∧ fixLat d.2 = La} := by
    intro d hd
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    refine ⟨fixLat d.2, ⟨?_, hd.2.2.2.1⟩, hd, rfl⟩
    intro y hy
    exact (hd.2.2.1.1 hy).2
  have h1 := (Set.encard_le_encard hsub).trans (Finset.set_encard_biUnion_le _ _)
  have h2 : ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤
      ∑ La ∈ hfin.toFinset, ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) := by
    refine (ENat.toENNReal_le.2 h1).trans (le_of_eq ?_)
    exact map_sum ENat.toENNRealRingHom _ _
  refine h2.trans ((Finset.sum_le_card_nsmul _ _ _ fun La _ => hfib La x).trans ?_)
  rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  gcongr
  rw [← ENNReal.ofReal_natCast, ← Set.ncard_eq_toFinset_card S hfin]
  exact ENNReal.ofReal_le_ofReal hcnt

end GlobalTheory.DegCnt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardEmbeddedHermDataIndexLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_embedded_hermData_index_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ x : ℕ, 1 ≤ x → ((({d | IsDat H g L₀ j x d}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (((Module.finrank K V) : ℝ) + cf K) * ((x : ℝ) * D₀) ^ (3 * (2 * j + 1))) := by
  first | exact @GlobalTheory.DegCnt.encard_isDat_le | exact GlobalTheory.DegCnt.encard_isDat_le | (intros; apply GlobalTheory.DegCnt.encard_isDat_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairsIsometryNoFixedVectorCountBound
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PairNoFix

theorem encard_le_of_fibres {α β : Type} (S : Set α) (T : Set β) (f : α → β) (hf : ∀ a ∈ S, f a ∈ T)
    (c : ℝ≥0∞) (hc : ∀ b ∈ T, ((({a ∈ S | f a = b}).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((T.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun a : S => (⟨f a, hf a a.2⟩ : T))]
  refine ENNReal.tsum_le_tsum fun b => ?_
  rw [ENNReal.tsum_set_one]
  refine le_trans ?_ (hc b b.2)
  rw [← (Subtype.val_injective.encard_image _)]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.2, congrArg Subtype.val ha⟩

theorem arith (k f : ℕ) (c e : ℝ) (hc : 0 ≤ c) (x x' D q A : ℝ) (hx : 1 ≤ x) (hx' : 1 ≤ x') (hD : 1 ≤ D)
    (hq : 0 < q) (hA : 0 ≤ A) (h : 1 ≤ q ^ (2 * k * f) * D * x * x') (m : ℕ) (hm : (m : ℝ) = e) :
    (x ^ ((k : ℝ) + c) * (x * D) ^ m) * (x' ^ ((k : ℝ) + c) * (x' * D) ^ m) * A ^ (4 * k * f) ≤
      (x * x') ^ ((k : ℝ) / 2) * (x * x' * D ^ 2) ^ (c + e) * (q ^ (k * f) * A ^ (4 * f) * D * x * x') ^ k := by
  subst hm
  have x0 : 0 < x := by linarith
  have x0' : 0 < x' := by linarith
  have D0 : 0 < D := by linarith
  have h1 : 1 ≤ (x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k := by
    have hs : ((x * x') ^ ((k : ℝ) / 2)) ^ 2 = (x * x') ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have h2 : 1 ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) ^ 2 := by
      rw [mul_pow, hs]
      have : (x * x') ^ k * ((q ^ (k * f) * D) ^ k) ^ 2 = (q ^ (2 * k * f) * D * x * x') ^ k * D ^ k := by
        ring
      rw [this]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h) (one_le_pow₀ hD)
    exact (one_le_sq_iff₀ (by positivity)).1 h2
  have h3 : x ^ c * x' ^ c ≤ (x * x' * D ^ 2) ^ c := by
    rw [← Real.mul_rpow x0.le x0'.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hc
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD)
  rw [Real.rpow_add x0, Real.rpow_add x0', Real.rpow_add (by positivity : 0 < x * x' * D ^ 2)]
  simp only [Real.rpow_natCast]
  calc x ^ k * x ^ c * (x * D) ^ m * (x' ^ k * x' ^ c * (x' * D) ^ m) * A ^ (4 * k * f)
      = 1 * (x ^ c * x' ^ c) * ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by ring
    _ ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) * (x * x' * D ^ 2) ^ c *
        ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by gcongr
    _ = _ := by ring

theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx'
  rcases Set.eq_empty_or_nonempty {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} with he | ⟨p₀, hp₀, hfix⟩
  · rw [he]; simp
  have h43 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx' p₀ hp₀
  rw [hfix] at h43
  have hone : GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (⊥ : Submodule K V))
      (GlobalTheory.Mass.latIn ⊥ (fixLat p₀.1.2)) = 1 := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN
    rw [AddSubgroup.relIndex_eq_one]
    intro y _
    rw [Subsingleton.elim y 0]
    exact zero_mem _
  rw [hone, finrank_bot, Nat.sub_zero, Nat.cast_one] at h43
  have hD1 : 1 ≤ D₀ := by
    rcases Nat.eq_zero_or_pos D₀ with h | h
    · rw [h] at h43; norm_num at h43
    · exact h
  have hcf : 0 ≤ cf K := by
    unfold cf
    have : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith
  have hA := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x hx
  have hB := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x' hx'
  have hcnt := encard_le_of_fibres {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}
    ({d | IsDat H g L₀ j x d} ×ˢ {d | IsDat H g L₀ j x' d}) (fun p => (p.1, p.2.1))
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)))
    (by
      rintro ⟨d, d'⟩ ⟨hd, hd'⟩
      have h := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hPD ⊥ d'.1 d.1 hd'.1.1 hd.1.1
      rw [finrank_bot, Nat.sub_zero] at h
      refine le_trans (ENat.toENNReal_le.2 ?_) h
      refine Set.encard_le_encard_of_injOn (f := fun p => p.2.2) ?_ ?_
      · rintro ⟨a, b, η⟩ ⟨⟨hp, -⟩, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨hp.2.2.1, hp.2.2.2.1, ?_⟩
        intro y hy
        rw [(Submodule.mem_bot K).1 hy, map_zero]
      · rintro ⟨a, b, η⟩ ⟨-, he⟩ ⟨a', b', η'⟩ ⟨-, he'⟩ hη
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
        simp only at hη
        rw [hη])
  rw [Set.encard_prod, ENat.toENNReal_mul] at hcnt
  refine hcnt.trans ((mul_le_mul_left (mul_le_mul' hA hB) _).trans ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  exact arith _ _ _ _ hcf _ _ _ _ _ (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast hD1)
    (by positivity) (by positivity) h43 _ (by push_cast; ring)

end GlobalTheory.PairNoFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairsIsometryNoFixedVectorCountBoundStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairs_isometry_no_fixed_vector_count_bound : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  first | exact @GlobalTheory.PairNoFix.main | exact GlobalTheory.PairNoFix.main | (intros; apply GlobalTheory.PairNoFix.main <;> assumption)
end
end

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PairMean

section Cyclic

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

def GoodAt (A B : Submodule R W) (P : Ideal R) (v : W) : Prop :=
  ∀ b ∈ B, ∃ s, s ∉ P ∧ ∃ r : R, s • b - r • v ∈ A

theorem goodAt_comb {A B : Submodule R W} {P : Ideal R} (hP : P.IsPrime) {v w : W} {e e' : R}
    (hw : GoodAt A B P w) (hv : v ∈ B) (he : e ∈ P) (he' : e' ∉ P) : GoodAt A B P (e • v + e' • w) := by
  intro b hb
  obtain ⟨s, hs, r, h⟩ := hw v hv
  obtain ⟨s', hs', r', h'⟩ := hw b hb
  refine ⟨(e * r + s * e') * s', fun hm => ?_, r' * s, ?_⟩
  · rcases hP.mem_or_mem hm with h1 | h1
    · have : s * e' ∈ P := by simpa using P.sub_mem h1 (P.mul_mem_right r he)
      exact (hP.mem_or_mem this).elim hs he'
    · exact hs' h1
  · have := A.sub_mem (A.smul_mem (e * r + s * e') h') (A.smul_mem (r' * e) h)
    convert this using 1
    module

theorem exists_goodAt {A B : Submodule R W} (S : Finset (Ideal R)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : ∀ P ∈ S, ∃ v ∈ B, GoodAt A B P v) : ∃ v ∈ B, ∀ P ∈ S, GoodAt A B P v := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, B.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨v, hv, hg⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
      (fun Q hQ => h Q (Finset.mem_insert_of_mem hQ))
    obtain ⟨w, hw, hgw⟩ := h P (Finset.mem_insert_self _ _)
    have hP := hS P (Finset.mem_insert_self _ _)
    have hn : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hle⟩
      have := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hle
      exact hPS (this ▸ hQ)
    obtain ⟨y, hy, hyP⟩ := SetLike.not_le_iff_exists.1 hn
    obtain ⟨a, e, he, hae⟩ := hP.exists_inv hyP
    refine ⟨e • v + (a * y) • w, B.add_mem (B.smul_mem _ hv) (B.smul_mem _ hw), fun Q hQ => ?_⟩
    rcases Finset.mem_insert.1 hQ with rfl | hQ'
    · refine goodAt_comb hP.isPrime hgw hv he fun hm => hP.ne_top ?_
      rw [Ideal.eq_top_iff_one, ← hae]
      exact Q.add_mem hm he
    · have hyQ : a * y ∈ Q := Q.mul_mem_left a (Finset.inf_le (f := id) hQ' hy)
      rw [add_comm]
      refine goodAt_comb (hS Q hQ).isPrime (hg Q hQ') hw hyQ fun hm => (hS Q hQ).ne_top ?_
      rw [Ideal.eq_top_iff_one, ← hae]
      exact Q.add_mem hyQ hm

theorem cyclic_of_local [IsDedekindDomain R] {A B : Submodule R W} (hAB : A ≤ B) (c : R) (hc : c ≠ 0)
    (hcB : ∀ b ∈ B, c • b ∈ A) (h : ∀ P : Ideal R, P.IsMaximal → ∃ v ∈ B, GoodAt A B P v) :
    ∃ v, B = A ⊔ Submodule.span R {v} := by
  have h0 : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨v, hv, hg⟩ := exists_goodAt (A := A) (B := B)
    ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})).toFinset.filter fun P => P.IsMaximal)
    (fun P hP => (Finset.mem_filter.1 hP).2) (fun P hP => h P (Finset.mem_filter.1 hP).2)
  refine ⟨v, le_antisymm (fun b hb => ?_) (sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).2 hv))⟩
  let I : Ideal R := (A ⊔ Submodule.span R {v}).comap (LinearMap.toSpanSingleton R W b)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hne
    have hcP : c ∈ P := hle (Submodule.mem_sup_left (hcB b hb))
    obtain ⟨s, hs, r, hr⟩ := hg P (Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2
      ((Ideal.mem_normalizedFactors_iff h0).2 ⟨hP.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hcP⟩), hP⟩) b hb
    refine hs (hle ?_)
    change s • b ∈ A ⊔ Submodule.span R {v}
    rw [← sub_add_cancel (s • b) (r • v)]
    exact Submodule.add_mem_sup hr (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using this

end Cyclic

section Lat

open Formalism.HermitianLatticesTheory GlobalTheory.Mass

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem genBy_of_genus (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) {M N : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) (hN : N ∈ genus h M) (hNd : N ≤ Formalism.HermitianLatticesTheory.dual h N) (h0 : discN h N ≠ 0)
    (t : V) (ht : t ∈ Formalism.HermitianLatticesTheory.dual h M) (htM : ∀ y ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ r : 𝓞 K, y - r • t ∈ M) :
    GenBy (Formalism.HermitianLatticesTheory.dual h N) N 1 := by
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨v, hv⟩ := cyclic_of_local hNd (discN h N : 𝓞 K) (by exact_mod_cast h0) (fun x hx => by
      rw [Nat.cast_smul_eq_nsmul]
      exact AddSubgroup.nsmul_index_mem
        (H := N.toAddSubgroup.addSubgroupOf (Formalism.HermitianLatticesTheory.dual h N).toAddSubgroup) ⟨x, hx⟩) (fun P hP => by
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg M
    have b1 := (ld (gmap g M) (a5.2 hM).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    have k1 := key _ _ hgL
    have k2 := key (Formalism.HermitianLatticesTheory.dual h M) (Formalism.HermitianLatticesTheory.dual h N) (by
      rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (Formalism.HermitianLatticesTheory.dual h M)).2.1 P])
    have up : ∀ (A : Submodule (𝓞 K) V) x, x ∈ A → x ∈ locS P.primeCompl A :=
      fun A x hx => ⟨1, one_mem _, by rwa [one_smul]⟩
    obtain ⟨s₀, hs₀, hv⟩ : g t ∈ locS P.primeCompl (Formalism.HermitianLatticesTheory.dual h N) := k2 ▸ ⟨t, up _ _ ht, rfl⟩
    refine ⟨_, hv, fun b hb => ?_⟩
    obtain ⟨y, ⟨s, hs, hy⟩, hyb⟩ : b ∈ gmap g (locS P.primeCompl (Formalism.HermitianLatticesTheory.dual h M)) := k2 ▸ up _ _ hb
    obtain ⟨r, hr⟩ := htM _ hy
    obtain ⟨s', hs', ha⟩ : ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) (s • y - r • t) ∈ locS P.primeCompl N :=
      k1 ▸ ⟨_, up _ _ hr, rfl⟩
    refine ⟨s₀ * s' * s, mul_mem (mul_mem hs₀ hs') hs, s' * r, ?_⟩
    rw [map_sub, map_smul, map_smul, hyb] at ha
    have := N.smul_mem s₀ ha
    convert this using 1
    change _ = s₀ • s' • (s • b - r • g t)
    module)
  exact ⟨{v}, by simp, by simpa using hv⟩

omit [NumberField K] in
theorem discN_top (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    discN (hRes h ⊤) (latIn ⊤ L) = discN h L := by
  have e : Formalism.HermitianLatticesTheory.dual (hRes h ⊤) (latIn ⊤ L) = latIn ⊤ (Formalism.HermitianLatticesTheory.dual h L) := by
    ext x
    change _ ↔ (x : V) ∈ Formalism.HermitianLatticesTheory.dual h L
    rw [isomAct_mem_dual, isomAct_mem_dual]
    exact ⟨fun a y hy => a ⟨y, trivial⟩ hy, fun a y hy => a y hy⟩
  unfold discN
  rw [e]
  let f : (⊤ : Submodule K V) →+ V := ((⊤ : Submodule K V).subtype : (⊤ : Submodule K V) →+ V)
  change (L.toAddSubgroup.comap f).relIndex ((Formalism.HermitianLatticesTheory.dual h L).toAddSubgroup.comap f) = _
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (fun y => ⟨⟨y, trivial⟩, rfl⟩)]
  rfl

theorem isIntLat_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L)
    (U : Submodule K V) : IsIntLat (hRes h U) (latIn U L) := by
  haveI : Submodule.IsLattice K (latIn U L) := by
    apply Submodule.IsLattice.of_fg K
    apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype
    exact hL.1.fg.of_le (Submodule.map_comap_le _ _)
  refine ⟨⟨?_⟩, fun x hx y hy => hL.2 x hx y hy⟩
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨a, hax⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ (x : V)
    (show (x : V) ∈ Submodule.span K (L : Set V) by rw [hL.1.span_eq_top]; trivial)
  rw [Submodule.span_eq] at hax
  have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using nonZeroDivisors.coe_ne_zero a
  rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
  exact Submodule.subset_span hax

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem pd_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  constructor <;>
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

theorem discN_res_ne_zero [FiniteDimensional K V] (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hp : PD h) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L) (U : Submodule K V) :
    discN (hRes h U) (latIn U L) ≠ 0 :=
  (GlobalTheory.Mass.DiscOrder.main K U (hRes h U) hK ⟨fun x y => hs.eq (x : V) (y : V)⟩
    (pd_nondeg _ fun τ x hx => hp τ (x : V) (fun e => hx (Subtype.ext e))) _ (isIntLat_latIn h hL U)).1

theorem of_equiv (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    discN h L = T ^ Module.finrank ℚ K ∧
      ∃ t ∈ Formalism.HermitianLatticesTheory.dual h L, ∀ y ∈ Formalism.HermitianLatticesTheory.dual h L, ∃ r : 𝓞 K, y - r • t ∈ L := by
  constructor
  · unfold discN
    rw [GlobalTheory.Mass.DiscOrder.idxN_eq_card, Nat.card_congr e.toEquiv, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  · obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    refine ⟨t, t.2, fun y hy => ?_⟩
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨y, hy⟩))
    refine ⟨r, ?_⟩
    have : (Submodule.Quotient.mk ⟨y, hy⟩ : ↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) =
        Submodule.Quotient.mk (r • t) := by
      rw [Submodule.Quotient.mk_smul, ht, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, hr,
        LinearEquiv.symm_apply_apply]
    have h2 := (Submodule.Quotient.eq _).1 this
    exact h2

end Lat

section Count

theorem encard_fibres_le {α β : Type} (S : Set α) (φ : α → β) (P : Set β) (B : ℝ≥0∞)
    (h : ∀ U ∈ P, ((({p ∈ S | φ p = U}).encard : ℕ∞) : ℝ≥0∞) ≤ B) :
    ((({p ∈ S | φ p ∈ P}).encard : ℕ∞) : ℝ≥0∞) ≤ ((P.encard : ℕ∞) : ℝ≥0∞) * B := by
  have e : {p ∈ S | φ p ∈ P} = ⋃ U ∈ P, {p ∈ S | φ p = U} := by
    ext p
    simp [and_comm]
  rw [e, ← ENNReal.tsum_set_one, ← ENNReal.tsum_set_const]
  refine (ENNReal.tsum_biUnion_le_tsum (fun _ => 1) _ _).trans (ENNReal.tsum_le_tsum fun U => ?_)
  rw [ENNReal.tsum_set_one]
  exact h U U.2

theorem encard_cover_le {α ι : Type} (S A₁ A₂ : Set α) (I : Finset ι) (F : ι → Set α)
    (h : S ⊆ A₁ ∪ A₂ ∪ ⋃ i ∈ I, F i) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ (A₁.encard : ℕ∞) + (A₂.encard : ℕ∞) + ∑ i ∈ I, (((F i).encard : ℕ∞) : ℝ≥0∞) := by
  have h1 : S.encard ≤ A₁.encard + A₂.encard + (⋃ i ∈ I, F i).encard :=
    (Set.encard_le_encard h).trans ((Set.encard_union_le _ _).trans (by
      gcongr; exact Set.encard_union_le _ _))
  have h2 : (((⋃ i ∈ I, F i).encard : ℕ∞) : ℝ≥0∞) ≤ ∑ i ∈ I, (((F i).encard : ℕ∞) : ℝ≥0∞) := by
    simp only [← ENNReal.tsum_set_one]
    exact ENNReal.tsum_biUnion_le (fun _ => 1) I F
  calc ((S.encard : ℕ∞) : ℝ≥0∞) ≤ (A₁.encard : ℕ∞) + (A₂.encard : ℕ∞) + ((⋃ i ∈ I, F i).encard : ℕ∞) := by
        exact_mod_cast h1
    _ ≤ _ := by gcongr

theorem orbSum_le_lin {G α ι : Type} [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) (c : ℝ≥0∞)
    (I : Finset ι) (M : ι → α → ℝ≥0∞) (B : ι → ℝ≥0∞) (h : ∀ a ∈ X, N a ≤ c + ∑ i ∈ I, M i a * B i) :
    GlobalTheory.Mass.orbSum G X N ≤ GlobalTheory.Mass.orbMass G X * c + ∑ i ∈ I, GlobalTheory.Mass.orbSum G X (M i) * B i := by
  unfold GlobalTheory.Mass.orbMass GlobalTheory.Mass.orbSum
  simp only [← ENNReal.tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun q => ?_
  refine (mul_le_mul_right (h _ q.2) _).trans (le_of_eq ?_)
  simp only [mul_add, Finset.mul_sum, mul_one, mul_assoc]

end Count

theorem mid_bound (m A c D X Y : ℝ) (g n s k f j x x' : ℕ) (hm : 0 ≤ m) (hA : 0 ≤ A) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hX : X = (x : ℝ) * x') (hX1 : 1 ≤ X) (hY : Y = X * D ^ 2) (hg : 2 ≤ g) (hn : 1 ≤ n) (hnD : (n : ℝ) ≤ D * X)
    (hs : s ≤ k) :
    m * (A * 16 ^ (s * k * f)) * ((n : ℝ) / D) ^ ((k : ℝ) / 2) * ((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) *
      (((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2) * X ^ (2 * (s : ℝ) + 2 * c + 1) *
        Y ^ (3 * (2 * j + 1)) * ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f)) ≤
    m * X ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A *
      ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s := by
  have n0 : (0 : ℝ) < n := by exact_mod_cast hn
  have g0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have D0 : 0 < D := by linarith
  have X0 : 0 < X := by linarith
  have hXY : X ≤ Y := by rw [hY]; exact le_mul_of_one_le_right X0.le (one_le_pow₀ hD)
  have Y0 : 0 < Y := by linarith
  have e1 : ((n : ℝ) / D) ^ ((k : ℝ) / 2) * ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2) =
      (2 / (g : ℝ)) ^ (s * k * f) * X ^ ((k : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : (n : ℝ) / D * ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) = (2 / (g : ℝ)) ^ (2 * s * f) * X := by
      rw [hX]; field_simp
    rw [this, Real.mul_rpow (by positivity) X0.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast]
    congr 2
    push_cast
    ring
  have b1 : ((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) ≤ Y ^ (5 * (s : ℝ) + 5 + 2 * c) :=
    Real.rpow_le_rpow (by positivity) (by rw [hY]; nlinarith) (by positivity)
  have b2 : X ^ (2 * (s : ℝ) + 2 * c + 1) ≤ Y ^ (2 * (s : ℝ) + 2 * c + 1) :=
    Real.rpow_le_rpow X0.le hXY (by positivity)
  have b3 : ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by gcongr
  have e2 : Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1)) =
      Y ^ (6 * (j : ℝ) + 9 + 4 * c) * (Y ^ 7) ^ s := by
    rw [← pow_mul, ← Real.rpow_natCast Y (3 * _), ← Real.rpow_natCast Y (7 * _), ← Real.rpow_add Y0,
      ← Real.rpow_add Y0, ← Real.rpow_add Y0]
    congr 1
    push_cast
    ring
  have e3 : (16 : ℝ) ^ (s * k * f) * (2 / (g : ℝ)) ^ (s * k * f) = ((32 / (g : ℝ)) ^ (k * f)) ^ s := by
    rw [← mul_pow, ← pow_mul]
    congr 1 <;> ring
  have e4 : ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) = (((4 * k * f : ℕ) : ℝ) ^ (4 * f)) ^ s := by
    rw [← pow_mul]; congr 1; ring
  calc _ = m * A * 16 ^ (s * k * f) * (((n : ℝ) / D) ^ ((k : ℝ) / 2) *
        ((2 / (g : ℝ)) ^ (2 * s * f) * D * x * x' / n) ^ ((k : ℝ) / 2)) *
        (((n : ℝ) * D) ^ (5 * (s : ℝ) + 5 + 2 * c) * X ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f) := by ring
    _ ≤ m * A * 16 ^ (s * k * f) * ((2 / (g : ℝ)) ^ (s * k * f) * X ^ ((k : ℝ) / 2)) *
        (Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by rw [e1]; gcongr
    _ = m * X ^ ((k : ℝ) / 2) * A * ((16 : ℝ) ^ (s * k * f) * (2 / (g : ℝ)) ^ (s * k * f)) *
        (Y ^ (5 * (s : ℝ) + 5 + 2 * c) * Y ^ (2 * (s : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1))) *
        ((4 * k * f : ℕ) : ℝ) ^ (4 * s * f) := by ring
    _ = _ := by rw [e2, e3, e4, mul_pow, mul_pow]; ring

theorem top_bound (c D X Y : ℝ) (g k f j x x' : ℕ) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hX : X = (x : ℝ) * x') (hX1 : 1 ≤ X) (hY : Y = X * D ^ 2) :
    ((2 / (g : ℝ)) ^ (2 * 0 * f) * D * x * x' / D) ^ ((k : ℝ) / 2) * X ^ (2 * ((0 : ℕ) : ℝ) + 2 * c + 1) *
        Y ^ (3 * (2 * j + 1)) * ((4 * 0 * f : ℕ) : ℝ) ^ (4 * 0 * f) ≤
      X ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * c) := by
  have D0 : 0 < D := by linarith
  have X0 : 0 < X := by linarith
  have hXY : X ≤ Y := by rw [hY]; exact le_mul_of_one_le_right X0.le (one_le_pow₀ hD)
  have Y0 : 0 < Y := by linarith
  have e : (2 / (g : ℝ)) ^ (2 * 0 * f) * D * x * x' / D = X := by rw [hX]; simp; field_simp
  rw [e]
  simp only [mul_zero, zero_mul, pow_zero, mul_one, Nat.cast_zero, zero_add, mul_assoc]
  gcongr
  calc _ ≤ Y ^ (2 * c + 1) * Y ^ (3 * (2 * j + 1)) := by gcongr
    _ = Y ^ (2 * c + 1 + (3 * (2 * j + 1) : ℕ)) := by rw [Real.rpow_add Y0 (2 * c + 1), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)


set_option maxHeartbeats 800000 in
theorem main : MinkowskiBound → GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ (g j x x' : ℕ) (Y : ℝ), 2 ≤ g → 1 ≤ x → 1 ≤ x' → Y = (x : ℝ) * x' * D₀ ^ 2 → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((Trip H g L j x x').encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * ((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) * (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * (∑ s ∈ Finset.Ico 1 (Module.finrank K V), ((32 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * Y ^ 7) ^ s) + ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V))) := by
  intro hMk hMax hSi K V _ _ _ _ _ _ _ _ H hK hO hv hpd hk T L₀ Mb hT hTP hL₀ he hMb D₀ hD₀ g j x x' Y hg hx hx' hY
  have hSC := GlobalTheory.T.mean_primitiveSublattices_genus_definiteLattice hMax hSi K V H hK hO hv hpd hk T L₀ Mb hT hTP hL₀ he hMb D₀ hD₀
  obtain ⟨e⟩ := he
  have hs := flip_isSymm H
  have hnd := pd_nondeg _ hpd
  obtain ⟨hd, t, ht, htM⟩ := of_equiv _ L₀ T e
  rw [(GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex K hK.1).1] at hd
  obtain ⟨hmass, hm0, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V H.B.flip hK hs hpd L₀ hL₀.1
  have hgen := (GlobalTheory.Mass.DiscOrder.main K V H.B.flip hK hs hnd L₀ hL₀).2.2.2.1
  set k := Module.finrank K V with hkdef
  set f := Formalism.HermitianLatticesTheory.fDeg K with hf
  set m := Formalism.HermitianLatticesTheory.mass H.B.flip L₀ with hm
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = T ^ (2 * f) := ⟨_, rfl⟩
  rw [← hD] at hd
  have hDD : D₀ = D := by rw [hD₀, hD]; push_cast; rfl
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_pow _ _ hT.pos
  subst hDD
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hc : 0 ≤ cf K := add_nonneg zero_le_one (Real.logb_nonneg one_lt_two (by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)))
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  have hA : 0 ≤ Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f := by positivity
  have hX1 : (1 : ℝ) ≤ (x : ℝ) * x' := by exact_mod_cast Nat.mul_pos hx hx'
  have hY1 : (D : ℝ) * ((x : ℝ) * x') ≤ Y := by rw [hY]; nlinarith [mul_nonneg (sub_nonneg.2 hX1) (sub_nonneg.2 hD1')]
  have hY2 : 1 ≤ Y := le_trans (one_le_mul_of_one_le_of_one_le hD1' hX1) hY1
  have Y0 : 0 < Y := by linarith
  set c := cf K with hcdef
  set Z := ((x : ℝ) * x') ^ ((k : ℝ) / 2) with hZ
  have Z0 : 0 ≤ Z := by positivity
  set Pk := ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D * x * x') ^ k with hPk
  have Pk0 : 0 ≤ Pk := by positivity
  let I : Finset (ℕ × ℕ) := Finset.Ico 1 k ×ˢ Finset.Icc 1 (D * x * x')
  let B : ℕ × ℕ → ℝ := fun i => ((2 / (g : ℝ)) ^ (2 * i.1 * f) * D * x * x' / i.2) ^ ((k : ℝ) / 2) *
    ((x : ℝ) * x') ^ (2 * (i.1 : ℝ) + 2 * c + 1) * Y ^ (3 * (2 * j + 1)) * ((4 * i.1 * f : ℕ) : ℝ) ^ (4 * i.1 * f)
  have h1 := orbSum_le_lin (G := Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀)
    (fun L => (((Trip H g L j x x').encard : ℕ∞) : ℝ≥0∞))
    (ENNReal.ofReal (Z * Y ^ (6 * (j : ℝ) + 10 + 4 * c) * (1 + Pk))) I
    (fun i L => (((GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2).encard : ℕ∞) : ℝ≥0∞))
    (fun i => ENNReal.ofReal (B i)) (by
      intro L hL
      obtain ⟨hLi, hLd⟩ := hgen L hL
      rw [hd] at hLd
      have hG : GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L) L 1 := genBy_of_genus _ hs hL₀.1.toIsLattice hL
        (fun x hx => (Formalism.HermitianLatticesTheory.isomAct_mem_dual _ L x).2 fun y hy => hLi.2 y hy x hx)
        (by rw [hLd]; omega) t ht htM
      have ps := fun s n U => GlobalTheory.T.count_isometry_pairs_with_given_fixed_space hMk K V H hK hpd L g j D hLi hLd hG hg x x' s n U hx hx'
      have pk := GlobalTheory.T.pairs_isometry_no_fixed_vector_count_bound hMk K V H hK hpd L g j D hLi hLd hG hg x x' hx hx'
      rw [← hY] at ps pk
      refine (encard_cover_le _ {p ∈ Trip H g L j x x' | fixSp p.2.2 = ⊤}
        {p ∈ Trip H g L j x x' | fixSp p.2.2 = ⊥} I
        (fun i => {p ∈ Trip H g L j x x' | fixSp p.2.2 ∈ GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2}) ?_).trans ?_
      · intro p hp
        by_cases h1 : fixSp p.2.2 = ⊤
        · exact Or.inl (Or.inl ⟨hp, h1⟩)
        by_cases h2 : fixSp p.2.2 = ⊥
        · exact Or.inl (Or.inr ⟨hp, h2⟩)
        have l1 : Module.finrank K (fixSp p.2.2) < k := Submodule.finrank_lt h1
        have l2 : Module.finrank K (fixSp p.2.2) ≠ 0 := fun e => h2 (Submodule.finrank_eq_zero.1 e)
        have l3 := Nat.one_le_iff_ne_zero.2 (discN_res_ne_zero hK _ hs hpd hLi (fixSp p.2.2))
        have l4 := ps (k - Module.finrank K (fixSp p.2.2)) _ (fixSp p.2.2) l3 (by omega) rfl
        refine Or.inr (Set.mem_biUnion (x := (k - Module.finrank K (fixSp p.2.2),
          GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (fixSp p.2.2)) (GlobalTheory.Mass.latIn (fixSp p.2.2) L))) ?_
          ⟨hp, by simp only; omega, rfl⟩)
        simp only [I, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico, Finset.mem_Icc]
        refine ⟨by omega, l3, ?_⟩
        by_contra hn
        rw [if_neg (fun a => hn (by exact_mod_cast a))] at l4
        have : ({q ∈ Trip H g L j x x' | fixSp q.2.2 = fixSp p.2.2}).encard = 0 := by simpa using l4
        exact (Set.eq_empty_iff_forall_notMem.1 (Set.encard_eq_zero.1 this)) p ⟨hp, rfl⟩
      · refine add_le_add ?_ (Finset.sum_le_sum fun i hi => encard_fibres_le _ _ _ _ fun U hU => ?_)
        · have p0 := ps 0 D ⊤ hD1 (by simp) ((discN_top _ _).trans hLd)
          rw [if_pos (by nlinarith)] at p0
          rw [mul_add, mul_one, ENNReal.ofReal_add (by positivity) (by positivity)]
          refine add_le_add (p0.trans (ENNReal.ofReal_le_ofReal
            (top_bound c D _ Y g k f j x x' hc hD1' rfl hX1 hY))) (pk.trans (ENNReal.ofReal_le_ofReal ?_))
          have : Y ^ (c + 3 * (2 * (j : ℝ) + 1)) ≤ Y ^ (6 * (j : ℝ) + 10 + 4 * c) :=
            Real.rpow_le_rpow_of_exponent_le hY2 (by linarith)
          change Z * _ * Pk ≤ _
          gcongr
        · simp only [I, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hi
          have p1 := ps i.1 i.2 U hi.2.1 (by rw [hU.1]; omega) hU.2
          rw [if_pos (by exact_mod_cast hi.2.2)] at p1
          exact p1)
  refine h1.trans ?_
  rw [← hmass, ← ENNReal.ofReal_mul hm0.le]
  set C : ℕ → ℝ := fun s => ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s with hC
  have C0 : ∀ s, 0 ≤ C s := fun s => pow_nonneg (by positivity) _
  set A := Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f with hAdef
  have h2 : ∑ i ∈ I, GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀)
      (fun L => (((GlobalTheory.Mass.primSp H.B.flip L (k - i.1) i.2).encard : ℕ∞) : ℝ≥0∞)) * ENNReal.ofReal (B i) ≤
      ∑ i ∈ I, ENNReal.ofReal (m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * C i.1) := by
    refine Finset.sum_le_sum fun i hi => ?_
    simp only [I, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hi
    refine (mul_le_mul_left (hSC i.1 i.2 hi.1.1 hi.1.2 hi.2.1) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mid_bound m A c D _ Y g i.2 i.1 k f j x x' hm0.le hA hc hD1' rfl hX1 hY hg
      hi.2.1 (by rw [← mul_assoc]; exact_mod_cast hi.2.2) hi.1.2.le)
  refine (add_le_add_right h2 _).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := C0 i.1; positivity),
    ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by have := C0 i.1; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : ∑ i ∈ I, m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * C i.1 =
      (D * ((x : ℝ) * x')) * (m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * ∑ s ∈ Finset.Ico 1 k, C s) := by
    rw [Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [mul_assoc]
  have e2 : Y ^ (6 * (j : ℝ) + 10 + 4 * c) = Y * Y ^ (6 * (j : ℝ) + 9 + 4 * c) := by
    rw [← Real.rpow_one_add' Y0.le (by positivity)]
    congr 1
    ring
  have S0 : 0 ≤ ∑ s ∈ Finset.Ico 1 k, C s := Finset.sum_nonneg fun s _ => C0 s
  have b := mul_le_mul_of_nonneg_right hY1
    (show 0 ≤ m * Z * Y ^ (6 * (j : ℝ) + 9 + 4 * c) * A * ∑ s ∈ Finset.Ico 1 k, C s by positivity)
  rw [e1, e2]
  refine (add_le_add_right b _).trans (le_of_eq ?_)
  ring

end GlobalTheory.DegCnt.PairMean
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBound
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairsRow

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  intro hMax hSi hHost hLat D large₂ X Y u hStd W HW hEmb hk hpd Λ hΛ x x' hx hx'
  obtain ⟨hK, -, -, hv1, -, -, -, -, -, -, -, hg, hT⟩ := hHost D large₂ hStd
  have hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [(hHost D large₂ hStd).2.2.1]; exact hv1
  obtain ⟨hTp, hTP⟩ := hT u
  obtain ⟨hI, he⟩ := hLat D large₂ X Y u hStd W HW hEmb Λ hΛ
  have hk3 : 3 ≤ Module.finrank D.host.E W := by
    rw [hk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have : FiniteDimensional D.host.E W := Module.finite_of_finrank_pos (by omega)
  have h := GlobalTheory.DegCnt.PairMean.main Formalism.MainNotions.KappaEndpoints.mk_core hMax hSi D.host.E W HW hK
    (GlobalTheory.OrthoLattice.hasOrtho D.host.E hK) hv hpd hk3 (Tu D u) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) _ hTp hTP hI he rfl
    _ rfl (gS D) D.R.rS x x' _ hg hx hx' rfl
  rw [hk] at h
  refine h.trans (le_of_eq ?_)
  unfold GlobalTheory.DegAsm.pairBd
  simp only [mul_assoc]

end GlobalTheory.PairsRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBoundStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  first | exact @GlobalTheory.PairsRow.main | exact GlobalTheory.PairsRow.main | (intros; apply GlobalTheory.PairsRow.main <;> assumption)
end
