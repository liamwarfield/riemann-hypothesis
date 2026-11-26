module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.LiftCoker

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem map_mem_A (f : O⟦X⟧) : PowerSeries.map (algebraMap O K) f ∈ A O K := by
  rw [← coe_equivA]
  exact (equivA O K f).2


variable (O K) in
def colon {ι κ : Type} [Fintype ι] (G : Matrix κ ι K⟦X⟧) : Ideal O⟦X⟧ where
  carrier := {α | ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
    ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m}
  add_mem' {α β} hα hβ w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    obtain ⟨m', hm', h'⟩ := hβ w hw
    exact ⟨m + m', fun j => add_mem (hm j) (hm' j), by rw [map_add (f := _), add_smul, h, h', Matrix.mulVec_add]⟩
  zero_mem' w _ := ⟨0, fun _ => zero_mem _, by simp⟩
  smul_mem' c α hα w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    refine ⟨PowerSeries.map (algebraMap O K) c • m, fun j => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hm j)
    · rw [smul_eq_mul, map_mul, mul_smul, h, Matrix.mulVec_smul]

theorem mem_colon {ι κ : Type} [Fintype ι] {G : Matrix κ ι K⟦X⟧} {α : O⟦X⟧} :
    α ∈ colon O K G ↔ ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
      ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m := Iff.rfl

end GlobalTheory.LiftCoker
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEn
open scoped PowerSeries Pointwise

namespace GlobalTheory.InertiaEigenvalues.PowerSeriesFree

theorem coeff_term {O : Type} [CommRing O] (l : ℕ) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (j m : ℕ) (g : O⟦X⟧) :
    PowerSeries.coeff m (PowerSeries.X ^ j * φ g) =
      if j ≤ m ∧ l ∣ (m - j) then PowerSeries.coeff ((m - j) / l) g else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : j ≤ m
  · simp only [h, true_and, if_true]
    exact hφ g (m - j)
  · simp [h]

theorem coeff_sum {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (g : Fin l → O⟦X⟧) (m : ℕ) :
    PowerSeries.coeff m (∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j)) =
      PowerSeries.coeff (m / l) (g ⟨m % l, Nat.mod_lt _ (by omega)⟩) := by
  have hl0 : 0 < l := by omega
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rw [Finset.sum_eq_single (⟨m % l, Nat.mod_lt _ hl0⟩ : Fin l)]
  · rw [coeff_term l φ hφ]
    have h1 : m % l ≤ m := Nat.mod_le _ _
    have h2 : l ∣ m - m % l := by
      have := Nat.div_add_mod m l
      exact ⟨m / l, by omega⟩
    have h3 : (m - m % l) / l = m / l := by
      have := Nat.div_add_mod m l
      rw [show m - m % l = l * (m / l) by omega]
      exact Nat.mul_div_cancel_left _ hl0
    simp only [h1, h2, and_self, if_true, h3]
  · intro j _ hj
    rw [coeff_term l φ hφ]
    rw [if_neg]
    rintro ⟨hjm, k, hk⟩
    apply hj
    ext
    simp only
    have hjl := j.isLt
    have : m = l * k + j.val := by omega
    rw [this, Nat.mul_add_mod]
    exact (Nat.mod_eq_of_lt hjl).symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem main : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  intro O _ l hl φ hφ f
  have hl0 : 0 < l := by omega
  refine ⟨fun j => PowerSeries.mk (fun n => PowerSeries.coeff (n * l + j.val) f), ?_, ?_⟩
  · ext m
    rw [coeff_sum l hl φ hφ, PowerSeries.coeff_mk]
    simp only
    rw [Nat.div_add_mod']
  · intro g hg
    funext j
    ext n
    rw [PowerSeries.coeff_mk, hg, coeff_sum l hl φ hφ]
    have hj := j.isLt
    have e1 : (n * l + j.val) / l = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl0, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (n * l + j.val) % l = j.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [e1, e2]

end GlobalTheory.InertiaEigenvalues.PowerSeriesFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  first | exact @GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | exact GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main | (intros; apply GlobalTheory.InertiaEigenvalues.PowerSeriesFree.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVariablePowSmulEqZeroOfFiniteLength
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVariablePowSmulEqZeroOfFiniteLength
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.UPow

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem isUnit_one_add_mul_uIn (f : A O K) : IsUnit (1 + f * uIn (A O K)) := by
  set g := (equivA O K).symm (1 + f * uIn (A O K))
  have hg : equivA O K g = 1 + f * uIn (A O K) := by simp [g]
  have hc : constantCoeff g = 1 := by
    apply IsUnitBall.inj (O := O) (K := K)
    have h1 := congrArg (fun x : A O K => constantCoeff (x : K⟦X⟧)) hg
    simp only [coe_equivA] at h1
    rw [map_one]
    have h2 : algebraMap O K (constantCoeff g) = constantCoeff ((PowerSeries.map (algebraMap O K)) g) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map]
    rw [h2, h1]
    simp
  have hu : IsUnit g := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hc]
    exact isUnit_one
  rw [← hg]
  exact hu.map (equivA O K)

theorem exists_uIn_pow_smul_eq_zero : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M →
    ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  intro O K _ _ _ _ _ M _ _ hM
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hM
  set I : Ideal (A O K) := Ideal.span {uIn (A O K)}
  let F : ℕ →o (Submodule (A O K) M)ᵒᵈ :=
    ⟨fun k => OrderDual.toDual (I ^ k • (⊤ : Submodule (A O K) M)), fun i j hij =>
      Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have hstab : I ^ n • (⊤ : Submodule (A O K) M) = I • (I ^ n • (⊤ : Submodule (A O K) M)) := by
    have : I ^ n • (⊤ : Submodule (A O K) M) = I ^ (n + 1) • (⊤ : Submodule (A O K) M) :=
      OrderDual.toDual_inj.1 (hn (n + 1) (Nat.le_succ n))
    rw [← Submodule.mul_smul, ← pow_succ', ← this]
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (I ^ n • (⊤ : Submodule (A O K) M)) (IsNoetherian.noetherian _) hstab.le
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 hr
  have hru : IsUnit r := by
    have : r = 1 + f * uIn (A O K) := by rw [hf]; ring
    rw [this]
    exact isUnit_one_add_mul_uIn f
  refine ⟨n, fun x => ?_⟩
  have hmem : (uIn (A O K)) ^ n • x ∈ I ^ n • (⊤ : Submodule (A O K) M) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) trivial
  have h0 := hr0 _ hmem
  obtain ⟨v, rfl⟩ := hru
  have := congrArg (fun y => ((v⁻¹ : (A O K)ˣ) : A O K) • y) h0
  simpa [smul_smul] using this

end GlobalTheory.UPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVariablePowSmulEqZeroOfFiniteLengthStatement
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variable_pow_smul_eq_zero_of_finiteLength : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M → ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  first | exact @GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero | exact GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero | (intros; apply GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealMapExpandLeFrobeniusStatement
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_map_expand_le_frobenius : ∀ (O K : Type)
    [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤
      colon (O := O) (K := K) (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => hα (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpand
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpand
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

noncomputable section

namespace GlobalTheory.LiftCoker

theorem map_decomp_frob {O K : Type} [CommRing O] [NormedField K] [Algebra O K] (l : ℕ) [Fact l.Prime]
    {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
    PowerSeries.map (algebraMap O K) f =
      ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_X, map_expand]
  rfl

theorem colon_map_frob_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    colon (O := O) (K := K) (G.map (frob K l)) ≤
      (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 _ (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧, f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (frob K l) (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob (K := K) l hb
  have key : ∀ j, b j ∈ colon (O := O) (K := K) G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob l (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm

  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))

end GlobalTheory.LiftCoker
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpandStatement
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_frobenius_le_map_expand :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
      [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ]
      (G : Matrix κ ι K⟦X⟧),
      colon (O := O) (K := K) (G.map (frob K l)) ≤
        (colon (O := O) (K := K) G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  exact @_root_.GlobalTheory.LiftCoker.colon_map_frob_le
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobenius
noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

theorem E_pow_mul_mem_colon_frob (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a) :
    ∀ α ∈ colon O K (F.mat τ),
      (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  intro α hα w hw
  set x := D₂.mx τ *ᵥ w with hxdef
  have hx : x ∈ D₂.Lcomp τ := D₂.mem_extc.2 ⟨w, hw, rfl⟩
  have hxL : (Pi.single τ x : Vec K a κ) ∈ D₂.L := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      simpa using hx
    · simp [h, zero_mem]
  have hup := mem_tot.1 (D₂.upper _ hxL) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hup
  obtain ⟨m, hm, hαm⟩ := hα (E K l e ^ η • x) hup
  have hmM : (Pi.single τ m : Vec K a ι) ∈ D₁.M := mem_tot.2 fun σ => by
    by_cases h : σ = τ
    · subst h
      rw [Pi.single_eq_same]
      exact hm
    · simp [h, zero_mem]
  have hlow := mem_tot.1 (D₁.lower _ hmM) τ
  simp only [Pi.smul_apply, Pi.single_eq_same] at hlow
  obtain ⟨m', hm', hm'eq⟩ := D₁.mem_extc.1 hlow
  have hE : PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) =
      E K l e ^ (H + η) * PowerSeries.map (algebraMap O K) α := by
    simp [E, map_X, map_natCast]
  refine ⟨m', hm', ?_⟩
  · have key : D₂.mx τ *ᵥ (PowerSeries.map (algebraMap O K) ((X ^ e + (l : O⟦X⟧)) ^ (H + η) * α) • w) =
        D₂.mx τ *ᵥ ((F.mat (τ - 1)).map (frob K l) *ᵥ m') := by
      rw [Matrix.mulVec_smul, ← hxdef, hE, pow_add,
        show E K l e ^ H * E K l e ^ η * PowerSeries.map (algebraMap O K) α =
          E K l e ^ H * (PowerSeries.map (algebraMap O K) α * E K l e ^ η) by ring,
        mul_smul, mul_smul, hαm,
        ← Matrix.mulVec_smul, hm'eq, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec]
    have := congrArg (fun v => D₂.mxInv τ *ᵥ v) key
    rwa [Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ),
      Matrix.mulVec_mulVec (M := D₂.mxInv τ) (N := D₂.mx τ), PhiMod.mxInv_mul_mx,
      Matrix.one_mulVec, Matrix.one_mulVec] at this

end GlobalTheory.LiftCoker
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobeniusStatement
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a), ∀ α ∈ colon O K (F.mat τ), (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  first | exact @GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | exact GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | (intros; apply GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIdealDegreeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIdealDegreeBound
open scoped PowerSeries Pointwise

namespace GlobalTheory.FrobIdealDeg

open PowerSeries

variable {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
  (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
    if l ∣ m then PowerSeries.coeff (m / l) f else 0)

noncomputable def comps (f : O⟦X⟧) : Fin l → O⟦X⟧ :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose

include hφ in
lemma comps_spec (f : O⟦X⟧) :
    f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (comps l hl φ hφ f j) :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose_spec

lemma comps_eq {f : O⟦X⟧} {c : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (c j)) : comps l hl φ hφ f = c :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).unique (comps_spec l hl φ hφ f) h

lemma comps_add (f f' : O⟦X⟧) :
    comps l hl φ hφ (f + f') = comps l hl φ hφ f + comps l hl φ hφ f' := by
  apply comps_eq
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  rw [← comps_spec l hl φ hφ f, ← comps_spec l hl φ hφ f']

lemma comps_zero : comps l hl φ hφ (0 : O⟦X⟧) = 0 := by
  apply comps_eq
  simp

lemma comps_mul_phi (c f : O⟦X⟧) (k : Fin l) :
    comps l hl φ hφ (φ c * f) k = c * comps l hl φ hφ f k := by
  have : comps l hl φ hφ (φ c * f) = fun k => c * comps l hl φ hφ f k := by
    apply comps_eq
    conv_lhs => rw [comps_spec l hl φ hφ f]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  rw [this]

include hl hφ in
lemma phi_X : φ PowerSeries.X = PowerSeries.X ^ l := by
  ext m
  rw [hφ, PowerSeries.coeff_X_pow]
  by_cases h1 : l ∣ m
  · obtain ⟨q, rfl⟩ := h1
    rw [if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q (by omega), PowerSeries.coeff_X]
    by_cases hq : q = 1
    · subst hq; simp
    · rw [if_neg hq, if_neg]
      intro h2
      apply hq
      have : l * q = l * 1 := by simpa using h2
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 dvd_rfl

lemma comps_X_pow (t : ℕ) :
    comps l hl φ hφ (PowerSeries.X ^ t) ⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ =
      PowerSeries.X ^ (t / l) := by
  have : comps l hl φ hφ (PowerSeries.X ^ t) = fun j =>
      if j = (⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ : Fin l) then PowerSeries.X ^ (t / l) else 0 := by
    apply comps_eq
    simp only [apply_ite φ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [map_pow, phi_X l hl φ hφ, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [this]; simp

lemma descend (J : Ideal O⟦X⟧) (b : ℕ) (f : O⟦X⟧)
    (hf : f ∈ J.map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) (k : Fin l) :
    comps l hl φ hφ f k ∈ J ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  clear hf
  rw [comps_add, Pi.add_apply]
  refine Submodule.add_mem_sup ?_ ?_
  · have key : ∀ r : O⟦X⟧, comps l hl φ hφ (r * x) k ∈ J := by
      change x ∈ Submodule.span O⟦X⟧ (φ '' (J : Set O⟦X⟧)) at hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, hj, rfl⟩ := hz
        intro r
        rw [mul_comm, comps_mul_phi]
        exact J.mul_mem_right _ hj
      | zero =>
        intro r
        rw [mul_zero, comps_zero]
        exact J.zero_mem
      | add z w _ _ hz hw =>
        intro r
        rw [mul_add, comps_add, Pi.add_apply]
        exact J.add_mem (hz r) (hw r)
      | smul s z _ hz =>
        intro r
        rw [smul_eq_mul, ← mul_assoc]
        exact hz (r * s)
    simpa using key 1
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e : c * (l : O⟦X⟧) ^ b = φ ((l : O⟦X⟧) ^ b) * c := by
      rw [map_pow, map_natCast, mul_comm]
    rw [e, comps_mul_phi]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

lemma pow_mem_binom (e h b : ℕ) (hb : 1 ≤ b) :
    (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) ∈
      Ideal.span {(PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h} ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  have : (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) =
      ((PowerSeries.X ^ e + (l : O⟦X⟧)) + (-(l : O⟦X⟧))) ^ (h + b - 1) := by
    rw [pow_mul]; congr 1; ring
  rw [this]
  apply Ideal.add_pow_mem_of_pow_mem_of_le (m := h) (n := b)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · rw [neg_pow]
    exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  · omega

end GlobalTheory.FrobIdealDeg

namespace GlobalTheory


open GlobalTheory.FrobIdealDeg in
theorem frobenius_ideal_degree_bound : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l →
    ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
      if l ∣ m then PowerSeries.coeff (m / l) f else 0) →
    ∀ (a e h b : ℕ) [NeZero a] (I : ZMod a → Ideal O⟦X⟧), 1 ≤ b → h + b ≤ l →
    (∀ τ, ∃ s : ℕ, PowerSeries.X ^ s ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) →
    (∀ τ, ∀ x ∈ I τ, (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x ∈ (I (τ - 1)).map φ) →
    ∀ τ, (PowerSeries.X : O⟦X⟧) ^ (e * (h + b)) ∈ (I τ).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  intro O _ l hl φ hφ a e h b _ I hb hhb hs hI
  classical
  have step : ∀ τ t, (PowerSeries.X : O⟦X⟧) ^ t ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} →
      (PowerSeries.X : O⟦X⟧) ^ (t + e * (h + b - 1)) ∈
        (I (τ - 1)).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
    intro τ t ht
    have hK := pow_mem_binom (O := O) l e h b hb
    obtain ⟨r1, hr1, r2, hr2, hr⟩ := Submodule.mem_sup.mp hK
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ht
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr1
    rw [pow_add, ← hxy, ← hr]
    have hring : (x + y) * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) =
        c * ((PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x) +
          (y * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) + x * r2) := by ring
    rw [hring]
    exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (hI τ x hx))
      (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_left _ _ hr2))
  let s : ZMod a → ℕ := fun τ => Nat.find (hs τ)
  have hspec : ∀ τ, (PowerSeries.X : O⟦X⟧) ^ s τ ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} :=
    fun τ => Nat.find_spec (hs τ)
  have down : ∀ τ, l * s τ ≤ s (τ + 1) + e * (h + b - 1) := by
    intro τ
    have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
    rw [add_sub_cancel_right] at h1
    have h2 := descend l hl φ hφ (I τ) b _ h1 ⟨(s (τ + 1) + e * (h + b - 1)) % l,
      Nat.mod_lt _ (by omega)⟩
    rw [comps_X_pow] at h2
    have h3 : s τ ≤ (s (τ + 1) + e * (h + b - 1)) / l := Nat.find_min' _ h2
    calc l * s τ ≤ l * ((s (τ + 1) + e * (h + b - 1)) / l) := Nat.mul_le_mul_left _ h3
      _ ≤ s (τ + 1) + e * (h + b - 1) := Nat.mul_div_le _ _
  obtain ⟨τ0, -, hmax⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
  obtain ⟨n, hn⟩ : ∃ n, h + b - 1 = n := ⟨_, rfl⟩
  have hnl : n + 1 ≤ l := by omega
  have hS : s τ0 ≤ e := by
    have d := down τ0
    have m := hmax (τ0 + 1) (Finset.mem_univ _)
    rw [hn] at d
    by_contra hc
    push_neg at hc
    nlinarith
  intro τ
  have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
  rw [add_sub_cancel_right] at h1
  refine Ideal.pow_mem_of_pow_mem _ h1 ?_
  have m := hmax (τ + 1) (Finset.mem_univ _)
  have : e * (h + b) = e * (h + b - 1) + e := by
    rw [← Nat.mul_add_one]; congr 1; omega
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIdealDegreeBoundStatement
open scoped PowerSeries Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_pow_mem_map_sup_span_pow_of_frobenius_bound : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ (a e h b : ℕ) [NeZero a] (I : ZMod a → Ideal O⟦X⟧), 1 ≤ b → h + b ≤ l → (∀ τ, ∃ s : ℕ, PowerSeries.X ^ s ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) → (∀ τ, ∀ x ∈ I τ, (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x ∈ (I (τ - 1)).map φ) → ∀ τ, (PowerSeries.X : O⟦X⟧) ^ (e * (h + b)) ∈ (I τ).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  first | exact @GlobalTheory.frobenius_ideal_degree_bound | exact GlobalTheory.frobenius_ideal_degree_bound | (intros; apply GlobalTheory.frobenius_ideal_degree_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernel
noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F hfin b hb hlb x hx
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_variable_pow_smul_eq_zero_of_finiteLength O K _ hfin
  have hX : ∀ τ, (X : O⟦X⟧) ^ n ∈ colon O K (F.mat τ) := by
    intro τ w hw
    have hW : (Pi.single τ w : Vec K a κ) ∈ D₂.M := mem_tot.2 fun σ i => by
      by_cases h : σ = τ
      · subst h; simpa using hw i
      · simp [h]
    have h1 := hn (Submodule.Quotient.mk ⟨_, hW⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    refine ⟨m τ, fun j => mem_tot.1 hm τ j, ?_⟩
    have h2 := congrFun hm' τ
    simp only [LinearMap.restrictScalars_apply, BK.Hom.app_apply] at h2
    rw [h2]
    simp [Submodule.coe_smul, Subalgebra.smul_def]
  have key := GlobalTheory.T.X_pow_mem_map_sup_span_pow_of_frobenius_bound (O := O) l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun f m => PowerSeries.coeff_expand _ _ f) a e (H + η) b (fun τ => colon O K (F.mat τ)) hb hlb
    (fun τ => ⟨n, Ideal.mem_sup_left (hX τ)⟩)
    (fun τ α hα => GlobalTheory.T.colonIdeal_frobenius_le_map_expand O K l ι κ _ (GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius O K l e a ι κ η H D₁ D₂ F τ α hα))
  have comp : ∀ τ, ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) → ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧
      ∃ w' : κ → K⟦X⟧, (∀ i, w' i ∈ A O K) ∧
        ((X : K⟦X⟧) ^ e) ^ (H + η + b) • w = (F.mat (τ - 1)).map (frob K l) *ᵥ m + (l : K⟦X⟧) ^ b • w' := by
    intro τ w hw
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (key (τ - 1))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hq
    obtain ⟨m, hm, hmeq⟩ := GlobalTheory.T.colonIdeal_map_expand_le_frobenius O K l ι κ _ hp w hw
    refine ⟨m, hm, PowerSeries.map (algebraMap O K) c • w, fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hw i)
    · have h3 := congrArg (PowerSeries.map (algebraMap O K)) hpq
      rw [map_add (f := _), map_mul, map_pow, map_pow, map_X, map_natCast] at h3
      rw [← pow_mul, ← h3, add_smul, hmeq, smul_smul, mul_comm]
  choose w hw hxw using fun τ => D₂.mem_extc.1 (mem_tot.1 hx τ)
  choose m hm w' hw' hmw using fun τ => comp τ (w τ) (hw τ)
  refine ⟨fun τ => D₁.mx τ *ᵥ m τ, mem_tot.2 fun τ => D₁.mem_extc.2 ⟨m τ, hm τ, rfl⟩,
    fun τ => D₂.mx τ *ᵥ w' τ, mem_tot.2 fun τ => D₂.mem_extc.2 ⟨w' τ, hw' τ, rfl⟩, ?_⟩
  funext τ
  have hsm : ∀ v : κ → K⟦X⟧, (l : K) ^ b • v = (l : K⟦X⟧) ^ b • v := fun v => by
    rw [← algebraMap_smul K⟦X⟧ ((l : K) ^ b) v, map_pow, map_natCast]
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hsm, BK.Hom.app_apply, Matrix.mulVec_mulVec,
    F.comm τ, hxw τ, ← Matrix.mulVec_smul, hmw τ, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernelStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  first | exact @GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | exact GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | (intros; apply GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow <;> assumption)
end
