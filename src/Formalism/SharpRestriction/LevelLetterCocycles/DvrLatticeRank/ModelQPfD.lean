module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PhibOLComplete

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfC
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfB
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

section Div

variable {O : Type} [CommRing O]

theorem phibN_div (p : ℕ) (hp : p.Prime) [Nontrivial O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] (N : ℕ)
    (f : PowerSeries O) : ∃ (Q : PowerSeries O) (R : Polynomial O), R.degree < ((p * N : ℕ) : WithBot ℕ) ∧
      f = ((1 + PowerSeries.X) ^ p - 1) ^ N * Q + (R : PowerSeries O) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set I : Ideal O := Ideal.span {((p : ℕ) : O)} with hI
  have hjac : I ≤ (⊥ : Ideal O).jacobson := by
    first
    | exact IsAdicComplete.le_jacobson_bot I
    | exact IsAdicComplete.le_jacobson_bot (I := I)
  have hIne : I ≠ ⊤ := by
    intro h
    rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at hjac
    exact bot_ne_top hjac
  have hp2 : ((p : ℕ) : O) ∈ nonunits O :=
    mem_nonunits_iff.2 (fun hu => hIne (Ideal.span_singleton_eq_top.2 hu))
  haveI hch : CharP (O ⧸ I) p := CharP.quotient O p hp2
  haveI : Nontrivial (O ⧸ I) := by
    first
    | exact Ideal.Quotient.nontrivial_iff.2 hIne
    | exact Submodule.Quotient.nontrivial_of_lt_top _ hIne.lt_top
    | exact Ideal.Quotient.nontrivial_of_lt_top hIne.lt_top
  have hinj : Function.Injective (algebraMap (O ⧸ I) (PowerSeries (O ⧸ I))) := by
    intro a b hab
    first
    | simpa using congrArg (PowerSeries.constantCoeff (O ⧸ I)) hab
    | simpa using congrArg PowerSeries.constantCoeff hab
    | simpa using congrArg (PowerSeries.coeff 0) hab
    | exact PowerSeries.C_injective hab
  haveI : CharP (PowerSeries (O ⧸ I)) p := charP_of_injective_algebraMap hinj p
  have hmap : PowerSeries.map (Ideal.Quotient.mk I) (((1 + PowerSeries.X) ^ p - 1) ^ N) =
      PowerSeries.X ^ (p * N) := by
    simp only [map_pow, map_sub, map_add (f := _), map_one, PowerSeries.map_X]
    rw [add_pow_char, one_pow, add_sub_cancel_left, ← pow_mul]
  have key : ∀ c : O, Ideal.Quotient.mk I c = 1 → IsUnit c := by
    intro c hc
    have hmem : c - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hc, map_one, sub_self]
    have hj := (Ideal.mem_jacobson_bot.1 (hjac hmem)) 1
    simpa using hj
  have hdiv : (((1 + PowerSeries.X) ^ p - 1) ^ N : PowerSeries O).IsWeierstrassDivisorAt I := by
    show IsUnit _
    rw [hmap, PowerSeries.order_X_pow, ENat.toNat_coe]
    apply key
    rw [← PowerSeries.coeff_map, hmap, PowerSeries.coeff_X_pow_self]
  have hW := hdiv.isWeierstrassDivisionAt_div_mod f
  refine ⟨hdiv.div f, hdiv.mod f, ?_, ?_⟩
  · have hd := hW.degree_lt
    rw [hmap, PowerSeries.order_X_pow, ENat.toNat_coe] at hd
    exact_mod_cast hd
  · exact hW.eq_mul_add

end Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem delF_mul' {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  rw [W.DelF_def] at hg hh ⊢
  obtain ⟨k₁, hk₁, h₁⟩ := hg
  obtain ⟨k₂, hk₂, h₂⟩ := hh
  exact ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, by
    rw [mul_pow, pow_mul, h₁, one_pow, one_mul, mul_comm k₁ k₂, pow_mul, h₂, one_pow]⟩

theorem delF_inv' {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  rw [W.DelF_def] at hg ⊢
  obtain ⟨k, hk, h⟩ := hg
  exact ⟨k, hk, by rw [inv_pow, h, inv_one]⟩

theorem γA_mul' (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext i
  show W.γ₀ (g * h) (a i) = W.γ₀ g (W.γ₀ h (a i))
  rw [map_mul, AlgHom.mul_apply]

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (letE c : LetA O n) = letE c
  intro δ _
  funext i
  show W.γ₀ δ ((letE c : LetA O n) i) = (letE c : LetA O n) i
  simp only [letE, Pi.single_apply]
  split_ifs <;> simp

theorem letE_mul_self' (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  simp only [letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

def avg (u : Oˣ) (x : LetA O n) : LetA O n := ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γA δ x

theorem avg_mem (u : Oˣ) (x : LetA O n) : avg W u x ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (avg W u x) = avg W u x
  intro δ' hδ'
  unfold avg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact delF_mul' W hδ' ha
  · intro a ha
    exact delF_mul' W (delF_inv' W hδ') ha
  · intro a _
    exact inv_mul_cancel_left δ' a
  · intro a _
    exact mul_inv_cancel_left δ' a
  · intro a _
    exact (γA_mul' W δ' a x).symm

theorem avg_self (u : Oˣ) (hu : (u : O) = (W.DelF.card : ℕ)) {x : LetA O n} (hx : x ∈ W.AΔ) :
    avg W u x = x := by
  have hx' : ∀ δ ∈ W.DelF, W.γA δ x = x := hx
  unfold avg
  rw [Finset.sum_congr rfl (fun δ hδ => hx' δ hδ), Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, ← hu,
    smul_smul, Units.inv_mul, one_smul]

theorem avg_add (u : Oˣ) (x y : LetA O n) : avg W u (x + y) = avg W u x + avg W u y := by
  simp only [avg, map_add (f := _), Finset.sum_add_distrib, smul_add]

theorem avg_mul_left (u : Oˣ) {y : LetA O n} (hy : y ∈ W.AΔ) (x : LetA O n) :
    avg W u (y * x) = y * avg W u x := by
  have hy' : ∀ δ ∈ W.DelF, W.γA δ y = y := hy
  have hs : ∑ δ ∈ W.DelF, W.γA δ (y * x) = y * ∑ δ ∈ W.DelF, W.γA δ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun δ hδ => by rw [map_mul, hy' δ hδ])
  unfold avg
  rw [hs, mul_smul_comm]

theorem avg_sum (u : Oˣ) {ι : Type} (s : Finset ι) (f : ι → LetA O n) :
    avg W u (∑ i ∈ s, f i) = ∑ i ∈ s, avg W u (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [avg, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

theorem div_at (hp : PD.p.Prime) [Nontrivial O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (s' h' : ℕ) (π' Eπ : LetA O n) (w₁ w₂ : (LetA O n)ˣ) (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (hq : W.q = w₂ * Eπ)
    (u : Oˣ) (hu : (u : O) = (W.DelF.card : ℕ)) (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ) (c : ZMod n) :
    ∃ (D : ℕ) (S : Fin D → ↥W.AΔ), ∀ a : ↥W.AΔ, ∃ (co : Fin D → O) (s : ↥W.AΔ),
      (letE c : LetA O n) * a = (letE c : LetA O n) * (∑ r, algebraMap O (LetA O n) (co r) * (S r : LetA O n)) +
        (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s) := by
  classical
  set N := s' + 2 * h' with hN
  refine ⟨PD.p * N, fun i => ⟨avg W u ((letπ : LetA O n) ^ (i : ℕ)), avg_mem W u _⟩, fun a => ?_⟩
  obtain ⟨Q, R, hR, hf⟩ := phibN_div (O := O) PD.p hp N ((a : LetA O n) c)
  set A1 : PowerSeries O := (w₁ : LetA O n) c
  set B1 : PowerSeries O := ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c
  set A2 : PowerSeries O := (w₂ : LetA O n) c
  set B2 : PowerSeries O := ((w₂⁻¹ : (LetA O n)ˣ) : LetA O n) c
  have h1 : A1 * B1 = 1 := by
    have := congrFun (Units.mul_inv w₁) c
    simpa using this
  have h2 : A2 * B2 = 1 := by
    have := congrFun (Units.mul_inv w₂) c
    simpa using this
  have hq0 : W.q₀ = A2 * Eπ c := by
    have := congrFun hq c
    simpa [LocWach.q] using this
  have hEc : Eπ c = B2 * W.q₀ := by
    rw [hq0, ← mul_assoc, mul_comm B2 A2, h2, one_mul]
  have hπc : π' c = A1 * PowerSeries.X ^ s' := by
    have := congrFun hπ c
    simpa [letπ] using this
  have hφb : (1 + PowerSeries.X) ^ PD.p - 1 = PowerSeries.X * W.q₀ := by
    rw [W.q₀_def, add_comm]
  have key : A1 * B1 * (A2 * B2) ^ (2 * h') = 1 := by rw [h1, h2, one_pow, one_mul]
  set s₀ : LetA O n := fun _ => PowerSeries.X ^ (2 * h') * W.q₀ ^ s' * B1 * A2 ^ (2 * h') * Q with hs₀
  set Rt : LetA O n := fun _ => (R : PowerSeries O) with hRt
  have hcl : (letE c : LetA O n) * a = (letE c : LetA O n) * Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s₀) := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_eq_same, one_mul, Pi.pow_apply, hs₀, hRt]
      rw [hf, hφb, hπc, hEc]
      linear_combination (-(PowerSeries.X ^ (s' + 2 * h') * W.q₀ ^ (s' + 2 * h') * Q)) * key
    · simp [letE, Pi.single_apply, hi]
  have hR' : Rt = ∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ) := by
    have hdeg : ∀ m, PD.p * N ≤ m → R.coeff m = 0 := fun m hm =>
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hR (by exact_mod_cast hm))
    funext j
    show (R : PowerSeries O) = (∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j
    rw [Finset.sum_apply]
    ext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.coeff_coe, map_sum]
    have ht : ∀ i : Fin (PD.p * N), PowerSeries.coeff k ((algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j) =
        if k = (i : ℕ) then R.coeff k else 0 := by
      intro i
      have e : (algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j = R.coeff i • PowerSeries.X ^ (i : ℕ) := by
        rw [← Algebra.smul_def]
        rfl
      rw [e, map_smul, PowerSeries.coeff_X_pow, smul_eq_mul]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => ht i),
      Fin.sum_univ_eq_sum_range (fun i => if k = i then R.coeff k else 0) (PD.p * N), Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · rw [Finset.mem_range, not_lt] at hk
      exact hdeg k hk
  have hg : π' * Eπ ^ (2 * h') ∈ W.AΔ := mul_mem hπΔ (pow_mem hEΔ _)
  have hae : (letE c : LetA O n) * a ∈ W.AΔ := mul_mem (letE_mem W c) a.2
  refine ⟨fun i => R.coeff i, ⟨avg W u s₀, avg_mem W u _⟩, ?_⟩
  calc (letE c : LetA O n) * a = avg W u ((letE c : LetA O n) * a) := (avg_self W u hu hae).symm
    _ = avg W u ((letE c : LetA O n) * Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s₀)) := by rw [hcl]
    _ = (letE c : LetA O n) * avg W u Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * avg W u s₀) := by
      rw [avg_add, avg_mul_left W u (letE_mem W c), avg_mul_left W u (letE_mem W c), avg_mul_left W u hg]
    _ = _ := by
      rw [hR', avg_sum]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [avg_mul_left W u (Subalgebra.algebraMap_mem _ _)]

end Formalism.MainNotions.N.Ln34.MQ
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem unit_comp (w : (LetA O n)ˣ) (i : ZMod n) :
    (w : LetA O n) i * ((w⁻¹ : (LetA O n)ˣ) : LetA O n) i = 1 := by
  exact congrFun (Units.mul_inv w) i

theorem π_at (s' : ℕ) (π' : LetA O n) (w₁ : (LetA O n)ˣ) (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (i : ZMod n) :
    π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := by
  rw [hπ]
  rfl

theorem hlet_of [IsDomain O] (s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n) (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (hπΔ : π' ∈ W.AΔ) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (c : ZMod n) :
    ∀ a : O, a ≠ 0 → ∀ u : W.EE,
      (∃ g ∈ W.AΔ, algebraMap (LetA O n) W.EE π' * u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      (∃ g ∈ W.AΔ, a • u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      ∃ g ∈ W.AΔ, u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by
  rintro a ha u ⟨g, hg, hgu⟩ ⟨h, hh, hhu⟩
  have hA : π' * ((letE c : LetA O n) * h) = algebraMap O (LetA O n) a * ((letE c : LetA O n) * g) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (π' * ((letE c : LetA O n) * h))
        = algebraMap (LetA O n) W.EE π' * algebraMap (LetA O n) W.EE ((letE c : LetA O n) * h) := map_mul _ _ _
      _ = algebraMap (LetA O n) W.EE π' * (a • u) := by rw [hhu]
      _ = a • (algebraMap (LetA O n) W.EE π' * u) := by rw [mul_smul_comm]
      _ = a • algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by rw [hgu]
      _ = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) a * ((letE c : LetA O n) * g)) := by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← map_mul]
  have hc : π' c * h c = a • g c := by
    have := congrFun hA c
    rw [Algebra.smul_def]
    simpa [letE] using this
  have hdvd : PowerSeries.X ^ s' ∣ g c := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have h1 := congrArg (PowerSeries.coeff m) hc
    rw [π_at s' π' w₁ hπ c, mul_comm ((w₁ : LetA O n) c), mul_assoc, PowerSeries.coeff_X_pow_mul',
      if_neg (by omega), map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left ha
  obtain ⟨G', hG'⟩ := hdvd
  set g' : LetA O n := (letE c : LetA O n) * (fun _ => ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c * G') with hg'
  have hπg' : π' * g' = (letE c : LetA O n) * g := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.mul_apply, hg', letE, Pi.single_eq_same, one_mul]
      rw [π_at s' π' w₁ hπ i, hG']
      linear_combination (PowerSeries.X ^ s' * G') * unit_comp w₁ i
    · simp [hg', letE, Pi.single_apply, hi]
  have hcancel : ∀ x y : LetA O n, π' * x = π' * y → x = y := by
    intro x y hxy
    funext i
    have hxi := congrFun hxy i
    simp only [Pi.mul_apply] at hxi
    rw [π_at s' π' w₁ hπ i] at hxi
    have hne : (w₁ : LetA O n) i * PowerSeries.X ^ s' ≠ 0 := by
      have hw : (w₁ : LetA O n) i ≠ 0 := by
        intro h0
        have := unit_comp w₁ i
        rw [h0, zero_mul] at this
        exact zero_ne_one this
      exact mul_ne_zero hw (pow_ne_zero _ PowerSeries.X_ne_zero)
    exact mul_left_cancel₀ hne hxi
  have hπΔ' : ∀ δ ∈ W.DelF, W.γA δ π' = π' := hπΔ
  have hm : (letE c : LetA O n) * g ∈ W.AΔ := mul_mem (letE_mem W c) hg
  have hm' : ∀ δ ∈ W.DelF, W.γA δ ((letE c : LetA O n) * g) = (letE c : LetA O n) * g := hm
  have hg'Δ : g' ∈ W.AΔ := by
    show ∀ δ ∈ W.DelF, W.γA δ g' = g'
    intro δ hδ
    apply hcancel
    calc π' * W.γA δ g' = W.γA δ π' * W.γA δ g' := by rw [hπΔ' δ hδ]
      _ = W.γA δ (π' * g') := (map_mul _ _ _).symm
      _ = W.γA δ ((letE c : LetA O n) * g) := by rw [hπg']
      _ = (letE c : LetA O n) * g := hm' δ hδ
      _ = π' * g' := hπg'.symm
  refine ⟨g', hg'Δ, ?_⟩
  have hle : (letE c : LetA O n) * g' = g' := by rw [hg', ← mul_assoc, letE_mul_self']
  rw [hle]
  exact hπu.mul_left_cancel (by rw [hgu, ← hπg', map_mul])

theorem q_unit (hp : PD.p.Prime) : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
  exact Formalism.MainNotions.LiftingTheory.liftb_q_unit W

end Formalism.MainNotions.N.Ln34.MQ
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

theorem dvd_pow_of_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0)
    (hpu : ¬ IsUnit p) : ∀ a : O, a ≠ 0 → ∃ (k : ℕ) (b : O), p ^ k = b * a := by
  intro a ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hpu (associated_one_iff_isUnit.1 (by simpa using hk))
  have h1 : ϖ ^ m ∣ ϖ ^ (k * m) := pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk1))
  have hdvd : a ∣ p ^ m :=
    hm.dvd.trans (h1.trans (by rw [pow_mul]; exact (hk.symm.pow_pow).dvd))
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨m, b, by rw [hb, mul_comm]⟩

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_DelS' {x : W.DD T} : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  simp [DelS, Submodule.mem_iInf, sub_eq_zero]

theorem mem_letS' {c : ZMod n} {x : W.DD T} : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  simp [letS, sub_eq_zero]

theorem γD_smulA' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem expand_at (π' a : LetA O n) (i : ZMod n) (hπ0 : PowerSeries.constantCoeff (π' i) = 0)
    (F : PowerSeries O) (hF : a i = PowerSeries.subst (π' i) F) :
    a i = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F) +
      PowerSeries.C (PowerSeries.constantCoeff F) := by
  have hS : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  conv_lhs => rw [hF, PowerSeries.eq_X_mul_shift_add_const F]
  rw [PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_X hS, PowerSeries.subst_C]
  rfl


set_option maxHeartbeats 1000000 in
theorem basis_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Nonempty (Module.Basis (Fin r) O (LcQ W T π' c)) := by
  classical
  set d : ZMod n := c - 1 with hd
  have hπd : ∀ i, π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := fun i => π_at s' π' w₁ hπ i
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    rw [hπd i, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hmem : ∀ j, (letE d : LetA O n) • b j ∈ NcS W T d := by
    intro j
    obtain ⟨hN, hΔ⟩ := hbΔ j
    refine ⟨⟨(W.N T).smul_mem _ hN, (mem_DelS' W T).2 fun δ hδ => ?_⟩, (mem_letS' W T).2 ?_⟩
    · rw [γD_smulA', hΔ δ hδ, (show ∀ δ ∈ W.DelF, W.γA δ (letE d : LetA O n) = letE d from letE_mem W d) δ hδ]
    · rw [smul_smul, letE_mul_self']
  let v : Fin r → LcQ W T π' c := fun j => Submodule.Quotient.mk ⟨_, hmem j⟩
  have hli : LinearIndependent O v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (∑ j, g j • (⟨_, hmem j⟩ : ↥(NcS W T d))) ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      simpa only [map_smul, Submodule.mkQ_apply] using hg
    rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    obtain ⟨⟨y, hyN, hy⟩, -⟩ := h0
    obtain ⟨a', ha'⟩ := (hbu y hyN).exists
    have hxN : π' • y ∈ W.N T := (W.N T).smul_mem _ hyN
    have hrep1 : π' • y = ∑ j, (π' * a' j) • b j := by
      rw [ha', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    have hrep2 : π' • y = ∑ j, (algebraMap O (LetA O n) (g j) * (letE d : LetA O n)) • b j := by
      have hy' : π' • y = ∑ j, g j • ((letE d : LetA O n) • b j) := by
        rw [← hy]
        show π' • y = ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y
        rw [pow_one]
        rfl
      rw [hy']
      exact Finset.sum_congr rfl fun j _ => by rw [← smul_smul, algebraMap_smul]
    have huq := (hbu _ hxN).unique hrep1 hrep2
    have hj := congrFun (congrFun huq j) d
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one] at hj
    have hcc := congrArg PowerSeries.constantCoeff hj
    rw [map_mul, hπ0 d, zero_mul] at hcc
    have : PowerSeries.constantCoeff ((algebraMap O (LetA O n) (g j)) d) = g j := by
      show PowerSeries.constantCoeff (algebraMap O (PowerSeries O) (g j)) = g j
      rw [PowerSeries.algebraMap_apply]
      simp
    rw [this] at hcc
    exact hcc.symm
  have hsp : ⊤ ≤ Submodule.span O (Set.range v) := by
    rintro q -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨⟨hxN, hxΔ⟩, hxl⟩ := hx
    have hxΔ' := (mem_DelS' W T).1 hxΔ
    have hxl' := (mem_letS' W T).1 hxl
    obtain ⟨a, haΔ, hxa⟩ := hbe x ⟨hxN, hxΔ'⟩
    choose F hF using fun j => (huniq (a j) (haΔ j)).exists
    let κ : Fin r → O := fun j => PowerSeries.constantCoeff (F j d)
    let t : Fin r → LetA O n := fun j _ => PowerSeries.subst (π' d) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F j d))
    have hkey : ∀ j, (letE d : LetA O n) * a j = algebraMap O (LetA O n) (κ j) * letE d + π' * ((letE d : LetA O n) * t j) := by
      intro j
      funext i
      by_cases hi : i = d
      · subst hi
        simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_eq_same, one_mul, mul_one]
        rw [expand_at π' (a j) _ (hπ0 _) (F j _) (hF j _)]
        show _ = algebraMap O (PowerSeries O) (κ j) + _
        rw [PowerSeries.algebraMap_apply]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, t, κ]
        ring
      · simp [letE, Pi.single_apply, hi]
    set y : W.DD T := ∑ j, ((letE d : LetA O n) * t j) • b j with hydef
    have hyN : y ∈ W.N T := Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbΔ j).1
    have hxe : x = ∑ j, κ j • ((letE d : LetA O n) • b j) + π' • y := by
      conv_lhs => rw [← hxl', hxa, Finset.smul_sum]
      rw [hydef, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, hkey j, add_smul, smul_smul, ← algebraMap_smul (LetA O n) (κ j), smul_smul]
    have hdiff : (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) - ∑ j, κ j • ⟨_, hmem j⟩ ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by
      rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      have he : x - ∑ j, κ j • ((letE d : LetA O n) • b j) = π' • y := by rw [hxe]; abel
      rw [he]
      refine ⟨⟨y, hyN, ?_⟩, ?_⟩
      · show ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y = π' • y
        rw [pow_one]; rfl
      · rw [← he]
        refine sub_mem hxΔ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j).1.2)
    have hq : (Submodule.Quotient.mk (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) : LcQ W T π' c) = ∑ j, κ j • v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(Submodule.Quotient.eq _).2 hdiff, ← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
      rfl
    rw [hq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp⟩

theorem finite_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Module.Finite O (LcQ W T π' c) := by
  exact Module.Finite.of_basis (basis_L W T π' s' hs w₁ hπ huniq b hbΔ hbu hbe c).some

end Formalism.MainNotions.N.Ln34.MQ
