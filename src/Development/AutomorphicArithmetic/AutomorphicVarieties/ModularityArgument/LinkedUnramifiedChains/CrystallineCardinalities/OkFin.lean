module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.okFin :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → (∀ k, Finite (Ok l O k)) ∧ (∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c})) ∧ (∀ k, (∀ x : Ok l O k, l ^ k • x = 0)) ∧ (∀ k, 2 ^ k ≤ Nat.card (Ok l O k)) ∧ (∀ k, ∃ N, maximalIdeal O ^ N ≤ Ideal.span {(l : O) ^ k}) ∧ (∀ k (a : ℤ_[l]) (x : Ok l O k), algebraMap ℤ_[l] O a • x = (PadicInt.toZModPow k a).val • x) ∧ (∀ k, 0 < k → Ideal.span {(l : O) ^ k} ≤ maximalIdeal O) := by
  intro l _ O _ _ _ _ _ hl
  haveI hchar := IsCoef.char (l := l) (O := O)
  haveI hfinres := IsCoef.fin (l := l) (O := O)
  have hlm : (l : O) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hlu : ¬ IsUnit (l : O) := fun hu => ((IsLocalRing.mem_maximalIdeal _).mp hlm) hu
  have hfinc : ∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c}) := by
    intro c hc
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    apply IsLocalRing.finite_quotient_iff.mpr
    refine ⟨n, ?_⟩
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact Units.mul_left_dvd.mpr dvd_rfl
  have hfin : ∀ k, Finite (Ok l O k) := fun k => hfinc _ (pow_ne_zero k hl)
  have hcard : ∀ k, 2 ^ k ≤ Nat.card (Ok l O k) := by
    intro k
    induction k with
    | zero =>
      haveI := hfin 0
      rw [pow_zero]
      exact Nat.card_pos
    | succ k ih =>
      haveI := hfin k
      haveI := hfin (k + 1)
      have hle : Ideal.span {(l : O) ^ (k + 1)} ≤ Ideal.span {(l : O) ^ k} := by
        rw [Ideal.span_singleton_le_span_singleton]
        exact pow_dvd_pow _ (Nat.le_succ k)
      let g : Ok l O (k + 1) →+ Ok l O k := (Ideal.Quotient.factor hle).toAddMonoidHom
      have hsurj : Function.Surjective g := Ideal.Quotient.factor_surjective hle
      have hmem : Ideal.Quotient.mk (Ideal.span {(l : O) ^ (k + 1)}) ((l : O) ^ k) ∈ g.ker := by
        rw [AddMonoidHom.mem_ker]
        show Ideal.Quotient.factor hle (Ideal.Quotient.mk _ ((l : O) ^ k)) = 0
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self _
      have hne : Ideal.Quotient.mk (Ideal.span {(l : O) ^ (k + 1)}) ((l : O) ^ k) ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_dvd_pow_iff hl hlu]
        omega
      haveI : Nontrivial g.ker := nontrivial_of_ne ⟨_, hmem⟩ 0 (fun h => hne (congrArg Subtype.val h))
      have h2 : 2 ≤ Nat.card g.ker := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have hrange : Nat.card g.range = Nat.card (Ok l O k) := by
        rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top]
      calc 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        _ ≤ Nat.card (Ok l O k) * Nat.card g.ker := Nat.mul_le_mul ih h2
        _ = Nat.card g.ker * g.ker.index := by rw [AddSubgroup.index_ker, hrange, mul_comm]
        _ = Nat.card (Ok l O (k + 1)) := AddSubgroup.card_mul_index _
  refine ⟨hfin, hfinc, ?_, hcard, ?_, ?_, ?_⟩
  · intro k x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro k
    haveI := hfin k
    exact IsLocalRing.finite_quotient_iff.mp (hfin k)
  · intro k a x
    have hmem : a - (((PadicInt.toZModPow k a).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) k) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨b, hb⟩ := hmem
    have ha : algebraMap ℤ_[l] O a =
        (((PadicInt.toZModPow k a).val : ℕ) : O) + algebraMap ℤ_[l] O b * (l : O) ^ k := by
      have h0 := congrArg (algebraMap ℤ_[l] O) hb
      simp only [map_mul, map_sub, map_pow, map_natCast] at h0
      linear_combination (-1 : O) * h0
    have hz : (algebraMap ℤ_[l] O b * (l : O) ^ k) • x = 0 := by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    rw [ha, add_smul, Nat.cast_smul_eq_nsmul, hz, add_zero]
  · intro k hk
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_of_mem _ hlm k hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualCard
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.dualCard :
    ∀ (l : ℕ) [Fact l.Prime] (k : ℕ) (N : Type) [AddCommGroup N] [Finite N], (∀ x : N, l ^ k • x = 0) → Finite (N →+ ZMod (l ^ k)) ∧ Nat.card (N →+ ZMod (l ^ k)) = Nat.card N := by
  intro l _ k N _ _ h
  have hne : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  letI : Module (ZMod (l ^ k)) N := AddCommGroup.zmodModule h
  have hfin : Finite (N →+ ZMod (l ^ k)) :=
    Finite.of_injective (fun f : N →+ ZMod (l ^ k) => (f : N → ZMod (l ^ k))) DFunLike.coe_injective
  refine ⟨hfin, ?_⟩
  rw [← GlobalTheory.ZModDual.card_dual_eq (l ^ k) N]
  refine Nat.card_congr
    { toFun := fun f => f.toZModLinearMap (l ^ k)
      invFun := fun f => f.toAddMonoidHom
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.WtCut
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.wtCut :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (I : Subgroup D) (d k m : ℕ) (A N : Type) [AddCommGroup A] [Finite A] [AddCommGroup N], GenI l I d → (∀ x : A, l ^ k • x = 0) → ∀ (Z : AddSubgroup (D → N)), Finite Z → ∀ p : Fin m → N →+ A, (∀ z ∈ Z, IsLocallyConstant z ∧ ∀ j s s', p j (z (s * s')) = p j (z s) + p j (z s')) → Nat.card Z ≤ {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}.ncard * Nat.card A ^ (m * d) := by
  intro l _ D _ _ I d k m A N _ _ _ hG hA Z _ p hZ
  obtain ⟨u, -, hu⟩ := hG
  let Φ : Z →+ (Fin m → Fin d → A) :=
    { toFun := fun z j a => p j (z.1 (u a))
      map_zero' := by
        funext j a
        simp
      map_add' := by
        intro x y
        funext j a
        simp }
  let S : Set (D → N) := {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}
  have hSfin : S.Finite := Set.Finite.subset (Set.toFinite (Z : Set (D → N))) (fun z hz => hz.1)
  have hker : ∀ z ∈ Φ.ker, (z : D → N) ∈ S := by
    intro z hz
    refine ⟨z.2, fun j s hs => ?_⟩
    have hz0 : ∀ a, p j (z.1 (u a)) = 0 := fun a => congrFun (congrFun hz j) a
    exact hu k A hA (fun s => p j (z.1 s)) ((hZ _ z.2).1.comp (p j))
      (fun s t => (hZ _ z.2).2 j s t) hz0 s hs
  have h1 : Nat.card Φ.ker ≤ S.ncard := by
    rw [← Nat.card_coe_set_eq]
    haveI := hSfin.to_subtype
    refine Nat.card_le_card_of_injective (fun z : Φ.ker => (⟨z.1.1, hker z.1 z.2⟩ : S)) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  have h2 : Nat.card Φ.range ≤ Nat.card A ^ (m * d) := by
    calc Nat.card Φ.range ≤ Nat.card (Fin m → Fin d → A) :=
          Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
      _ = Nat.card A ^ (m * d) := by
          simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
          rw [← pow_mul, mul_comm]
  calc Nat.card Z = Nat.card Φ.ker * Φ.ker.index := (AddSubgroup.card_mul_index _).symm
    _ = Nat.card Φ.ker * Nat.card Φ.range := by rw [AddSubgroup.index_ker]
    _ ≤ S.ncard * Nat.card A ^ (m * d) := Nat.mul_le_mul h1 h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.AdicContinuousSumThree
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem ac_const {D R : Type} [TopologicalSpace D] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : D => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := fun N => by
  have h := (hf N).add (hg N)
  convert h using 1
  funext s
  exact map_add (Ideal.Quotient.mk (I ^ N)) (f s) (g s)

private theorem ac_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  have h := (hf N).mul (hg N)
  convert h using 1
  funext s
  exact map_mul (Ideal.Quotient.mk (I ^ N)) (f s) (g s)

private theorem ac_comp {D E R : Type} [TopologicalSpace D] [TopologicalSpace E] [CommRing R] {I : Ideal R}
    {f : E → R} (hf : AdicCont I f) {φ : D → E} (hφ : Continuous φ) : AdicCont I fun s => f (φ s) :=
  fun N => (hf N).comp_continuous hφ

private theorem adic_continuous_sum_three {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f : Fin 3 → D → R}
    (hf : ∀ a, AdicCont I (f a)) : AdicCont I fun s => ∑ a, f a s := by
  simp only [Fin.sum_univ_three]
  exact ac_add (ac_add (hf 0) (hf 1)) (hf 2)

variable {l : ℕ} [Fact l.Prime]

private theorem triOf_val {C : Type} [CommRing C] {κ : Type} [Field κ] {F : Frame l κ} (B : Box F 3 C) (v : F.V)
    (s : F.Gv v) : (triOf B v s : Matrix (Fin 3) (Fin 3) C) =
      (B.g v : Matrix (Fin 3) (Fin 3) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := rfl

private theorem pow_w_ne {κ : Type} [Field κ] (x : κˣ) (hx : x ^ 2 ≠ 1) (i j : Fin 3) (h : i ≠ j) :
    ((x ^ w 3 i : κˣ) : κ) ≠ ((x ^ w 3 j : κˣ) : κ) := by
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have h1 : x ≠ 1 := fun e => hx (by simp [e])
  have h2 : x ≠ x⁻¹ := fun e => hx (by
    rw [pow_two]
    nth_rewrite 2 [e]
    simp)
  have h3 : x⁻¹ ≠ 1 := fun e => h1 (by simpa using e)
  intro e
  have e' := Units.ext e
  fin_cases i <;> fin_cases j <;> simp_all

private theorem genI_of {D : Type} [Group D] [TopologicalSpace D] {I : Subgroup D} {d : ℕ}
    (h : ∃ u : Fin d → D, (∀ a, u a ∈ I) ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : D →* A,
      IsOpen (χ.ker : Set D) → (∀ a, χ (u a) = 1) → ∀ g ∈ I, χ g = 1) : GenI l I d := by
  obtain ⟨u, hu, hχ⟩ := h
  refine ⟨u, hu, ?_⟩
  intro k A _ _ hk a hloc hadd hz g hg
  have h1 : a 1 = 0 := by simpa using hadd 1 1
  let χ : D →* Multiplicative A :=
    { toFun := fun s => Multiplicative.ofAdd (a s)
      map_one' := by rw [h1]; rfl
      map_mul' := fun s t => by rw [hadd]; rfl }
  have hp : IsPGroup l (Multiplicative A) := fun x => ⟨k, by
    show Multiplicative.ofAdd (l ^ k • Multiplicative.toAdd x) = 1
    rw [hk]
    rfl⟩
  have ho : IsOpen (χ.ker : Set D) := by
    have : (χ.ker : Set D) = a ⁻¹' {0} := by
      ext s
      show χ s = 1 ↔ a s = 0
      exact Iff.rfl
    rw [this]
    exact hloc.isOpen_fiber 0
  exact hχ (Multiplicative A) hp χ ho (fun j => by
    show Multiplicative.ofAdd (a (u j)) = 1
    rw [hz]
    rfl) g hg

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.triOk :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ v, TriRep (triOf B v) ∧ GenI l (F.Iv v) (F.dv v) ∧ ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
  intro l _ O _ _ _ _ _ F C₀ hF _ ρ B hL hB hC v
  have hd : ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
    intro s j
    rw [triOf_val]
    have e : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hB.res (F.loc0 v s)
    rw [e]
    exact hB.psi v j s
  have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
  refine ⟨⟨fun i j => ?_, fun s => ?_, ?_⟩, ?_, hd⟩
  · have e : (fun s => (triOf B v s : Matrix (Fin 3) (Fin 3) O) i j) = fun s =>
        ∑ b, (∑ a, (B.g v : Matrix (Fin 3) (Fin 3) O) i a * (B.r (F.loc v s)).mat a b) *
          (((B.g v)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) b j := by
      funext s
      rw [triOf_val, Matrix.mul_apply]
      simp only [Matrix.mul_apply]
    rw [e]
    exact adic_continuous_sum_three fun b => ac_mul (adic_continuous_sum_three fun a => ac_mul (ac_const _ _) (ac_comp (hC a b) hloc)) (ac_const _ _)
  · exact B.tri v s
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij => ?_⟩
    rw [hd, hd]
    by_contra hn
    have hm : (ρ.ψ v i s : O) - (ρ.ψ v j s : O) ∈ maximalIdeal O := hn
    have h0 := (res_eq_zero_iff O O _).2 hm
    rw [map_sub, sub_eq_zero] at h0
    have hi := hL.2.1.2 v i s
    have hj := hL.2.1.2 v j s
    simp only [NRep.map_ψ, RingHom.id_apply] at hi hj
    exact pow_w_ne _ hs i j hij (by rw [← hi, ← hj]; exact h0)
  · obtain ⟨u, a₀, hu, -, hχ⟩ := hF.gen v
    exact genI_of ⟨u, fun a => (hu a).1, hχ⟩
end
