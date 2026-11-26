module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.FlagAll
open UpperTheory.V.Z.Win.Dn
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.BasicNotions UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win
open scoped Pointwise

theorem UpperTheory.V.Z.Win.Dn.flagAll_of :
    FlagAll := by
  intro F Ω _ _ _ _ _ l _ n r h v hv B hB
  obtain ⟨A, hA, κ, P, hP⟩ := h v hv
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hB
  have hmem : ∀ s ∈ Dec (F := F) (g • A), g⁻¹ * s * g ∈ Dec (F := F) A := fun s hs => by
    have h1 : s • g • A = g • A := hs
    show (g⁻¹ * s * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  let d : ↥(Dec (F := F) (g • A)) →* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g⁻¹ * s * g, hmem s s.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp [mul_assoc] }
  refine ⟨fun i => (κ i).comp d, P * r g⁻¹, fun s => ?_⟩
  have e : P * r g⁻¹ * r s * (P * r g⁻¹)⁻¹ = P * r (d s) * P⁻¹ := by
    show _ = P * r (g⁻¹ * s * g) * P⁻¹
    rw [map_mul, map_mul, map_inv]
    group
  rw [e]
  exact hP (d s)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.IneOfKer
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FinChar
open Polynomial

namespace UpperTheory.V.Lib.FinChar

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

theorem exists_eigenbasis (f : Module.End k (Fin n → k)) {m : ℕ} (hm : 0 < m) (hfm : f ^ m = 1) :
    ∃ (b : Module.Basis (Fin n) k (Fin n → k)) (d : Fin n → k), ∀ i, f (b i) = d i • b i := by
  classical
  have hmk : ((m : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsep : (X ^ m - C (1 : k)).Separable := separable_X_pow_sub_C 1 hmk one_ne_zero
  have hss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hfm])
  have hint : DirectSum.IsInternal f.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep
      hss.iSup_eigenspace_eq_top
  let v := fun μ => Module.Basis.ofVectorSpace k (f.eigenspace μ)
  let B := hint.collectedBasis v
  let e := B.indexEquiv (Pi.basisFun k (Fin n))
  refine ⟨B.reindex e, fun i => (e.symm i).1, fun i => ?_⟩
  have hmem := hint.collectedBasis_mem v (e.symm i)
  rw [Module.End.mem_eigenspace_iff] at hmem
  simpa [Module.Basis.reindex_apply, B] using hmem

theorem exists_eigenframe (T : (Matrix (Fin n) (Fin n) k)ˣ) {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ (u : (Matrix (Fin n) (Fin n) k)ˣ) (d : Fin n → k), T.val * u.val = u.val * Matrix.diagonal d := by
  classical
  obtain ⟨b, d, hb⟩ := exists_eigenbasis (Matrix.toLinAlgEquiv' T.val) hm
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hT, Units.val_one, map_one])
  letI := (Pi.basisFun k (Fin n)).invertibleToMatrix b
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b), d, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  have hj := congrFun (hb j) i
  simp only [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hj
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, hj, mul_comm]

theorem charpoly_powers (T : (Matrix (Fin n) (Fin n) k)ˣ) {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ d : Fin n → k, (∀ i, d i ^ m = 1) ∧ ∀ a : ℕ, (T ^ a).val.charpoly = ∏ i, (X - C (d i ^ a)) := by
  classical
  obtain ⟨u, d, hu⟩ := exists_eigenframe T hm hT
  have hc : ∀ a : ℕ, T.val ^ a * u.val = u.val * Matrix.diagonal d ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hu, mul_assoc, ← pow_succ']
  refine ⟨d, fun i => ?_, fun a => ?_⟩
  · have h1 : u.val * Matrix.diagonal (d ^ m) = u.val * 1 := by
      rw [← Matrix.diagonal_pow, ← hc m, ← Units.val_pow_eq_pow_val, hT, Units.val_one, one_mul,
        mul_one]
    have h2 := (Units.mul_right_inj u).mp h1
    have h3 := congrFun (congrFun h2 i) i
    simpa using h3
  · have hdet : IsUnit u.val.det := (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
    have h1 : (T ^ a).val = u.val * Matrix.diagonal d ^ a * (u.val)⁻¹ := by
      rw [Units.val_pow_eq_pow_val, ← hc a, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    rw [h1, Matrix.charpoly_units_conj, Matrix.diagonal_pow, Matrix.charpoly_diagonal]
    simp [Pi.pow_apply]

theorem charpoly_of_ker {Γ : Type} [Group Γ] (r : Γ →* (Matrix (Fin n) (Fin n) k)ˣ) (χ : Γ →* kˣ) (I : Subgroup Γ)
    (hf : (χ '' (I : Set Γ)).Finite) (hk : ∀ g ∈ I, χ g = 1 → r g = 1) :
    ∃ j : Fin n → ℕ, ∀ g ∈ I, (r g).val.charpoly = ∏ i, (X - C ((χ g : k) ^ j i)) := by
  classical
  set S : Subgroup kˣ := I.map χ with hS
  have hSf : (S : Set kˣ).Finite := by rw [hS, Subgroup.coe_map]; exact hf
  haveI : Finite S := hSf.to_subtype
  obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := S)
  obtain ⟨g0, hg0I, hg0⟩ := Subgroup.mem_map.mp x.2
  set N := orderOf x with hN
  have hNpos : 0 < N := orderOf_pos x
  have hxN : (x : kˣ) ^ N = 1 := by
    have h := congrArg Subtype.val (pow_orderOf_eq_one x)
    exact_mod_cast h
  have hrN : r g0 ^ N = 1 := by
    rw [← map_pow]
    apply hk _ (I.pow_mem hg0I N)
    rw [map_pow, hg0, hxN]
  obtain ⟨d, hd, hchar⟩ := charpoly_powers (r g0) hNpos hrN
  have hprim : IsPrimitiveRoot ((x : kˣ) : k) N := by
    rw [IsPrimitiveRoot.coe_units_iff, hN, ← Subgroup.orderOf_coe]
    exact IsPrimitiveRoot.orderOf _
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have hj : ∀ i, ∃ j, ((x : kˣ) : k) ^ j = d i := fun i =>
    let ⟨j, _, h⟩ := hprim.eq_pow_of_pow_eq_one (hd i); ⟨j, h⟩
  choose j hj using hj
  refine ⟨j, fun g hg => ?_⟩
  obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp (hx ⟨χ g, Subgroup.mem_map_of_mem χ hg⟩)
  have hχa : χ g = (x : kˣ) ^ a := by
    rw [← SubgroupClass.coe_pow, ha]
  have hrg : r g = r g0 ^ a := by
    have h1 : χ (g * (g0 ^ a)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hg0, hχa, mul_inv_cancel]
    have h2 := hk _ (I.mul_mem hg (I.inv_mem (I.pow_mem hg0I a))) h1
    rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h2
    exact h2
  rw [hrg, hchar a]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← hj i, hχa, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, Nat.mul_comm]

end UpperTheory.V.Lib.FinChar
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Z.Win
open UpperTheory.V.Z.Win.Dn

theorem UpperTheory.V.Z.Win.Dn.ineOfKer_of :
    IneOfKer := by
  intro F Ω _ _ _ _ _ l _ n r h v hv A hA
  have hn : ¬ A.valuation (l : Ω) < 1 := fun e => hv ((hA (l : 𝓞 F)).1 (by simpa only [map_natCast] using e))
  obtain ⟨χ, hc, hf, hk⟩ := h A hn
  obtain ⟨j, hj⟩ := UpperTheory.V.Lib.FinChar.charpoly_of_ker r χ (Ine (F := F) A) hf hk
  refine ⟨fun i => (χ.comp (Dec (F := F) A).subtype) ^ j i, fun i => ?_, fun g hg => ?_⟩
  · exact (hc.comp continuous_subtype_val).pow (j i)
  · refine (hj _ hg).trans (Finset.prod_congr rfl fun i _ => ?_)
    simp
end
