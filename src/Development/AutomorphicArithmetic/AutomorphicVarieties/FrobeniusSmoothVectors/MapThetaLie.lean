module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MapThetaLie
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C]
  {K : Ideal C} (u : K →ₗ[O] ResidueField O)

private theorem evk_add {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x + y) = evK K u x + evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.add_mem hx hy), ← map_add (f := _)]
  rfl

private theorem evk_sub {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    evK K u (x - y) = evK K u x - evK K u y := by
  rw [evK_of_mem u hx, evK_of_mem u hy, evK_of_mem u (K.sub_mem hx hy), ← map_sub]
  rfl

private theorem evk_neg {x : C} (hx : x ∈ K) : evK K u (-x) = - evK K u x := by
  rw [evK_of_mem u hx, evK_of_mem u (K.neg_mem hx), ← map_neg]
  rfl

private theorem evk_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, f i ∈ K) :
    evK K u (∑ i ∈ s, f i) = ∑ i ∈ s, evK K u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, evK_of_mem u K.zero_mem]
    exact map_zero u
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evk_add u (hf a) (K.sum_mem fun i _ => hf i), ih]

private theorem evk_mul [IsCO O C] (hK : maximalIdeal C * K = ⊥) (a : C) {x : C} (hx : x ∈ K) :
    evK K u (a * x) = res O C a * evK K u x := by
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
  have h0 : (a - algebraMap O C b) * x = 0 := by
    have := Ideal.mul_mem_mul hb hx
    rwa [hK, Ideal.mem_bot] at this
  have h1 : res O C a = algebraMap O _ b := by
    have := (res_eq_zero_iff O C _).2 hb
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  rw [evK_of_mem u hx, evK_of_mem u (K.mul_mem_left a hx), h1, ← Algebra.smul_def, ← map_smul]
  congr 1
  apply Subtype.ext
  show a * x = b • x
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, h0]

variable {n : ℕ}

private theorem mem_left {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (A * Z) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_left _ (hZ k j)

private theorem mem_right {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K)
    (A : Matrix (Fin n) (Fin n) C) (i j : Fin n) : (Z * A) i j ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun k _ => K.mul_mem_right _ (hZ i k)

private theorem map_left [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_left _ (hZ k j)]
  exact Finset.sum_congr rfl fun k _ => evk_mul u hK _ (hZ k j)

private theorem map_right [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) (A : Matrix (Fin n) (Fin n) C) :
    (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply,
    evk_sum u _ _ fun k => K.mul_mem_right _ (hZ i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, evk_mul u hK _ (hZ i k), mul_comm]
  rfl

private theorem mem_theta {Z : Matrix (Fin n) (Fin n) C} (hZ : ∀ i j, Z i j ∈ K) (i j : Fin n) :
    thetaLie Z i j ∈ K :=
  K.neg_mem (mem_right (mem_left (Z := Zᵀ) (fun i j => hZ j i) _) _ i j)

private theorem map_thetaLie [IsCO O C] (hK : maximalIdeal C * K = ⊥) {Z : Matrix (Fin n) (Fin n) C}
    (hZ : ∀ i j, Z i j ∈ K) : (thetaLie Z).map (evK K u) = thetaLie (Z.map (evK K u)) := by
  have hT : ∀ i j, Zᵀ i j ∈ K := fun i j => hZ j i
  have hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have e : (Jmat C n * Zᵀ * Jmat C n).map (evK K u) =
      Jmat (ResidueField O) n * (Z.map (evK K u))ᵀ * Jmat (ResidueField O) n := by
    rw [map_right u hK (mem_left hT _), map_left u hK hT, hJ]
    rfl
  unfold thetaLie
  rw [← e]
  ext i j
  exact evk_neg u (mem_right (mem_left hT _) _ i j)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_evk :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (K : Ideal C) (u : K →ₗ[O] ResidueField O), maximalIdeal C * K = ⊥ → K ≤ maximalIdeal C → ∀ Z : Matrix (Fin n) (Fin n) C, (∀ i j, Z i j ∈ K) → (∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 ∧ (Z + Z').map (evK K u) = Z.map (evK K u) + Z'.map (evK K u) ∧ (Z - Z').map (evK K u) = Z.map (evK K u) - Z'.map (evK K u)) ∧ (∀ A : Matrix (Fin n) (Fin n) C, (∀ i j, (A * Z) i j ∈ K ∧ (Z * A) i j ∈ K) ∧ (A * Z).map (evK K u) = A.map (res O C) * Z.map (evK K u) ∧ (Z * A).map (evK K u) = Z.map (evK K u) * A.map (res O C)) ∧ ∀ x : GG (m := n) (R := C), (∀ i j, x.adFun Z i j ∈ K) ∧ (x.adFun Z).map (evK K u) = (GG.map (res O C : C →+* ResidueField O) x).adFun (Z.map (evK K u)) ∧ ∀ z : GL (Fin n) C, (z : Matrix (Fin n) (Fin n) C) = 1 + Z → (x * GG.ofGL z * x⁻¹).mat = 1 + x.adFun Z := by
  intro O _ _ C _ _ _ n K u hK hKm Z hZ
  have hsq : ∀ Z' : Matrix (Fin n) (Fin n) C, (∀ i j, Z' i j ∈ K) → Z * Z' = 0 := fun Z' hZ' => by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := Ideal.mul_mem_mul (hKm (hZ i k)) (hZ' k j)
    rwa [hK, Ideal.mem_bot] at this
  refine ⟨fun Z' hZ' => ⟨hsq Z' hZ', ?_, ?_⟩,
    fun A => ⟨fun i j => ⟨mem_left hZ A i j, mem_right hZ A i j⟩, map_left u hK hZ A, map_right u hK hZ A⟩,
    fun x => ?_⟩
  · ext i j
    exact evk_add u (hZ i j) (hZ' i j)
  · ext i j
    exact evk_sub u (hZ i j) (hZ' i j)
  have hY : ∀ i j, (if x.right = 1 then Z else thetaLie Z) i j ∈ K := fun i j => by
    split_ifs
    · exact hZ i j
    · exact mem_theta hZ i j
  refine ⟨mem_right (mem_left hY _) _, ?_, fun z hz => ?_⟩
  · have hY' : (if x.right = 1 then Z else thetaLie Z).map (evK K u) =
        if x.right = 1 then Z.map (evK K u) else thetaLie (Z.map (evK K u)) := by
      split_ifs
      · rfl
      · exact map_thetaLie u hK hZ
    unfold GG.adFun
    rw [map_right u hK (mem_left hY _), map_left u hK hY, hY']
    rfl
  · have hinv : ((z⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = 1 - Z := by
      have : (z : Matrix (Fin n) (Fin n) C) * (1 - Z) = 1 := by
        rw [hz, add_mul, mul_sub, mul_sub, hsq Z hZ]
        simp
      exact Units.inv_eq_of_mul_eq_one_right this
    have hl : (x * GG.ofGL z * x⁻¹).left = x.left * sgnAct n C x.right z * x.left⁻¹ := by
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one,
        ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    have hs : ((sgnAct n C x.right z : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
        1 + (if x.right = 1 then Z else thetaLie Z) := by
      rcases Int.units_eq_one_or x.right with h | h
      · rw [h, sgnAct_one, if_pos rfl, hz]
      · rw [h, sgnAct_neg_one, if_neg (by decide), theta_val, hinv, thetaLie, Matrix.transpose_sub,
          Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jmat_mul_Jmat,
          sub_eq_add_neg]
    unfold GG.adFun GG.mat
    rw [hl, Units.val_mul, Units.val_mul, hs, mul_add, add_mul, mul_one, Units.mul_inv]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSetlift
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.InfPowBot
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ maximalIdeal R ^ (k + 1) • (⊤ : Submodule R R) ⊓ (I : Submodule R R) := by
    refine ⟨?_, hxI⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hxm
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hle : maximalIdeal R • (maximalIdeal R ^ k • (⊤ : Submodule R R) ⊓ (I : Submodule R R))
      ≤ maximalIdeal R • (I : Submodule R R) :=
    Submodule.smul_mono le_rfl inf_le_right
  have hx' := hle hx
  rw [Ideal.smul_eq_mul, h] at hx'
  exact (Submodule.mem_bot R).1 hx'

theorem UpperTheory.V.Fr.pr_sec :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → ∀ (Γ : Type) [TopologicalSpace Γ] (x : Γ → C), AdicCont (maximalIdeal C) x → ∃ y : Γ → C', AdicCont (maximalIdeal C') y ∧ ∀ g, p (y g) = x g := by
  intro O _ _ C' _ _ _ C _ _ _ p hp hker Γ _ x hx
  have hmem : ∀ z : C', p z ∈ maximalIdeal C ↔ z ∈ maximalIdeal C' := by
    intro z
    rw [← res_eq_zero_iff O C, ← res_eq_zero_iff O C', res_map]
  have hmap : Ideal.map p (maximalIdeal C') = maximalIdeal C := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (hmem z).2 hz
    · intro c hc
      obtain ⟨z, rfl⟩ := hp c
      exact Ideal.mem_map_of_mem p ((hmem z).1 hc)
  have hpow : ∀ n : ℕ, ∀ c ∈ maximalIdeal C ^ n, ∃ z ∈ maximalIdeal C' ^ n, p z = c := by
    intro n c hc
    rw [← hmap, ← Ideal.map_pow] at hc
    exact (Ideal.mem_map_iff_of_surjective p hp).1 hc
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  obtain ⟨N₀, hN₀⟩ := inf_pow_bot C' (RingHom.ker p) hker
  have hq : Function.Surjective (fun z : C' => Ideal.Quotient.mk (maximalIdeal C ^ N₀) (p z)) :=
    Ideal.Quotient.mk_surjective.comp hp
  let σ := Function.surjInv hq
  have hσ : ∀ c : C, c - p (σ (Ideal.Quotient.mk _ c)) ∈ maximalIdeal C ^ N₀ := by
    intro c
    apply Ideal.Quotient.eq.1
    exact (Function.surjInv_eq hq (Ideal.Quotient.mk _ c)).symm
  have hw : ∀ c : C, ∃ w ∈ maximalIdeal C' ^ N₀, p w = c - p (σ (Ideal.Quotient.mk _ c)) :=
    fun c => hpow N₀ _ (hσ c)
  choose w hwm hwp using hw
  let s : C → C' := fun c => σ (Ideal.Quotient.mk (maximalIdeal C ^ N₀) c) + w c
  have hs : ∀ c, p (s c) = c := by
    intro c
    simp only [s, map_add (f := _), hwp]
    ring
  have hsd : ∀ n ≥ N₀, ∀ c₁ c₂ : C, c₁ - c₂ ∈ maximalIdeal C ^ n →
      s c₁ - s c₂ ∈ maximalIdeal C' ^ n := by
    intro n hn c₁ c₂ h
    have hcl : Ideal.Quotient.mk (maximalIdeal C ^ N₀) c₁ = Ideal.Quotient.mk _ c₂ :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right hn h)
    obtain ⟨z, hz, hpz⟩ := hpow n _ h
    have hdiff : s c₁ - s c₂ = w c₁ - w c₂ := by
      simp only [s, hcl]
      ring
    have hz0 : (s c₁ - s c₂) - z = 0 := by
      apply hN₀
      · rw [RingHom.mem_ker]
        simp [map_sub, hs, hpz]
      · rw [hdiff]
        exact sub_mem (sub_mem (hwm c₁) (hwm c₂)) (Ideal.pow_le_pow_right hn hz)
    rw [sub_eq_zero.1 hz0]
    exact hz
  refine ⟨fun g => s (x g), ?_, fun g => hs (x g)⟩
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hxl := (IsLocallyConstant.iff_eventually_eq _).1 (hx (max n N₀)) g
  filter_upwards [hxl] with g' hg'
  apply Ideal.Quotient.eq.2
  exact Ideal.pow_le_pow_right (le_max_left n N₀)
    (hsd _ (le_max_right _ _) _ _ (Ideal.Quotient.eq.1 hg'))
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ac_const {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem ac_sum {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} (S : Finset ι)
    {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun s => ∑ i ∈ S, f i s := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (∑ i ∈ S, f i s)) = ∑ i ∈ S, fun s => Ideal.Quotient.mk (I ^ N) (f i s) := by
    funext s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply]
  rw [e]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb) (IsLocallyConstant.const 0) (fun i _ => hf i N)

private theorem gl_lift {n : ℕ} (O : Type) [CommRing O] [IsLocalRing O] (C' : Type) [CommRing C'] [Algebra O C']
    [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (hp : Function.Surjective p)
    (hk : maximalIdeal C' * RingHom.ker p = ⊥) (Γ : Type) [TopologicalSpace Γ] (x : Γ → GL (Fin n) C)
    (hx : ∀ i j, AdicCont (maximalIdeal C) fun s => x s i j) :
    ∃ y : Γ → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = x s) ∧
      ∀ i j, (∀ s, x s i j = 0) → ∀ s, y s i j = 0 := by
  classical
  have hloc : ∀ a : C', IsUnit (p a) → IsUnit a := by
    intro a ha
    by_contra hna
    obtain ⟨b, hb⟩ := hp (↑ha.unit⁻¹ : C)
    have hK : a * b - 1 ∈ RingHom.ker (p : C' →+* C) := by
      rw [RingHom.mem_ker]
      show p (a * b - 1) = 0
      rw [map_sub, map_mul, map_one, hb, IsUnit.mul_val_inv, sub_self]
    have hKm : RingHom.ker (p : C' →+* C) ≤ maximalIdeal C' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have ham : a ∈ maximalIdeal C' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hna
    have h1 : (1 : C') ∈ maximalIdeal C' := by
      have h2 := sub_mem (Ideal.mul_mem_right b _ ham) (hKm hK)
      simpa using h2
    exact (maximalIdeal.isMaximal C').ne_top ((Ideal.eq_top_iff_one _).2 h1)
  let Y : Fin n → Fin n → Γ → C' := fun i j =>
    if ∀ s, x s i j = 0 then fun _ => 0 else Classical.choose (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))
  have hYc : ∀ i j, AdicCont (maximalIdeal C') (Y i j) := by
    intro i j
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h]
      exact fun _ => IsLocallyConstant.const _
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).1
  have hYp : ∀ i j s, p (Y i j s) = x s i j := by
    intro i j s
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h, map_zero]
      exact (h s).symm
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).2 s
  have hY0 : ∀ i j, (∀ s, x s i j = 0) → ∀ s, Y i j s = 0 := by
    intro i j h s
    simp only [Y, if_pos h]
  let M : Γ → Matrix (Fin n) (Fin n) C' := fun s => Matrix.of fun i j => Y i j s
  have hMp : ∀ s, (M s).map p = (x s : Matrix (Fin n) (Fin n) C) := by
    intro s
    ext i j
    exact hYp i j s
  have hdet : ∀ s, IsUnit (M s).det := by
    intro s
    apply hloc
    have e : p (M s).det = ((M s).map p).det := RingHom.map_det (p : C' →+* C) (M s)
    rw [e, hMp]
    exact Matrix.isUnits_det_units (x s)
  refine ⟨fun s => Matrix.nonsingInvUnit (M s) (hdet s), fun i j => hYc i j, fun s => ?_, fun i j h s => hY0 i j h s⟩
  apply Units.ext
  exact hMp s

theorem UpperTheory.V.Fr.pr_setlift :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → B.Cont (maximalIdeal C) → Nonempty (SetLift p B) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B hp hk hcont
  obtain ⟨r, hrc, hrm, -⟩ := gl_lift O C' C p hp hk F.Γ (fun s => (B.r s).left) (fun i j => hcont i j)
  have hg : ∀ v, ∃ a : GL (Fin n) C', GeneralLinearGroup.map (p : C' →+* C) a = B.g v := by
    intro v
    obtain ⟨y, -, hy, -⟩ := gl_lift O C' C p hp hk Unit (fun _ => B.g v)
      (fun i j N => IsLocallyConstant.of_constant _ (fun _ _ => rfl))
    exact ⟨y (), hy ()⟩
  have ht : ∀ v, ∃ y : F.Gv v → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) ∧
      ∀ s, UpT (y s : Matrix (Fin n) (Fin n) C') := by
    intro v
    have hM : ∀ a b, AdicCont (maximalIdeal C) fun s : F.Gv v => (B.r (F.loc v s)).mat a b :=
      fun a b N => (hcont a b N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))
    have hx : ∀ i j, AdicCont (maximalIdeal C) fun s : F.Gv v => ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) i j := by
      intro i j
      simp only [Units.val_mul, Matrix.mul_apply]
      exact ac_sum _ (f := fun q s => (∑ a, (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q) * ((B.g v)⁻¹ : GL (Fin n) C) q j)
        fun q => ac_mul (ac_sum _ (f := fun a s => (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q)
          fun a => ac_mul (ac_const _ _) (hM a q)) (ac_const _ _)
    obtain ⟨y, hyc, hym, hy0⟩ := gl_lift O C' C p hp hk (F.Gv v) _ hx
    refine ⟨y, hyc, hym, fun s i j hij => hy0 i j (fun s' => B.tri v s' i j hij) s⟩
  choose g hgm using hg
  choose t htc htm htt using ht
  exact ⟨⟨r, hrc, hrm, g, hgm, t, htc, htt, htm⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpBasis
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem par_equiv {ι : Type} [Fintype ι] (v : ι → ZMod 2) :
    ∃ (a g : ℕ) (e : Fin a ⊕ Fin g ≃ ι), ∀ s, v (e s) = Space.Loc.par a g s := by
  classical
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {i // v i = 0}).symm
    (Fintype.equivFin {i // ¬ v i = 0}).symm).trans (Equiv.sumCompl fun i => v i = 0), ?_⟩
  have h2 : ∀ j : ZMod 2, ¬ j = 0 → j = 1 := by decide
  rintro (s | s)
  · exact ((Fintype.equivFin {i // v i = 0}).symm s).2
  · exact h2 _ ((Fintype.equivFin {i // ¬ v i = 0}).symm s).2

theorem UpperTheory.V.Fr.ep_basis :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ J N : Ideal R, (∀ y ∈ J, σ y ∈ J) → (∀ y ∈ N, σ y ∈ N) → maximalIdeal R * J ≤ N → ∃ (a g : ℕ) (z : Fin a ⊕ Fin g → R), (∀ s, z s ∈ J ∧ z s ∈ evp σ (Space.Loc.par a g s)) ∧ J ≤ Ideal.span (Set.range z) ⊔ N ∧ ∀ c : Fin a ⊕ Fin g → O, ∑ s, c s • z s ∈ N → ∀ s, c s ∈ maximalIdeal O := by
  classical
  intro O _ _ _ _ h2 R _ _ _ σ hσ J N hJ hN hmJ
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  obtain ⟨u, hu2, hucomm⟩ : ∃ u : R, u * 2 = 1 ∧ ∀ x, σ (u * x) = u * σ x :=
    ⟨algebraMap O R ↑h2.unit⁻¹, by
      rw [← map_ofNat (algebraMap O R) 2, ← map_mul, h2.val_inv_mul, map_one],
      fun x => by rw [map_mul, AlgHom.commutes]⟩
  have hsg : ∀ p : ZMod 2, sg R p * sg R p = 1 := by
    intro p
    simp only [sg, ← pow_add, ← two_mul, pow_mul]
    simp
  have hsgσ : ∀ p : ZMod 2, σ (sg R p) = sg R p := by
    intro p
    simp [sg]
  have s0 : sg R 0 = 1 := by simp [sg]
  have s1 : sg R 1 = -1 := by
    show (-1 : R) ^ ((1 : ZMod 2).val) = -1
    rw [show (1 : ZMod 2).val = 1 from rfl]
    simp
  let w : T × ZMod 2 → R := fun j => u * (j.1.1 + sg R j.2 * σ j.1.1)
  have hwJ : ∀ j, w j ∈ J := by
    intro j
    have ht : (j.1 : R) ∈ J := hT ▸ Submodule.subset_span j.1.2
    exact J.mul_mem_left _ (J.add_mem ht (J.mul_mem_left _ (hJ _ ht)))
  have hwev : ∀ j, w j ∈ evp σ j.2 := by
    intro j
    show σ (w j) = sg R j.2 * w j
    simp only [w, hucomm, map_add (f := _), map_mul, hσ, hsgσ]
    linear_combination (-(u * σ j.1.1)) * hsg j.2
  have hmemN : ∀ c ∈ maximalIdeal O, ∀ y ∈ J, c • y ∈ N := by
    intro c hc y hy
    rw [Algebra.smul_def]
    exact hmJ (Ideal.mul_mem_mul (map_nonunit (algebraMap O R) c hc) hy)
  let Indep : Finset (T × ZMod 2) → Prop := fun S =>
    ∀ c : T × ZMod 2 → O, ∑ s ∈ S, c s • w s ∈ N → ∀ s ∈ S, c s ∈ maximalIdeal O
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset.filter Indep) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨by simp, fun c _ s hs => absurd hs (Finset.notMem_empty s)⟩⟩
  have hS' : Indep S := (Finset.mem_filter.mp hS).2
  obtain ⟨a, g, e, he⟩ := par_equiv (ι := S) (fun i => i.1.2)
  refine ⟨a, g, fun s => w (e s).1, ?_, ?_, ?_⟩
  · intro s
    refine ⟨hwJ _, ?_⟩
    rw [← he s]
    exact hwev _
  · have hspan : ∀ j, w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
      intro j
      by_cases hj : j ∈ S
      · exact Ideal.mem_sup_left (Ideal.subset_span ⟨e.symm ⟨j, hj⟩, by simp⟩)
      · have hnot : ¬ Indep (insert j S) := by
          intro hI
          have := hmax (insert j S) (Finset.mem_filter.mpr ⟨by simp, hI⟩)
          rw [Finset.card_insert_of_notMem hj] at this
          omega
        simp only [Indep, not_forall] at hnot
        obtain ⟨c, hc, s, hs, hcs⟩ := hnot
        rw [Finset.sum_insert hj] at hc
        have hcj : c j ∉ maximalIdeal O := by
          intro hcj
          have h1 : c j • w j ∈ N := hmemN _ hcj _ (hwJ j)
          have h2' : ∑ s ∈ S, c s • w s ∈ N := by
            have := N.sub_mem hc h1
            simpa using this
          rcases Finset.mem_insert.mp hs with rfl | hs
          · exact hcs hcj
          · exact hcs (hS' c h2' s hs)
        have hunit : IsUnit (c j) := by
          by_contra h
          exact hcj ((IsLocalRing.mem_maximalIdeal _).mpr h)
        have hsumS : ∑ s ∈ S, c s • w s ∈ Ideal.span (Set.range fun s => w (e s).1) := by
          refine Ideal.sum_mem _ fun s hs => ?_
          rw [Algebra.smul_def]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e.symm ⟨s, hs⟩, by simp⟩)
        have hcw : c j • w j ∈ Ideal.span (Set.range fun s => w (e s).1) ⊔ N := by
          have : c j • w j = (c j • w j + ∑ s ∈ S, c s • w s) - ∑ s ∈ S, c s • w s := by
            abel
          rw [this]
          exact Submodule.sub_mem _ (Ideal.mem_sup_right hc) (Ideal.mem_sup_left hsumS)
        obtain ⟨d, hd⟩ := hunit.exists_left_inv
        have : w j = d • (c j • w j) := by rw [smul_smul, hd, one_smul]
        rw [this, Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hcw
    rw [← hT]
    show Submodule.span R (T : Set R) ≤ _
    rw [Submodule.span_le]
    intro t ht
    have : t = w (⟨t, ht⟩, 0) + w (⟨t, ht⟩, 1) := by
      simp only [w, s0, s1]
      linear_combination (-t) * hu2
    rw [this]
    exact Submodule.add_mem _ (hspan _) (hspan _)
  · intro c hc s
    let c' : T × ZMod 2 → O := fun j => if h : j ∈ S then c (e.symm ⟨j, h⟩) else 0
    have hsum : ∑ j ∈ S, c' j • w j = ∑ s, c s • w (e s).1 := by
      rw [← Finset.sum_coe_sort S, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [c']
    have := hS' c' (hsum ▸ hc) (e s).1 (e s).2
    simpa [c'] using this
end
