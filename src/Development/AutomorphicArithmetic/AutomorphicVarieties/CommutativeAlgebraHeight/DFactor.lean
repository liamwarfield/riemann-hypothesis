module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E']
  (f : E →ₐ[A] E')

private theorem map_eq_lTensor (S : Type) [CommRing S] [Algebra A S] (z : S ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id S S) f z = f.toLinearMap.lTensor S z := by
  induction z with
  | tmul s x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective S (g := f.toLinearMap) hf y
  exact ⟨x, (map_eq_lTensor f S x).trans hx⟩

private theorem eq_of_map_eq (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → x ∈ D.ker)
    (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E)
    (h : Algebra.TensorProduct.map (AlgHom.id S S) f x = Algebra.TensorProduct.map (AlgHom.id S S) f y) :
    D.D S x = D.D S y := by
  have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  have h0 : f.toLinearMap.lTensor S (x - y) = 0 := by
    rw [← map_eq_lTensor, map_sub, h, sub_self]
  obtain ⟨w, hw⟩ := (hex _).1 h0
  have key : ∀ (w : S ⊗[A] (LinearMap.ker f.toLinearMap)) (y : S ⊗[A] E),
      D.D S (y + (LinearMap.ker f.toLinearMap).subtype.lTensor S w) = D.D S y := by
    intro w
    induction w with
    | tmul s k =>
      intro y
      have := (D.mem_ker.1 (hk k.1 k.2)) S y (s ⊗ₜ 1) 1
      simpa using this
    | add a b ha hb => intro y; rw [LinearMap.map_add (f := _), ← add_assoc, hb, ha]
  rw [← key w y, hw, add_sub_cancel]

private theorem map_map_swap (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (g : B →ₐ[A] B')
    (x : B ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id B' B') f (Algebra.TensorProduct.map g (AlgHom.id A E) x) =
      Algebra.TensorProduct.map g (AlgHom.id A E') (Algebra.TensorProduct.map (AlgHom.id B B) f x) := by
  induction x with
  | tmul s x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end

theorem UpperTheory.V.CA.d_factor :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E →ₐ[A] E'), Function.Surjective f → (∀ x, f x = 0 → x ∈ D.ker) → ∃! D' : Det n A E', D'.pull f = D := by
  intro n A E _ _ _ D E' _ _ f hf hk
  have hs := map_surj f hf
  have he := eq_of_map_eq D f hf hk
  have hσ : ∀ (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] E),
      D.D S (Function.surjInv (hs S) (Algebra.TensorProduct.map (AlgHom.id S S) f x)) = D.D S x :=
    fun S _ _ x => he S _ _ (Function.surjInv_eq _ _)
  let D' : Det n A E' :=
    { D := fun S _ _ =>
        { toFun := fun y => D.D S (Function.surjInv (hs S) y)
          map_one' := by
            rw [← map_one (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, map_one]
          map_mul' := fun x y => by
            obtain ⟨x, rfl⟩ := hs S x
            obtain ⟨y, rfl⟩ := hs S y
            rw [← map_mul (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, hσ, hσ, map_mul] }
      nat := fun B B' _ _ _ _ g x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B' (Function.surjInv (hs B') _) = g (D.D B (Function.surjInv (hs B) _))
        rw [← map_map_swap, hσ, hσ, D.nat]
      homog := fun B _ _ b x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B (Function.surjInv (hs B) _) = b ^ n * D.D B (Function.surjInv (hs B) _)
        rw [← map_smul, hσ, hσ, D.homog] }
  refine ⟨D', Det.ext' fun S _ _ x => hσ S x, fun D'' h => Det.ext' fun S _ _ y => ?_⟩
  obtain ⟨x, rfl⟩ := hs S y
  refine Eq.trans ?_ (hσ S x).symm
  rw [← h]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClQuot
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem maximalIdeal_map_eq_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : (maximalIdeal R).map f = maximalIdeal R' := by
  have hk : RingHom.ker f ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (f := f) hf (I := maximalIdeal R)
      (maximalIdeal.isMaximal R) with h | h
  · exfalso
    have h1 : (1 : R') ∈ (maximalIdeal R).map f := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective f hf).1 h1
    have hker : 1 - y ∈ RingHom.ker f := by simp [RingHom.mem_ker, hy1]
    have h2 := Ideal.add_mem _ (hk hker) hy
    rw [sub_add_cancel] at h2
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · exact IsLocalRing.eq_maximalIdeal h

private theorem isLocalHom_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hx' : x ∈ maximalIdeal R := h
  have : f x ∈ maximalIdeal R' := by
    rw [← maximalIdeal_map_eq_of_surjective f hf]
    exact Ideal.mem_map_of_mem f hx'
  exact this hx

private theorem smodEq_ideal_pow_smul_univ_iff_sub_mem {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (a b : A) :
    a ≡ b [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ a - b ∈ I ^ n := by
  simp [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem UpperTheory.V.CA.cl_quot :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ p hp hR
  have hpr : Function.Surjective (p : R →+* R') := hp
  haveI : IsLocalHom (p : R →+* R') := isLocalHom_of_surjective _ hpr
  haveI := hR.noeth
  haveI : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hpr
  haveI := hR.complete
  have hm : maximalIdeal R' = (maximalIdeal R).map (p : R →+* R') := (maximalIdeal_map_eq_of_surjective _ hpr).symm
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · haveI : IsHausdorff (maximalIdeal R') R' := inferInstance
    refine { toIsHausdorff := inferInstance, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
    have hd : ∀ n, ∃ d ∈ maximalIdeal R ^ n, p d = f (n + 1) - f n := by
      intro n
      have h0 := (smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hf (Nat.le_succ n))
      rw [hm, ← Ideal.map_pow] at h0
      obtain ⟨d, hd, hd'⟩ := (Ideal.mem_map_iff_of_surjective _ hpr).1 (neg_mem h0)
      refine ⟨d, hd, ?_⟩
      rw [neg_sub] at hd'
      exact hd'
    choose d hdm hdp using hd
    obtain ⟨y0, hy0⟩ := hp (f 0)
    have hy : ∀ n, p (y0 + ∑ k ∈ Finset.range n, d k) = f n := by
      intro n
      induction n with
      | zero => simp [hy0]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _), ih, hdp]
        ring
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (y0 + ∑ k ∈ Finset.range m, d k) ≡ (y0 + ∑ k ∈ Finset.range n, d k)
          [SMOD (maximalIdeal R ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [smodEq_ideal_pow_smul_univ_iff_sub_mem]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have e : (y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range (n + 1), d k) =
            ((y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range n, d k)) - d n := by
          rw [Finset.sum_range_succ]
          ring
        rw [e]
        exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hmn (hdm n))
    obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (maximalIdeal R) R).prec'
      (fun n => y0 + ∑ k ∈ Finset.range n, d k) hcauchy
    refine ⟨p L, fun n => ?_⟩
    rw [smodEq_ideal_pow_smul_univ_iff_sub_mem, hm, ← Ideal.map_pow, ← hy n, ← map_sub]
    exact Ideal.mem_map_of_mem (p : R →+* R') ((smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hL n))
  · refine ⟨fun x hx => ?_⟩
    have e : algebraMap O R' x = (p : R →+* R') (algebraMap O R x) := (p.commutes x).symm
    rw [e] at hx
    exact hR.isLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ hx)
  · let L : ResidueField R →ₗ[O] ResidueField R' :=
      { toFun := IsLocalRing.ResidueField.map (p : R →+* R')
        map_add' := map_add _
        map_smul' := by
          intro o x
          obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
          simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
          congr 1
          rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
            IsScalarTower.algebraMap_apply O R' (ResidueField R')]
          change IsLocalRing.ResidueField.map _ (residue R _) = residue R' _
          rw [IsLocalRing.ResidueField.map_residue]
          simp }
    have hL : Function.Surjective L := by
      intro z
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨y, rfl⟩ := hpr y'
      exact ⟨IsLocalRing.residue R y, IsLocalRing.ResidueField.map_residue _ _⟩
    haveI := hR.res_fin
    exact Module.Finite.of_surjective L hL
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClFin
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

theorem UpperTheory.V.CA.cl_fin :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'], IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ _ _ _ h
  haveI := h.noeth
  haveI := h.complete
  haveI := h.isLocalHom
  haveI := h.res_fin
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hIntegral : (algebraMap R R').IsIntegral :=
    RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap R R') hIntegral (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R') hIntegral P
        (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (isPrecomplete_finite _))
  haveI hloc : IsLocalHom (algebraMap R R') := ⟨fun a ha => by
    by_contra hn
    have h1 : a ∈ maximalIdeal R := hn
    rw [← hcomap, Ideal.mem_comap] at h1
    exact h1 ha⟩
  haveI hT : IsScalarTower O (ResidueField R) (ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
        ← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField R'),
        IsScalarTower.algebraMap_apply O R' (ResidueField R'),
        IsScalarTower.algebraMap_apply R R' (ResidueField R'),
        IsScalarTower.algebraMap_apply O R R']
  exact
    { noeth := hN
      complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
      isLocalHom := by
        rw [IsScalarTower.algebraMap_eq O R R']
        infer_instance
      res_fin := Module.Finite.trans (ResidueField R) (ResidueField R') }
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnopMemCH
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section SlopeTestRemainingChoices

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E]

private theorem unopS_tmul (S : Type) [CommRing S] [Algebra A S] (s : S) (a : Eᵐᵒᵖ) :
    Det.unopS A E S (s ⊗ₜ a) = s ⊗ₜ a.unop := by
  simp [Det.unopS]

private theorem unopS_surj (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    ∃ z, Det.unopS A E S z = y := by
  induction y with
  | tmul s a => exact ⟨s ⊗ₜ MulOpposite.op a, unopS_tmul S s _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩

private theorem op_D (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] Eᵐᵒᵖ) :
    D.op.D S x = D.D S (Det.unopS A E S x) := rfl

private theorem unopS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (φ : S →ₐ[A] T)
    (x : S ⊗[A] Eᵐᵒᵖ) :
    Det.unopS A E T (Algebra.TensorProduct.map φ (AlgHom.id A _) x) =
      Algebra.TensorProduct.map φ (AlgHom.id A E) (Det.unopS A E S x) := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s a => simp [Det.unopS]

private theorem op_chiS (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) :
    D.op.chiS S y = D.chiS S (Det.unopS A E S y) := by
  unfold Det.chiS
  rw [op_D, map_sub, unopS_map, unopS_tmul, MulOpposite.unop_one]

private theorem unopS_pow (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (k : ℕ) :
    Det.unopS A E S (y ^ k) = Det.unopS A E S y ^ k := by
  induction k with
  | zero => simp [Det.unopS, Algebra.TensorProduct.one_def]
  | succ k ih => rw [pow_succ, Det.unopS_mul, ih, pow_succ']

private theorem unopS_aeval (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] Eᵐᵒᵖ) (p : Polynomial S) :
    Det.unopS A E S (Polynomial.aeval y p) = Polynomial.aeval (Det.unopS A E S y) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial k s =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, unopS_pow]

private theorem unopS_gen {k : ℕ} (x : Fin k → Eᵐᵒᵖ) :
    Det.unopS A E _ (Det.gen (A := A) x) = Det.gen (A := A) fun a => (x a).unop := by
  unfold Det.gen
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => unopS_tmul _ _ _

private theorem lid_unopS (S : Type) [CommRing S] [Algebra A S] (f : S →ₗ[A] A) (y : S ⊗[A] Eᵐᵒᵖ) :
    (TensorProduct.lid A Eᵐᵒᵖ (f.rTensor Eᵐᵒᵖ y)).unop =
      TensorProduct.lid A E (f.rTensor E (Det.unopS A E S y)) := by
  induction y with
  | add a b ha hb => simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
  | tmul s a => simp [unopS_tmul]

private theorem op_chElt (D : Det n A E) {k : ℕ} (x : Fin k → Eᵐᵒᵖ) (α : Fin k →₀ ℕ) :
    (D.op.chElt x α).unop = D.chElt (fun a => (x a).unop) α := by
  unfold Det.chElt
  rw [lid_unopS, unopS_aeval, op_chiS, unopS_gen]

private theorem unop_mem_CH (D : Det n A E) {x : Eᵐᵒᵖ} (h : x ∈ D.op.CH) : x.unop ∈ D.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, _, α, op_chElt D y α⟩
  | zero => exact D.CH.zero_mem
  | add x y _ _ hx hy => exact D.CH.add_mem hx hy
  | neg x _ hx => exact D.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.CH.mul_mem_left _ _ hx

private theorem op_mem_CH (D : Det n A E) {x : E} (h : x ∈ D.CH) : MulOpposite.op x ∈ D.op.CH := by
  unfold Det.CH at h
  induction h using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨k, y, α, rfl⟩ := hx
    exact TwoSidedIdeal.subset_span ⟨k, fun a => MulOpposite.op (y a), α,
      (congrArg MulOpposite.op (op_chElt D (fun a => MulOpposite.op (y a)) α)).symm⟩
  | zero => exact D.op.CH.zero_mem
  | add x y _ _ hx hy => exact D.op.CH.add_mem hx hy
  | neg x _ hx => exact D.op.CH.neg_mem hx
  | left_absorb a x _ hx => exact D.op.CH.mul_mem_right _ _ hx
  | right_absorb b x _ hx => exact D.op.CH.mul_mem_left _ _ hx

end SlopeTestRemainingChoices

theorem UpperTheory.V.CA.d_op :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (∀ x, D.op.chi (MulOpposite.op x) = D.chi x) ∧ (∀ x, MulOpposite.op x ∈ D.op.ker ↔ x ∈ D.ker) ∧ ∀ x, MulOpposite.op x ∈ D.op.CH ↔ x ∈ D.CH := by
  intro n A E _ _ _ D
  refine ⟨fun x => ?_, fun x => ?_, fun x => ⟨fun h => unop_mem_CH D h, op_mem_CH D⟩⟩
  · unfold Det.chi
    rw [op_D, map_sub, unopS_tmul, unopS_tmul, MulOpposite.unop_one, MulOpposite.unop_op]
  · rw [Det.mem_ker, Det.mem_ker]
    constructor
    · intro h S _ _ y u v
      obtain ⟨y, rfl⟩ := unopS_surj S y
      obtain ⟨u, rfl⟩ := unopS_surj S u
      obtain ⟨v, rfl⟩ := unopS_surj S v
      have := h S y v u
      rw [op_D, op_D, map_add (f := _), Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc] at this
      exact this
    · intro h S _ _ y u v
      rw [op_D, op_D, map_add (f := _), Det.unopS_mul, Det.unopS_mul, unopS_tmul, MulOpposite.unop_op, ← mul_assoc]
      exact h S _ _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DLiftIdem
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem dli_left_inv {E : Type} [Ring E] {j : E} (hj : j ∈ Ring.jacobson E) :
    ∃ z : E, z * (1 - j) = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hj
  obtain ⟨z, hz⟩ := hj (-1)
  rw [Ideal.mem_bot] at hz
  refine ⟨z, ?_⟩
  rw [← sub_eq_zero, ← hz]
  noncomm_ring

private theorem dli_idem_zero {E : Type} [Ring E] {u : E} (hu : IsIdempotentElem u)
    (hj : u ∈ Ring.jacobson E) : u = 0 := by
  obtain ⟨z, hz⟩ := dli_left_inv hj
  calc u = z * (1 - u) * u := by rw [hz, one_mul]
    _ = 0 := by rw [mul_assoc, sub_mul, one_mul, hu.eq, sub_self, mul_zero]

private theorem dli_mem_max {A B E : Type} [CommRing A] [CommRing B] [Ring E] [Algebra A B] [Algebra A E]
    [Algebra.IsIntegral A E] (ι : B →ₐ[A] E) (hι : Function.Injective ι) {y : B}
    (hy : ι y ∈ Ring.jacobson E) (M : Ideal B) (hM : M.IsMaximal) : y ∈ M := by
  by_contra hyM
  obtain ⟨b, m, hm, hbm⟩ := hM.exists_inv hyM
  have h1 : ι (b * y) ∈ Ring.jacobson E := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  obtain ⟨z, hz⟩ := dli_left_inv h1
  have hm' : 1 - ι (b * y) = ι m := by
    rw [← map_one ι, ← map_sub, ← hbm]; simp
  rw [hm'] at hz
  obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := A) z
  have hpow : ∀ i : ℕ, z ^ i * ι m ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ z, pow_succ' (ι m), mul_assoc, ← mul_assoc z, hz, one_mul, ih]
  rw [← aeval_def, aeval_eq_sum_range] at hp0
  have h2 : ι (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • m ^ (p.natDegree - i)) = ι 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, ← zero_mul (ι m ^ p.natDegree), ← hp0, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [map_smul, map_pow, smul_mul_assoc]
    congr 1
    conv_rhs => rw [← Nat.add_sub_cancel' hi', pow_add, ← mul_assoc, hpow, one_mul]
  have h3 := hι h2
  rw [Finset.sum_range_succ, hp.coeff_natDegree, Nat.sub_self, pow_zero, one_smul] at h3
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_right h3]
  refine M.neg_mem (M.sum_mem fun i hi => ?_)
  rw [Algebra.smul_def]
  exact M.mul_mem_left _ (M.pow_mem_of_mem hm _ (Nat.sub_pos_of_lt (Finset.mem_range.1 hi)))

private theorem dli_comm {A B F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Ring F] (φ : B →+* F) (x : B)
    (hx : IsIdempotentElem (φ x)) (hy : ∀ M : Ideal B, M.IsMaximal → x - x ^ 2 ∈ M) :
    ∃ e : B, IsIdempotentElem e ∧ φ e = φ x := by
  set K : Ideal B := (maximalIdeal A).map (algebraMap A B) with hK
  haveI : IsAdicComplete K B := GlobalTheory.isAdicComplete_map_of_finite _ B
  have hrad : x - x ^ 2 ∈ K.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hKP, hP⟩
    refine hy P (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) P ?_)
    have : maximalIdeal A = P.under A :=
      (maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hKP)
    rw [← this]; exact maximalIdeal.isMaximal A
  obtain ⟨n, hn⟩ := hrad
  have hn' : (x - x ^ 2) ^ (n + 1) ∈ K := by rw [pow_succ]; exact K.mul_mem_right _ hn
  set a : B := 1 - (1 - x ^ (n + 1)) ^ (n + 1) with ha
  have hφa : φ a = φ x := by
    simp only [ha, map_sub, map_one, map_pow, hx.pow_succ_eq, hx.one_sub.pow_succ_eq, sub_sub_cancel]
  have h0 : a ^ 2 - a ∈ K := by
    have := isIdempotentElem_one_sub_one_sub_pow_pow (Ideal.Quotient.mk K x) (n + 1) (by
      rw [← map_pow, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn')
    rw [← Ideal.Quotient.eq, sq, map_mul]
    simpa [ha] using this.eq
  obtain ⟨e, he, he'⟩ := HenselianRing.is_henselian (I := K) (Polynomial.X ^ 2 - Polynomial.X : B[X])
    (by nontriviality B; monicity!) a (by simpa using h0) (by
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk K (2 * a - 1)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq]
      convert K.mul_mem_left 4 h0 using 1
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one]
      push_cast
      ring)
  have he2 : e * e - e = 0 := by simpa [sq] using he
  refine ⟨e, sub_eq_zero.1 he2, ?_⟩
  have hu : IsUnit ((e - a) * (-(e - a)) + 1) := Ring.mem_jacobson_iff.1 (HenselianRing.jac he') _
  have hk : a ^ 2 - a ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, map_pow, hφa, sq, hx.eq, sub_self]
  have hd : (e - a) * ((e - a) * (-(e - a)) + 1) ∈ RingHom.ker φ := by
    have : (e - a) * ((e - a) * (-(e - a)) + 1) = -(3 * e - a - 1) * (a ^ 2 - a) := by
      linear_combination (-(e + 1 - 3 * a)) * he2
    rw [this]; exact Ideal.mul_mem_left _ _ hk
  rw [Ideal.mul_unit_mem_iff_mem _ hu, RingHom.mem_ker, map_sub, sub_eq_zero] at hd
  rw [hd, hφa]

section

variable {A E F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A]
  [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] (π : E →ₐ[A] F)

private theorem dli_one (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E) (x : E) (hx : IsIdempotentElem (π x)) :
    ∃ e ∈ Algebra.adjoin A {x}, IsIdempotentElem e ∧ π e = π x := by
  haveI : Module.Finite A (Algebra.adjoin A {x}) :=
    Module.Finite.iff_fg.2 (Algebra.IsIntegral.isIntegral (R := A) x).fg_adjoin_singleton
  obtain ⟨e, he, he'⟩ := dli_comm (A := A) (B := Algebra.adjoin A {x})
    (π.comp (Algebra.adjoin A {x}).val).toRingHom ⟨x, Algebra.self_mem_adjoin_singleton A x⟩ hx
    (dli_mem_max (Algebra.adjoin A {x}).val Subtype.val_injective (hk _ (by
      simp [sq, hx.eq])))
  exact ⟨e, e.2, congrArg Subtype.val he.eq, he'⟩

private theorem dli_orth (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    (e₁ : F) (he₁ : IsIdempotentElem e₁) (e₂ : E) (he₂ : IsIdempotentElem e₂)
    (h₁ : e₁ * π e₂ = 0) (h₂ : π e₂ * e₁ = 0) :
    ∃ e' : E, IsIdempotentElem e' ∧ π e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  obtain ⟨y, rfl⟩ := hs e₁
  have hx : π ((1 - e₂) * y * (1 - e₂)) = π y := by
    simp only [map_mul, map_sub, map_one, sub_mul, mul_sub, one_mul, mul_one, h₁, h₂, zero_mul, sub_zero]
  obtain ⟨e, hm, he, he'⟩ := dli_one π hk ((1 - e₂) * y * (1 - e₂)) (hx ▸ he₁)
  rw [hx] at he'
  have hc0 : Commute e₂ ((1 - e₂) * y * (1 - e₂)) := by
    rw [Commute, SemiconjBy, ← mul_assoc, ← mul_assoc, he₂.mul_one_sub_self, mul_assoc _ (1 - e₂),
      he₂.one_sub_mul_self]
    simp
  have hc : Commute e₂ e := Algebra.commute_of_mem_adjoin_singleton_of_commute hm hc0
  have h0 : e₂ * e = 0 := dli_idem_zero (he₂.mul_of_commute hc he) (hk _ (by rw [map_mul, he', h₂]))
  exact ⟨e, he, he', by rw [← hc.eq, h0], h0⟩

private theorem dli_fin (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    {n : ℕ} {e : Fin n → F} (he : OrthogonalIdempotents e) :
    ∃ e' : Fin n → E, OrthogonalIdempotents e' ∧ π ∘ e' = e := by
  induction n with
  | zero => exact ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n))
    have h₂' (i) : π (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ := dli_orth π hs hk _ (he.idem 0) _ h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

end

theorem UpperTheory.V.CA.d_lift_idem :
    ∀ {A E F ι : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A] [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] [Fintype ι] [DecidableEq ι] (π : E →ₐ[A] F), Function.Surjective π → (∀ x, π x = 0 → x ∈ Ring.jacobson E) → ∀ f : ι → F, CompleteOrthogonalIdempotents f → ∃ e : ι → E, CompleteOrthogonalIdempotents e ∧ ∀ i, π (e i) = f i := by
  intro A E F ι _ _ _ _ _ _ _ _ _ _ _ π hs hk f hf
  obtain ⟨e', h₁, h₂⟩ := dli_fin π hs hk
    (hf.toOrthogonalIdempotents.embedding (Fintype.equivFin ι).symm.toEmbedding)
  have ho := h₁.embedding (Fintype.equivFin ι).toEmbedding
  have hv : ∀ i, π ((e' ∘ (Fintype.equivFin ι).toEmbedding) i) = f i := fun i => by
    simpa using congr_fun h₂ (Fintype.equivFin ι i)
  refine ⟨_, ⟨ho, ?_⟩, hv⟩
  have := dli_idem_zero ho.isIdempotentElem_sum.one_sub (hk _ (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, map_sum, Finset.sum_congr rfl fun i _ => hv i, hf.complete, sub_self]))
  exact (sub_eq_zero.1 this).symm
end
