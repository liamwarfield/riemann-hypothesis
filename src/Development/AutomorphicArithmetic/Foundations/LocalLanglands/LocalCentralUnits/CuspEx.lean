module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodMap
public import Development.AutomorphicArithmetic.WhittakerHecke.ContinuousInertiaRestrictionOfCompat
public import Development.AutomorphicArithmetic.WhittakerHecke.CardResidueFieldAdicCompletionIntegersEqAbsNorm
public import Development.AutomorphicArithmetic.WhittakerHecke.TameInertiaCharacterFrobeniusConjEqPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ParDual
noncomputable section

namespace UpperTheory.Zero.LLC.ParameterDuality

open Polynomial GlobalTheory.PRep GlobalTheory.LocGL

private theorem exists_dual_map {G K Γ V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group K] [Group Γ]
    [Fintype Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (π : Representation ℂ G V) (hπ : IsSmooth π) (ρ : Representation ℂ Γ W)
    (ι : K →* G) (q : K →* Γ) (hq : Function.Surjective q) (H : Subgroup G) (hH : IsCompact (H : Set G))
    (h1 : ∀ k, q k = 1 → ι k ∈ H) (h2 : ∀ x ∈ H, ∃ k, ι k = x ∧ q k = 1)
    (B : W →ₗ[ℂ] Module.Dual ℂ V) (hB : B ≠ 0)
    (hinv : ∀ k w v, B (ρ (q k) w) (π (ι k) v) = B w v) :
    ∃ ψ : Module.Dual ℂ W →ₗ[ℂ] V, ψ ≠ 0 ∧ ∀ k l, ψ (ρ.dual (q k) l) = π (ι k) (ψ l) := by
  classical
  obtain ⟨w0, v1, hv1⟩ : ∃ w v, B w v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB (LinearMap.ext fun w => LinearMap.ext fun v => hc w v)
  have hfix : ∀ (w : W) (x : H) (v : V), B w (π x v) = B w v := fun w x v => by
    obtain ⟨k, hk, hk1⟩ := h2 x x.2
    have := hinv k w v
    rw [hk1, map_one, hk] at this
    simpa using this
  have hker : ∀ w, ∀ u ∈ twKer π H 1, B w u = 0 := fun w u hu => by
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, v, rfl⟩ := hx
      simp [hfix]
    | zero => simp
    | add _ _ _ _ h h' => simp [h, h']
    | smul c _ _ h => simp [h]
  obtain ⟨v0, hv0, b, hb, rfl⟩ : ∃ v0 ∈ fixed π H, ∃ b ∈ twKer π H 1, v0 + b = v1 :=
    Submodule.mem_sup.1 ((isCompl_fixed_twKer hπ hH).sup_eq_top ▸ Submodule.mem_top)
  have hw0 : B w0 v0 ≠ 0 := by simpa [hker w0 b hb] using hv1
  choose s hs using hq
  have hv0' : ∀ k, q k = 1 → π (ι k) v0 = v0 := fun k hk => by
    exact GlobalTheory.Parabolic.mem_fixed.1 hv0 _ (h1 k hk)
  let ψ : Module.Dual ℂ W →ₗ[ℂ] V :=
    ∑ γ : Γ, LinearMap.smulRight (Module.Dual.eval ℂ W (ρ γ w0)) (π (ι (s γ)) v0)
  have hψ : ∀ l, ψ l = ∑ γ : Γ, l (ρ γ w0) • π (ι (s γ)) v0 := fun l => by
    simp [ψ, LinearMap.sum_apply]
  refine ⟨ψ, fun h0 => ?_, fun k l => ?_⟩
  · let f : Module.Dual ℂ W := B.flip v0
    let P : Module.End ℂ W := f.smulRight w0
    let T : Module.End ℂ W := ∑ γ : Γ, ρ γ * P * ρ γ⁻¹
    have hT : T = 0 := by
      refine LinearMap.ext fun w => (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
      have e : B w (ψ l) = 0 := by rw [h0]; simp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hψ, map_sum] at e
      rw [← e]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [T, LinearMap.sum_apply, map_sum, LinearMap.zero_apply]
      refine Finset.sum_congr rfl fun γ _ => ?_
      have e2 := hinv (s γ) (ρ γ⁻¹ w) v0
      rw [hs γ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e2
      simp only [map_smul, e2, smul_eq_mul, Module.End.mul_apply, P, f, LinearMap.smulRight_apply,
        LinearMap.flip_apply]
      ring
    have ht : LinearMap.trace ℂ W T = (Fintype.card Γ : ℂ) * f w0 := by
      have hP : LinearMap.trace ℂ W P = f w0 := by
        have : P = dualTensorHom ℂ W W (f ⊗ₜ w0) := by
          ext x
          simp [P, dualTensorHom_apply]
        rw [this, LinearMap.trace_eq_contract_apply]
        simp
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [T, map_sum]
      have : ∀ γ : Γ, LinearMap.trace ℂ W (ρ γ * P * ρ γ⁻¹) = f w0 := fun γ => by
        rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul, hP]
      simp [this]
    rw [hT, map_zero] at ht
    have hc : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact hw0 (by simpa [f, hc] using ht.symm)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hψ, hψ, map_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft (q k)⁻¹) _ _ fun γ => ?_)
      have e : π (ι (s γ)) v0 = π (ι k) (π (ι (s ((q k)⁻¹ * γ))) v0) := by
        have hu : q ((k * s ((q k)⁻¹ * γ))⁻¹ * s γ) = 1 := by
          simp [hs]
        have e2 : ι (s γ) = ι (k * s ((q k)⁻¹ * γ)) * ι ((k * s ((q k)⁻¹ * γ))⁻¹ * s γ) := by
          rw [← map_mul]
          congr 1
          group
        rw [e2, map_mul π, Module.End.mul_apply, hv0' _ hu, map_mul ι, map_mul π, Module.End.mul_apply]
      simp only [Equiv.coe_mulLeft]
      rw [map_smul, ← e, Representation.dual_apply, map_mul, Module.End.mul_apply]
      rfl

section Finite

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders

variable {g : ℕ} [Fact g.Prime]

private theorem irreducible_reverse {F : Type} [Field F] {p : F[X]} (hp : Irreducible p) (h0 : p.coeff 0 ≠ 0) :
    Irreducible p.reverse := by
  have deg : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → q.reverse.natDegree = q.natDegree := fun {q} h => by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.2 (Or.inr h), Nat.sub_zero]
  have rr : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → q.reverse.reverse = q := fun {q} h => by
    rw [reverse, deg h, reverse, reflect_reflect]
  have un : ∀ {q : F[X]}, q.coeff 0 ≠ 0 → IsUnit q.reverse → IsUnit q := fun {q} h hu => by
    have h1 : q.natDegree = 0 := by rw [← deg h]; exact natDegree_eq_zero_of_isUnit hu
    rw [eq_C_of_natDegree_eq_zero h1]
    exact isUnit_C.2 (IsUnit.mk0 _ h)
  have r0 : p.reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.2 hp.ne_zero
  refine ⟨fun hu => hp.not_isUnit (un h0 hu), fun a b hab => ?_⟩
  have ha : a.coeff 0 ≠ 0 := fun e => r0 (by rw [hab, mul_coeff_zero, e, zero_mul])
  have hb : b.coeff 0 ≠ 0 := fun e => r0 (by rw [hab, mul_coeff_zero, e, mul_zero])
  have e : p = a.reverse * b.reverse := by rw [← reverse_mul_of_domain, ← hab, rr h0]
  exact (hp.isUnit_or_isUnit e).imp (un ha) (un hb)

private theorem charpoly_inv_mul {n : ℕ} (y : Gn g n) :
    ((y⁻¹ : Gn g n) : Mt g n).charpoly * C (y : Mt g n).det = C ((-1) ^ n) * (y : Mt g n).charpoly.reverse := by
  have hY : ((y⁻¹ : Gn g n) : Mt g n) * (y : Mt g n) = 1 := by simp
  have key : Matrix.charmatrix ((y⁻¹ : Gn g n) : Mt g n) * (C : ZMod g →+* (ZMod g)[X]).mapMatrix (y : Mt g n) =
      -(1 - (X : (ZMod g)[X]) • (y : Mt g n).map C) := by
    rw [Matrix.charmatrix, sub_mul, ← map_mul, hY, map_one, neg_sub]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_apply, Matrix.smul_apply]
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, ← RingHom.map_det, Matrix.det_neg] at this
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, Matrix.charpoly, this]
  simp

private theorem irreducible_charpoly_inv {n : ℕ} {y : Gn g n} (h : Irreducible (y : Mt g n).charpoly) :
    Irreducible ((y⁻¹ : Gn g n) : Mt g n).charpoly := by
  have hd : IsUnit (y : Mt g n).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have h0 : (y : Mt g n).charpoly.coeff 0 ≠ 0 := fun e => by
    have := Matrix.det_eq_sign_charpoly_coeff (y : Mt g n)
    rw [e, mul_zero] at this
    exact hd.ne_zero this
  have h1 := irreducible_reverse h h0
  have h2 : IsUnit (C ((-1 : ZMod g) ^ n)) := isUnit_C.2 ((isUnit_one.neg).pow n)
  rw [← irreducible_isUnit_mul h2, ← charpoly_inv_mul] at h1
  exact (irreducible_mul_isUnit (isUnit_C.2 hd)).1 h1

private theorem aeval_charpoly_inv {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K] {y : Gn g n} {z : Kˣ}
    (h : aeval (z : K) (y : Mt g n).charpoly = 0) :
    aeval (((z⁻¹ : Kˣ)) : K) ((y⁻¹ : Gn g n) : Mt g n).charpoly = 0 := by
  have hd : IsUnit (y : Mt g n).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have e := congrArg (aeval (((z⁻¹ : Kˣ)) : K)) (charpoly_inv_mul y)
  letI : Invertible (z : K) := invertibleOfNonzero z.ne_zero
  have r : aeval (((z⁻¹ : Kˣ)) : K) (y : Mt g n).charpoly.reverse = 0 := by
    rw [aeval_def, Units.val_inv_eq_inv_val, ← invOf_eq_inv, eval₂_reverse_eq_zero_iff, ← aeval_def, h]
  rw [map_mul, map_mul, r, mul_zero, aeval_C, mul_eq_zero] at e
  refine e.resolve_right ?_
  exact (_root_.map_ne_zero _).2 hd.ne_zero

private theorem rad_iff {a b n : ℕ} (hn : a + b = n) (M : Mt g n) :
    (InPar a M ∧ tl a M = ((1 : Gn g a) : Mt g a) ∧ br a b M = ((1 : Gn g b) : Mt g b)) ↔
      ∀ i j : Fin n, M i j ≠ (1 : Mt g n) i j → (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ i j hne
    by_contra hc
    apply hne
    by_cases hi : (i : ℕ) < a
    · have hj : (j : ℕ) < a := by
        by_contra hj
        exact hc ⟨hi, not_lt.1 hj⟩
      have := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
      simpa [tl, entN, Matrix.one_apply, Fin.ext_iff] using this
    · by_cases hj : (j : ℕ) < a
      · rw [h1 i j hj (not_lt.1 hi), Matrix.one_apply_ne]
        intro e
        rw [e] at hi
        exact hi hj
      · have hi' : (i : ℕ) - a < b := by omega
        have hj' : (j : ℕ) - a < b := by omega
        have := congrFun (congrFun h3 ⟨i - a, hi'⟩) ⟨j - a, hj'⟩
        have e1 : a + ((i : ℕ) - a) = i := by omega
        have e2 : a + ((j : ℕ) - a) = j := by omega
        simp only [br, entN, e1, e2, i.2, j.2, and_self, dif_pos, Units.val_one] at this
        rw [this, Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.ext_iff]
        congr 1
        apply propext
        omega
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · by_contra hc
      have hne : M i j ≠ (1 : Mt g n) i j := by
        rw [Matrix.one_apply_ne]
        · exact hc
        · intro e
          rw [e] at hi
          omega
      have := h i j hne
      omega
    · ext i j
      have hi : (i : ℕ) < n := by omega
      have hj : (j : ℕ) < n := by omega
      have hh : M ⟨i, hi⟩ ⟨j, hj⟩ = (1 : Mt g n) ⟨i, hi⟩ ⟨j, hj⟩ := by
        by_contra hc
        have := h _ _ hc
        simp only at this
        omega
      simp only [tl, entN, hi, hj, and_self, dif_pos, Units.val_one, hh, Matrix.one_apply, Fin.ext_iff]
    · ext i j
      have hi : a + (i : ℕ) < n := by omega
      have hj : a + (j : ℕ) < n := by omega
      have hh : M ⟨a + i, hi⟩ ⟨a + j, hj⟩ = (1 : Mt g n) ⟨a + i, hi⟩ ⟨a + j, hj⟩ := by
        by_contra hc
        have := h _ _ hc
        simp only at this
        omega
      simp only [br, entN, hi, hj, and_self, dif_pos, Units.val_one, hh, Matrix.one_apply, Fin.ext_iff]
      simp

private theorem rad_inv {a b n : ℕ} (hn : a + b = n) {x : Gn g n}
    (hx : InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
      br a b (x : Mt g n) = ((1 : Gn g b) : Mt g b)) :
    InPar a ((x⁻¹ : Gn g n) : Mt g n) ∧ tl a ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
      br a b ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g b) : Mt g b) := by
  have h := (rad_iff hn _).1 hx
  set Y : Mt g n := (x : Mt g n) - 1 with hY
  have hYi : ∀ i j, Y i j ≠ 0 → (i : ℕ) < a ∧ a ≤ (j : ℕ) := fun i j hne =>
    h i j fun e => hne (by simp [hY, e])
  have hsq : Y * Y = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_contra hc
    have h1 := hYi i k (left_ne_zero_of_mul hc)
    have h2 := hYi k j (right_ne_zero_of_mul hc)
    omega
  have hinv : ((x⁻¹ : Gn g n) : Mt g n) = 1 - Y := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    have : (x : Mt g n) = 1 + Y := by simp [hY]
    rw [this]
    noncomm_ring
    rw [hsq]
    simp
  rw [rad_iff hn, hinv]
  intro i j hne
  refine hYi i j fun e => hne ?_
  simp [e]

private theorem isCusp_dual {n : ℕ} {τ : FDRep ℂ (Gn g n)} (h : IsCusp τ.character) :
    IsCusp (FDRep.of (Representation.dual τ.ρ)).character := by
  refine ⟨h.1, ?_, fun a ha ha' => ?_⟩
  · obtain ⟨V, hV, hc⟩ := h.2.1
    refine ⟨FDRep.of (Representation.dual V.ρ), ?_, fun x => ?_⟩
    · rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
      rw [← hV]
      simp only [FDRep.char_dual, inv_inv]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · rw [FDRep.char_dual, FDRep.char_dual, hc]
  · have h3 := h.2.2 a ha ha'
    have hn : a + (n - a) = n := by omega
    rw [res] at h3 ⊢
    have hP : ∀ x : Gn g n, (InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
        br a (n - a) (x : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))) ↔
        (InPar a ((x⁻¹ : Gn g n) : Mt g n) ∧ tl a ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
        br a (n - a) ((x⁻¹ : Gn g n) : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))) := fun x =>
      ⟨rad_inv hn, fun e => by simpa using rad_inv hn e⟩
    rw [← Equiv.sum_comp (Equiv.inv (Gn g n))]
    refine Eq.trans (congrArg _ (Finset.sum_congr rfl fun x _ => ?_)) h3
    simp only [FDRep.char_dual, Equiv.inv_apply, inv_inv]
    split_ifs with c1 c2 c2
    · rfl
    · exact absurd ((hP x).2 c1) c2
    · exact absurd ((hP x).1 c2) c1
    · rfl

private theorem names_dual {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K] {θ : Kˣ →* ℂˣ} {τ : FDRep ℂ (Gn g n)}
    (h : Names g n θ τ) : Names g n θ⁻¹ (FDRep.of (Representation.dual τ.ρ)) := by
  intro y hy z hz
  rw [FDRep.char_dual, h y⁻¹ (irreducible_charpoly_inv hy) z⁻¹ (aeval_charpoly_inv hz)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [inv_pow]

private theorem isRegularChar_inv {n : ℕ} {K : Type} [Field K] {θ : Kˣ →* ℂˣ} (h : GlobalTheory.Published.IsRegularChar g n θ) :
    GlobalTheory.Published.IsRegularChar g n θ⁻¹ := fun i j hi hj e =>
  h i j hi hj (inv_injective (by simpa [inv_pow] using e))

end Finite

end UpperTheory.Zero.LLC.ParameterDuality

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC.ParameterDuality

private theorem inflates_dual {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {n : ℕ} (π σ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (e : σ.ρ.Equiv (contra π.ρ)) (τ : FDRep ℂ (Gn g n))
    (hinf : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    GlobalTheory.SerSys.TameGen.Inflates (π.ρ.comp (GeneralLinearGroup.map i.toRingHom))
      (FDRep.of (Representation.dual τ.ρ)) := by
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  let ι : GL (Fin n) ℤ_[g] →* GL (Fin n) (w.adicCompletion E) :=
    (GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g n)
  let e' := e.toIntertwiningMap
  let B : τ →ₗ[ℂ] Module.Dual ℂ π.V :=
    (smoothPart (Representation.dual π.ρ)).subtype ∘ₗ e'.toLinearMap ∘ₗ φ
  have hB : B ≠ 0 := fun h0 => hφ0 (LinearMap.ext fun w' => by
    have h1 : B w' = 0 := by rw [h0]; rfl
    have h2 : e.toLinearEquiv (φ w') = 0 := Subtype.ext h1
    simpa using h2)
  have hq : Function.Surjective (GlobalTheory.GLp.red g n) := fun x => by
    obtain ⟨m, rfl⟩ := DiscreteGroups.sglob.DzIso.redKO_surjective i hi n x
    obtain ⟨k, rfl⟩ := DiscreteGroups.sglob.DzIso.toKO_surjective i hi n m
    exact ⟨k, (DiscreteGroups.sglob.DzIso.redKO_toKO i hi n k).symm⟩
  have hker := DiscreteGroups.sglob.DzIso.ker_redKO i hi n
  have h1 : ∀ k, GlobalTheory.GLp.red g n k = 1 → ι k ∈ KOne (w.adicCompletion E) (Fin n) := fun k hk => by
    have : DiscreteGroups.sglob.DzIso.toKO i hi n k ∈ (DiscreteGroups.sglob.DzIso.redKO i hi n).ker := by
      rw [MonoidHom.mem_ker, DiscreteGroups.sglob.DzIso.redKO_toKO, hk]
    rw [hker, Subgroup.mem_subgroupOf, DiscreteGroups.sglob.DzIso.coe_toKO] at this
    exact this
  have h2 : ∀ x ∈ KOne (w.adicCompletion E) (Fin n), ∃ k, ι k = x ∧ GlobalTheory.GLp.red g n k = 1 := fun x hx => by
    have hxK : x ∈ KO (w.adicCompletion E) (Fin n) := by
      obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact ⟨b, rfl⟩
    obtain ⟨k, hk⟩ := DiscreteGroups.sglob.DzIso.toKO_surjective i hi n ⟨x, hxK⟩
    refine ⟨k, ?_, ?_⟩
    · show GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k) = x
      rw [← DiscreteGroups.sglob.DzIso.coe_toKO i hi, hk]
    · rw [← DiscreteGroups.sglob.DzIso.redKO_toKO i hi, hk, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact hx
  have hinv : ∀ k w' v, B (τ.ρ (GlobalTheory.GLp.red g n k) w') (π.ρ (ι k) v) = B w' v := fun k w' v => by
    have e1 : e' (φ (τ.ρ (GlobalTheory.GLp.red g n k) w')) = contra π.ρ (ι k) (e' (φ w')) := by
      rw [hφ k w']
      exact Representation.IntertwiningMap.isIntertwining _ _ e' (ι k) (φ w')
    show ((e' (φ (τ.ρ (GlobalTheory.GLp.red g n k) w')) : smoothPart _) : Module.Dual ℂ π.V) (π.ρ (ι k) v) =
      ((e' (φ w') : smoothPart _) : Module.Dual ℂ π.V) v
    rw [e1, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  obtain ⟨ψ, hψ0, hψ⟩ := exists_dual_map π.ρ π.smooth τ.ρ ι (GlobalTheory.GLp.red g n) hq
    (KOne (w.adicCompletion E) (Fin n)) GlobalTheory.DepthZeroJac.isCompact_KOne h1 h2 B hB hinv
  exact ⟨ψ, hψ0, hψ⟩

end UpperTheory.Zero.LLC.ParameterDuality

theorem UpperTheory.Zero.LLC.parDual :
    UpperTheory.Zero.LLC.ParDual := by
  intro E Ω _ _ _ _ _ A w h a ha _ _ i₀ _ y y' _ _ hD V hV
  obtain ⟨-, -, -, hIrr, hTame, hDim, hDet, hPol, -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h V
  obtain ⟨hIrrD, -⟩ : IsIrrWD V.lpDual ∧ True := ⟨(hIrr hV.irr).2.2, trivial⟩
  obtain ⟨-, -, -, hIrr', -⟩ := UpperTheory.Zero.LLC.wDBasic E Ω A w h V.lpDual
  have hC : CharZero (w.adicCompletion E) := charZero_of_injective_ringHom (f := i₀.toRingHom) i₀.injective
  obtain ⟨⟨ω₀, -, hω₀, -⟩, -, -, -, -, -, hdual⟩ := UpperTheory.Zero.LLC.clBasic (w.adicCompletion E) y
  obtain ⟨hy1, -, -, -, -, -, hcen⟩ := hdual y' hD
  obtain ⟨⟨ω₁, -, -, huniq⟩, -⟩ := UpperTheory.Zero.LLC.clBasic (w.adicCompletion E) y'
  refine ⟨hIrrD, ?_, hTame hV.tame, ?_, ?_⟩
  · rw [hDim, hV.dim, hy1]
  · intro ω hω σ
    have e : ω = ω₀⁻¹ := (huniq ω hω).trans (huniq _ (hcen ω₀ hω₀)).symm
    rw [hDet, hV.central ω₀ hω₀ σ, e]
    simp
  · intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
    obtain ⟨m, π, π', rfl, rfl, ⟨e⟩⟩ := hD
    obtain rfl : n = m := congrArg Sigma.fst hσ
    obtain ⟨e₁⟩ := IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) (w.adicCompletion E))) hσ)
    have hI := ParameterDuality.inflates_dual i hi π σ (e₁.trans e) τ hinf
    obtain ⟨-, hIn⟩ := hV.type g i hi n hn D R hR θ⁻¹ (ParameterDuality.isRegularChar_inv hθ) _
      (ParameterDuality.isCusp_dual hτ) (ParameterDuality.names_dual hN) π rfl hI
    refine ⟨(hIrr' hIrrD).1, fun t => ?_⟩
    have h3 := (hPol t ((Finset.range n).val.map fun j => (θ⁻¹ (R t ^ g ^ j))) (by
      rw [hIn t]
      change _ = (Multiset.map (fun z : ℂ => X - C z) (Multiset.bind _ fun a : ℂˣ => {(a : ℂ)})).prod
      rw [Multiset.bind_singleton, Multiset.map_map, Multiset.map_map]
      rfl)).2.1
    rw [h3, Multiset.map_map]
    simp [Finset.prod]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.JunkEx
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem exists_frobAut (K : Type) [Field K] [Finite K] (q n : ℕ) (hq : 1 < q) (hn : 0 < n)
    (hcard : Nat.card K = q ^ n) : ∃ f : RingAut K, (∀ x, f x = x ^ q) ∧ orderOf f = n := by
  classical
  letI := Fintype.ofFinite K
  obtain ⟨p, hpc⟩ := CharP.exists K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : ExpChar K p := ExpChar.prime hp
  have hc : Fintype.card K = q ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hd : q ∣ p ^ (k : ℕ) := by
    rw [← hk, hc]; exact dvd_pow_self q hn.ne'
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
  let f0 : K →+* K := iterateFrobenius K p j
  have hinj : Function.Injective f0 := f0.injective
  let f : RingAut K := RingEquiv.ofBijective f0 (Finite.injective_iff_bijective.1 hinj)
  have hf : ∀ x, f x = x ^ p ^ j := fun x => iterateFrobenius_def p j x
  have hpow : ∀ (m : ℕ) (x : K), (f ^ m) x = x ^ (p ^ j) ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', RingAut.mul_apply, ih, hf, ← pow_mul, ← pow_succ]
  refine ⟨f, hf, (orderOf_eq_iff hn).2 ⟨?_, fun m hmn hm0 hone => ?_⟩⟩
  · ext x
    rw [hpow, ← hc, FiniteField.pow_card]
    rfl
  · obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hob : orderOf b = (p ^ j) ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hb, Nat.card_eq_fintype_card, Fintype.card_units, hc]
    have hq1 : 1 ≤ (p ^ j) ^ m := Nat.one_le_pow _ _ (by omega)
    have h1 : (b : K) ^ (p ^ j) ^ m = b := by
      rw [← hpow, hone]; rfl
    have h2 : b ^ ((p ^ j) ^ m - 1) = 1 := by
      have h3 : b ^ (p ^ j) ^ m = b := Units.ext (by simpa using h1)
      have h4 : b ^ ((p ^ j) ^ m - 1) * b = 1 * b := by
        rw [← pow_succ, Nat.sub_add_cancel hq1, one_mul, h3]
      exact mul_right_cancel h4
    have hdv := orderOf_dvd_of_pow_eq_one h2
    rw [hob] at hdv
    have hlt : (p ^ j) ^ m < (p ^ j) ^ n := Nat.pow_lt_pow_right hq hmn
    have h2m : 2 ≤ (p ^ j) ^ m := le_trans hq (Nat.le_self_pow hm0.ne' _)
    have := Nat.le_of_dvd (by omega) hdv
    omega

private theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

private theorem exp_neg_one_le {γ : WithZero (Multiplicative ℤ)} (h : ¬ γ ≤ WithZero.exp (-2 : ℤ)) :
    WithZero.exp (-1 : ℤ) ≤ γ := by
  have h0 : γ ≠ 0 := by rintro rfl; exact h zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [WithZero.exp_le_exp] at h ⊢
  omega

private theorem le_val_of_not_mem_sq {L : Type} [Field L] [NumberField L] (u : HeightOneSpectrum (𝓞 L)) (c : 𝓞 L)
    (hc1 : c ∈ u.asIdeal) (hc2 : c ∉ u.asIdeal ^ 2) (x : u.adicCompletion L) (hx : Valued.v x < 1) :
    Valued.v x ≤ Valued.v (algebraMap L (u.adicCompletion L) (c : L)) := by
  have e : (Valued.v (algebraMap L (u.adicCompletion L) (c : L)) : WithZero (Multiplicative ℤ)) = u.intValuation c :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) u (c : L)).trans
      (HeightOneSpectrum.valuation_of_algebraMap u c)
  rw [e]
  refine (le_exp_neg_one hx).trans (exp_neg_one_le fun h2 => hc2 ?_)
  exact_mod_cast (u.intValuation_le_pow_iff_mem c 2).1 (by simpa using h2)

private theorem junkData (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : RingAut K) (π : Ine (F := E) A →* Multiplicative K),
      Nat.card K = normV w ^ n ∧ orderOf f = n ∧ Function.Surjective π ∧ IsOpen (π.ker : Set (Ine (F := E) A)) ∧
      ∀ t t' : Ine (F := E) A, ineIncl h t' = frob h * ineIncl h t * (frob h)⁻¹ →
        π t' = Multiplicative.ofAdd (f (Multiplicative.toAdd (π t))) := by
  classical
  obtain ⟨c, hcw, hc2⟩ : ∃ c : 𝓞 E, c ∈ w.asIdeal ∧ c ∉ w.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl)
  have hφ : IsFrob A (normV w) (frob h : G E Ω) := isFrob_frob
  obtain ⟨L, _, _, _, _, _, _, u, hu, s, hs, hfix, hcu, hN⟩ := UpperTheory.exists_numberField_extension_place_frobenius_degree E Ω A w h n hn _ hφ c hc2
  obtain ⟨a, ha, -⟩ := UpperTheory.Zero.LLC.artEx L Ω A u hu
  have hsu : ∀ x : 𝓞 L, RingOfIntegers.mapRingHom (s.toRingEquiv : L →+* L) x ∈ u.asIdeal ↔ x ∈ u.asIdeal := by
    intro x
    rw [← hu, ← hu x]
    have e : algebraMap L Ω ((RingOfIntegers.mapRingHom (s.toRingEquiv : L →+* L) x : 𝓞 L) : L) =
        (frob h : G E Ω) (algebraMap L Ω (x : L)) := (hs _).symm
    rw [e]
    exact valuation_apply_lt_one_iff hφ.1 _
  obtain ⟨i, hic, hil, hiv⟩ := UpperTheory.exists_adicCompletion_ringEquiv_extending_of_stable u s.toRingEquiv hsu

  have hcL1 : algebraMap (𝓞 E) (𝓞 L) c ∈ u.asIdeal := by
    rw [← hu]
    have e : algebraMap L Ω ((algebraMap (𝓞 E) (𝓞 L) c : 𝓞 L) : L) = algebraMap E Ω (c : E) :=
      (IsScalarTower.algebraMap_apply E L Ω (c : E)).symm
    rw [e]
    exact (h c).2 hcw
  set cL : 𝓞 L := algebraMap (𝓞 E) (𝓞 L) c with hcL
  set ϖ : u.adicCompletion L := algebraMap L (u.adicCompletion L) (cL : L) with hϖdef
  have hcL0 : cL ≠ 0 := fun h0 => hcu (by rw [h0]; exact zero_mem _)
  have hϖ0 : ϖ ≠ 0 := by
    rw [hϖdef, Ne, map_eq_zero]
    exact_mod_cast hcL0
  have hϖ1 : Valued.v ϖ < 1 := DiscreteGroups.sglob.DzType.val_alg_lt_one_of_mem cL hcL1
  have hϖ : ∀ x : u.adicCompletion L, Valued.v x < 1 → Valued.v x ≤ Valued.v ϖ :=
    le_val_of_not_mem_sq u cL hcL1 hcu
  let O : ValuationSubring (u.adicCompletion L) := (Valued.v : Valuation (u.adicCompletion L) _).valuationSubring
  let K : Type := IsLocalRing.ResidueField O
  let ρ : O →+* K := IsLocalRing.residue O
  have hcard : Nat.card K = normV w ^ n := (UpperTheory.card_residueField_adicCompletionIntegers_eq_absNorm u).trans hN
  have hq1 : 1 < normV w := ReciprocityTheory.Gal.one_lt_normV w
  have hQ : 4 ≤ normV w ^ n := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ normV w ^ 2 := Nat.pow_le_pow_left hq1 2
      _ ≤ normV w ^ n := Nat.pow_le_pow_right (by omega) hn
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  letI := Fintype.ofFinite K
  have hcardF : Fintype.card K = normV w ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hρ0 : ∀ x : O, ρ x = 0 ↔ Valued.v (x : u.adicCompletion L) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one.symm
  have hNz : ∀ z : K, z ≠ 0 → z ^ (normV w ^ n - 1) = 1 := fun z hz => by
    rw [← hcardF]; exact FiniteField.pow_card_sub_one_eq_one z hz
  have hNK : (((normV w ^ n - 1 : ℕ)) : K) = -1 := by
    have h0 : ((normV w ^ n : ℕ) : K) = 0 := by rw [← hcardF]; exact Nat.cast_card_eq_zero K
    rw [Nat.cast_sub (by omega), h0, Nat.cast_one, zero_sub]
  obtain ⟨abelian₂, hadd, hLs, hL0, hLi⟩ := UpperTheory.exists_unit_residue_logarithm_of_roots_of_unity (K := K) Valued.v ϖ hϖ0 hϖ1 hϖ ρ
    IsLocalRing.residue_surjective hρ0 (normV w ^ n - 1) (by omega) hNz hNK
  obtain ⟨f, hfx, hfo⟩ := exists_frobAut K (normV w) n hq1 (by omega) hcard

  have hρeq : ∀ x y : O, Valued.v ((x : u.adicCompletion L) - y) < 1 → ρ x = ρ y := by
    intro x y hxy
    rw [← sub_eq_zero, ← map_sub]
    exact (hρ0 _).2 (by simpa using hxy)
  have hρi : ∀ x y : O, (y : u.adicCompletion L) = i x →
      ρ y = f (ρ x) := by
    intro x y hyx
    obtain ⟨z, hz⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl u (x : u.adicCompletion L) x.2
    let Z : O := ⟨algebraMap L (u.adicCompletion L) (z : L), DiscreteGroups.sglob.DzType.val_le_one_int u z⟩
    have h1 : ρ x = ρ Z := hρeq _ _ hz
    have h2 : f (ρ x) = ρ (Z ^ normV w) := by
      rw [h1, map_pow]
      exact hfx _
    rw [h2]
    apply hρeq
    let z' : 𝓞 L := RingOfIntegers.mapRingHom (s.toRingEquiv : L →+* L) z - z ^ normV w
    have hz' : z' ∈ u.asIdeal := by
      rw [← hu]
      have e : algebraMap L Ω (z' : L) = (frob h : G E Ω) (algebraMap L Ω (z : L)) - (algebraMap L Ω (z : L)) ^ normV w := by
        rw [hs]
        simp [z']
      rw [e]
      exact hφ.2 _ (GlobalTheory.UnrCycExt.val_le_one_of_int A z)
    have e : (y : u.adicCompletion L) - ((Z ^ normV w : O) : u.adicCompletion L) =
        i ((x : u.adicCompletion L) - algebraMap L _ (z : L)) + algebraMap L _ (z' : L) := by
      rw [hyx, map_sub, hil]
      simp [z', Z]
    rw [e]
    refine Valuation.map_add_lt _ ?_ (DiscreteGroups.sglob.DzType.val_alg_lt_one_of_mem z' hz')
    rw [hiv]
    exact hz

  have hfixA : ∀ t : Ine (F := E) A, ∀ x : L, (t : G E Ω) (algebraMap L Ω x) = algebraMap L Ω x := fun t => hfix t t.2
  let ι₀ : Ine (F := E) A → G L Ω := fun t => { (t : G E Ω).toRingEquiv with commutes' := hfixA t }
  have hι₀ : ∀ (t : Ine (F := E) A) (x : Ω), ι₀ t x = (t : G E Ω) x := fun _ _ => rfl
  have hι₀m : ∀ t, ι₀ t ∈ Ine (F := L) A := fun t =>
    ⟨GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec t.2.1 x, fun x hx => t.2.2 x hx⟩
  let ι : Ine (F := E) A →* Ine (F := L) A := MonoidHom.mk' (fun t => ⟨ι₀ t, hι₀m t⟩) fun t t' => by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    rfl
  have hι : ∀ (t : Ine (F := E) A) (x : Ω), (ι t : G L Ω) x = (t : G E Ω) x := fun _ _ => rfl
  have hιs : ∀ t₁ : Ine (F := L) A, ∃ t : Ine (F := E) A, ι t = t₁ := by
    intro t₁
    have hd : AlgEquiv.restrictScalars E (t₁ : G L Ω) ∈ Ine (F := E) A :=
      ⟨GlobalTheory.FunExt.ConjLift.mem_Dec_of_iff fun x => apply_mem_iff_of_mem_Dec t₁.2.1 x, fun x hx => t₁.2.2 x hx⟩
    exact ⟨⟨_, hd⟩, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩
  have hval : ∀ t : Ine (F := E) A, Valued.v ((a (ineIncl hu (ι t)) : (u.adicCompletion L)ˣ) : u.adicCompletion L) = 1 :=
    fun t => DiscreteGroups.sglob.DzType.val_artin_ine ha (ι t)
  let π : Ine (F := E) A →* Multiplicative K :=
    MonoidHom.mk' (fun t => Multiplicative.ofAdd (abelian₂ (a (ineIncl hu (ι t))))) fun t t' => by
      rw [map_mul, map_mul, map_mul, hadd _ _ (hval t) (hval t')]
      rfl
  have hπ : ∀ t, Multiplicative.toAdd (π t) = abelian₂ (a (ineIncl hu (ι t))) := fun _ => rfl
  refine ⟨K, inferInstance, inferInstance, f, π, hcard, hfo, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb1, hby⟩ := hLs (Multiplicative.toAdd y)
    obtain ⟨t₁, ht₁⟩ := DiscreteGroups.sglob.DzType.exists_ine_of_v_eq_one ha b hb1
    obtain ⟨t, rfl⟩ := hιs t₁
    refine ⟨t, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hπ, ht₁, hby]
  · have hcont : Continuous fun t : Ine (F := E) A => a (ineIncl hu (ι t)) :=
      ha.cont.comp (UpperTheory.continuous_inertia_restriction_of_compat A ι hι)
    have hball : IsOpen {b : (u.adicCompletion L)ˣ | ((b : u.adicCompletion L) - 1) * (ϖ ^ 2)⁻¹ ∈ (O : Set (u.adicCompletion L))} :=
      (Valued.isOpen_valuationSubring _).preimage
        (((Units.continuous_val).sub continuous_const).mul continuous_const)
    have hU := hball.preimage hcont
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) ?_)
    · simp [O]
    · intro t ht
      apply Multiplicative.toAdd.injective
      refine hL0 _ ?_
      have hv0 : Valued.v ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
      have h1 : Valued.v ((((a (ineIncl hu (ι t)) : (u.adicCompletion L)ˣ) : u.adicCompletion L) - 1) * (ϖ ^ 2)⁻¹) ≤ 1 :=
        (Valuation.mem_valuationSubring_iff _ _).1 ht
      rw [map_mul, map_inv₀, map_pow, mul_inv_le_iff₀ (pow_pos (zero_lt_iff.2 hv0) 2), one_mul] at h1
      refine lt_of_le_of_lt h1 ?_
      rw [pow_two]
      exact mul_lt_of_lt_one_left (zero_lt_iff.2 hv0) hϖ1
  · intro t t' htt
    have hW : WeilRel (frob h : G E Ω).toRingEquiv (ineIncl hu (ι t)) (ineIncl hu (ι t')) := by
      intro z
      have e : (t' : G E Ω) = (frob h : G E Ω) * t * (frob h : G E Ω)⁻¹ := congrArg Subtype.val htt
      show (frob h : G E Ω) ((t : G E Ω) z) = (t' : G E Ω) ((frob h : G E Ω) z)
      rw [e]
      simp [AlgEquiv.mul_apply]
    have hP : PlaceIso A u A u (frob h : G E Ω).toRingEquiv (s.toRingEquiv : L →+* L) i :=
      ⟨fun z => apply_mem_iff_of_mem_Dec hφ.1 z, hs, hic, hil⟩
    have e := isLocalArtin_transport GlobalTheory.globalArtinReciprocity_holds GlobalTheory.Published.chevalleyUnits' L Ω A u hu L Ω A u hu
      _ _ i hP a a ha ha _ _ hW
    have hiϖ : i ϖ = ϖ := by
      rw [hϖdef, hil]
      congr 1
      exact s.commutes (c : E)
    apply Multiplicative.toAdd.injective
    rw [hπ, e, toAdd_ofAdd, hπ]
    exact hLi i f hiϖ hiv hρi _ (hval t)

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.junkEx :
    UpperTheory.Zero.LLC.JunkEx := by
  intro E Ω _ _ _ _ _ A w h n hn
  obtain ⟨K, _, _, f, π, hc, ho, hs, hop, he⟩ := UpperTheory.Zero.LLC.junkData E Ω A w h n hn
  obtain ⟨J, h1, h2, h3, h4⟩ := UpperTheory.tameInertiaCharacter_frobenius_conj_eq_pow h n hn K f π hc ho hs hop he
  exact ⟨J, h1, h2, h3, fun _ V ξ hξ hV => h4 V ξ hξ hV⟩

end
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section SlopeTestRemainingChoices

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E _).injective

private theorem twist_congr (V : WD h) {ξ ξ' : Weil h →* ℂˣ} (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ)
    (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ') (e : ξ = ξ') : V.lpTwist ξ hξ = V.lpTwist ξ' hξ' := by
  subst e; rfl

private theorem tw_congr (y : IrrGL (k := w.adicCompletion E)) {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (hχ' : IsSmoothChar χ') (e : χ = χ') : y.tw χ hχ = y.tw χ' hχ' := by
  subst e; rfl

private theorem good_cases {x : IrrGL (k := w.adicCompletion E)} (hc : x.IsCusp) (hg : GoodCusp x) :
    x.1 = 1 ∨ ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) ∧
      ∃ (y : IrrGL (k := w.adicCompletion E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ),
        y.IsCusp ∧ DZ y ∧ x = y.tw χ hχ) := by
  haveI := charZero_compl (E := E) w
  rcases hg with h1 | ⟨hq, y, χ, hχ, hd, rfl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hq, y, χ, hχ, ((clBasic _ y).2.1 χ hχ).2.1.1 hc, hd, rfl⟩

private theorem goodCusp_self {y : IrrGL (k := w.adicCompletion E)}
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) (hd : DZ y) : GoodCusp y :=
  Or.inr ⟨hq, y, 1, isSmoothChar_one, hd, (IrrGL.tw_one y _).symm⟩

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}

private theorem lpTw_eq (ha : IsLocalArtin h a) (V : WD h) (s : ℝ) :
    V.lpTw s = V.lpTwist ((absPow (w.adicCompletion E) s).comp a) (ha.smooth (isSmoothChar_absPow _)) :=
  twist_congr V _ _ (ha.absPow_comp s).symm

private theorem twist_twist (ha : IsLocalArtin h a) (V : WD h) {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (hχ' : IsSmoothChar χ') (hm : IsSmoothChar (χ * χ')) :
    (V.lpTwist (χ.comp a) (ha.smooth hχ)).lpTwist (χ'.comp a) (ha.smooth hχ') =
      V.lpTwist ((χ * χ').comp a) (ha.smooth hm) := by
  obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h V
  have e : (χ * χ').comp a = χ.comp a * χ'.comp a := MonoidHom.ext fun _ => rfl
  have hs : GlobalTheory.WeilDeligne.IsSmooth (χ.comp a * χ'.comp a) := e ▸ ha.smooth hm
  rw [(c9 _ (ha.smooth hχ)).2.2.2.1 _ (ha.smooth hχ') hs]
  exact twist_congr V _ _ e.symm

private theorem twist_one (ha : IsLocalArtin h a) (V : WD h) (h1 : IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ)) :
    V.lpTwist ((1 : (w.adicCompletion E)ˣ →* ℂˣ).comp a) (ha.smooth h1) = V := by
  obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h V
  exact (c9 _ (ha.smooth h1)).2.2.2.2.1 (MonoidHom.one_comp a)

private structure Gm (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (r : IrrGL (k := w.adicCompletion E) → WD h) : Prop where
  one : ∀ χ hχ, r (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
  tw : ∀ x, x.IsCusp → GoodCusp x → ∀ χ hχ, r (x.tw χ hχ) = (r x).lpTwist (χ.comp a) (ha.smooth hχ)
  par : (∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i) →
    ∀ y, y.IsCusp → DZ y → Par a y (r y)

variable {r : IrrGL (k := w.adicCompletion E) → WD h}

private theorem Gm.basic (H : Gm a ha r) {x : IrrGL (k := w.adicCompletion E)} (hc : x.IsCusp) (hg : GoodCusp x) :
    IsIrrWD (r x) ∧ (r x).lpDim = x.1 ∧
      ∀ ω, HasCentralChar x.rep ω → ∀ σ, ((r x).eig σ).prod = (ω (a σ) : ℂ) := by
  haveI := charZero_compl (E := E) w
  rcases good_cases hc hg with h1 | ⟨hq, y, χ, hχ, hy, hd, rfl⟩
  · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 h1).2
    obtain ⟨p1, p2, p3, p4, -⟩ := parOne E Ω A w h a ha χ hχ
    rw [H.one]
    refine ⟨p1, p2, fun ω hω σ => ?_⟩
    obtain ⟨ω₀, -, -, hu⟩ := (clBasic _ (IrrGL.ofChar χ hχ)).1
    rw [hu ω hω, ← hu χ p3]
    exact p4 σ
  · have P := H.par hq y hy hd
    obtain ⟨-, -, -, c4, -, -, -, -, c9⟩ := wDBasic E Ω A w h (r y)
    obtain ⟨t1, t2, t3, -⟩ := c9 _ (ha.smooth hχ)
    rw [H.tw y hy (goodCusp_self hq hd)]
    refine ⟨t2 P.irr, t1.trans (P.dim.trans ((clBasic _ y).2.1 χ hχ).1.symm), fun ω hω σ => ?_⟩
    obtain ⟨ω₀, -, h₀, -⟩ := (clBasic _ y).1
    obtain ⟨ω₁, -, -, hu⟩ := (clBasic _ (y.tw χ hχ)).1
    have h₁ := ((clBasic _ y).2.1 χ hχ).2.2.2.2 ω₀ h₀
    rw [hu ω hω, ← hu _ h₁, t3 σ, P.central ω₀ h₀ σ, P.dim]
    simp

private theorem Gm.dual (H : Gm a ha r) {x y : IrrGL (k := w.adicCompletion E)} (hc : x.IsCusp) (hg : GoodCusp x)
    (hd : DualCl x y) : r y = (r x).lpDual := by
  haveI := charZero_compl (E := E) w
  rcases good_cases hc hg with h1 | ⟨hq, u, χ, hχ, hu, hdz, rfl⟩
  · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 h1).2
    have hi := hχ.inv
    obtain ⟨-, -, -, -, -, -, -, p8, -⟩ := parOne E Ω A w h a ha χ hχ
    obtain ⟨d1, d2⟩ := p8 hi
    have := ((clBasic _ (IrrGL.ofChar χ hχ)).2.2.2.2.2.2 _ d1).2.2.2.2.1 y hd
    rw [this, H.one, H.one, d2]
  · obtain ⟨u', hu'⟩ := (clBasic _ u).2.2.2.2.2.1
    obtain ⟨-, f2, f3, -, -, f6, -⟩ := (clBasic _ u).2.2.2.2.2.2 u' hu'
    have hi := hχ.inv
    have ey := ((clBasic _ (u.tw χ hχ)).2.2.2.2.2.2 _ (f6 χ hχ hi)).2.2.2.2.1 y hd
    have hu'c : u'.IsCusp := f2.2 hu
    have hu'd : DZ u' := f3.2 hdz
    have P := H.par hq u hu hdz
    have P' := H.par hq u' hu'c hu'd
    obtain ⟨g, hgp, i, hi'⟩ := hq
    have D := parDual E Ω A w h a ha g i hi' u u' hu hdz hu' (r u) P
    have U := (parUniq E Ω A w h a ha g i hi' u' hu'c hu'd (r u') P').1 _ D
    have hq' : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i := ⟨g, hgp, i, hi'⟩
    rw [ey, H.tw u' hu'c (goodCusp_self hq' hu'd), H.tw u hu (goodCusp_self hq' hdz), ← U]
    obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h (r u)
    have hcomp : χ⁻¹.comp a = (χ.comp a)⁻¹ := MonoidHom.ext fun _ => rfl
    have hs : GlobalTheory.WeilDeligne.IsSmooth (χ.comp a)⁻¹ := hcomp ▸ ha.smooth hi
    rw [(c9 _ (ha.smooth hχ)).2.2.2.2.2.1 hs]
    exact twist_congr _ _ _ hcomp

private theorem Gm.tw_inj (H : Gm a ha r) {u v : IrrGL (k := w.adicCompletion E)}
    (hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i)
    (hu : u.IsCusp) (hud : DZ u) (hv : v.IsCusp) (hvd : DZ v) {χ χ' : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (e : r (u.tw χ hχ) = r (v.tw χ' hχ')) :
    u.tw χ hχ = v.tw χ' hχ' := by
  haveI := charZero_compl (E := E) w
  have Pu := H.par hq u hu hud
  have Pv := H.par hq v hv hvd
  rw [H.tw u hu (goodCusp_self hq hud), H.tw v hv (goodCusp_self hq hvd)] at e
  have hi := hχ.inv
  have hψ : IsSmoothChar (χ' * χ⁻¹) := hχ'.mul hi
  have e2 := congrArg (fun V => V.lpTwist (χ⁻¹.comp a) (ha.smooth hi)) e
  rw [twist_twist ha _ hχ hi (hχ.mul hi), twist_twist ha _ hχ' hi hψ] at e2
  have e3 : r u = (r v).lpTwist ((χ' * χ⁻¹).comp a) (ha.smooth hψ) := by
    rw [← e2, twist_congr (r u) (ha.smooth (hχ.mul hi)) (ha.smooth (isSmoothChar_one))
      (by rw [mul_inv_cancel]), twist_one ha _ isSmoothChar_one]
  have hpos : 0 < (r v).lpDim := by rw [Pv.dim]; exact hv.1
  obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h (r v)
  have wild := (c9 _ (ha.smooth hψ)).2.2.2.2.2.2.2 hpos Pv.tame (e3 ▸ Pu.tame)
  have tc : TameChar (χ' * χ⁻¹) := (tameArt E Ω A w h a ha _ hψ).2 wild
  obtain ⟨g, hgp, i, hi'⟩ := hq
  have T := parTw E Ω A w h a ha g i hi' v hv hvd (r v) Pv _ hψ tc
  rw [← e3] at T
  have hc' : (v.tw _ hψ).IsCusp := ((clBasic _ v).2.1 _ hψ).2.1.2 hv
  have hd' : DZ (v.tw _ hψ) := (twTame _ v _ hψ hv.1 hvd).2 tc
  have U := (parUniq E Ω A w h a ha g i hi' u hu hud (r u) Pu).2 _ hc' hd' T
  subst U
  rw [((clBasic _ v).2.1 _ hψ).2.2.2.1 χ hχ (hψ.mul hχ)]
  exact tw_congr v _ _ (by rw [inv_mul_cancel_right])

end SlopeTestRemainingChoices

theorem cuspEx : CuspEx := by
  intro E Ω _ _ _ _ _ A w h a ha
  haveI := charZero_compl (E := E) w
  classical
  obtain ⟨r₀, H1, H2, H3⟩ := goodMap E Ω A w h a ha
  have H : Gm a ha r₀ := ⟨H1, H2, H3⟩
  obtain ⟨e, he⟩ := expo E Ω A w h a ha
  haveI : Nonempty (WD h) := ⟨WD.lpZero (h := h)⟩
  choose! J hJ using junkEx E Ω A w h
  let r : IrrGL (k := w.adicCompletion E) → WD h := fun x => if GoodCusp x then r₀ x else (J x.1).lpTw (e x)
  have rg : ∀ x, GoodCusp x → r x = r₀ x := fun x hx => if_pos hx
  have rb : ∀ x, ¬ GoodCusp x → r x = (J x.1).lpTw (e x) := fun x hx => if_neg hx
  have two : ∀ x : IrrGL (k := w.adicCompletion E), x.IsCusp → ¬ GoodCusp x → 2 ≤ x.1 := by
    intro x hx hb
    have h0 := hx.1
    have h1 : x.1 ≠ 1 := fun h1 => hb (Or.inl h1)
    omega
  have hirr : ∀ x, x.IsCusp → IsIrrWD (r x) ∧ (r x).lpDim = x.1 := by
    intro x hx
    by_cases hg : GoodCusp x
    · rw [rg x hg]
      exact ⟨(H.basic hx hg).1, (H.basic hx hg).2.1⟩
    · rw [rb x hg]
      obtain ⟨j1, j2, -, -⟩ := hJ _ (two x hx hg)
      obtain ⟨-, -, -, -, -, -, -, -, c9⟩ := wDBasic E Ω A w h (J x.1)
      exact ⟨(c9 _ _).2.1 j1, ((c9 _ _).1).trans j2⟩
  have hcen : ∀ x : IrrGL (k := w.adicCompletion E), x.IsCusp → GoodCusp x → ∀ ω, HasCentralChar x.rep ω →
      ∀ σ, ((r x).eig σ).prod = (ω (a σ) : ℂ) := by
    intro x hx hg
    rw [rg x hg]
    exact (H.basic hx hg).2.2
  refine ⟨r, ⟨fun x hx => (hirr x hx).1, fun x hx => (hirr x hx).2, fun χ hχ => ?_, fun x hx s => ?_,
    fun x hx ω hω σ => ?_, fun x hx hg χ hχ => ?_, hcen, fun x y hx _ hg hd => ?_, fun x y hx hy hgy eq => ?_,
    fun x hx hg hd => ?_, fun x hx => ?_⟩⟩
  · rw [rg _ (Or.inl rfl)]
    exact H1 χ hχ
  · have hiff := ((clBasic _ x).2.1 _ (isSmoothChar_absPow (s : ℂ))).2.2.1
    by_cases hg : GoodCusp x
    · have hg' : GoodCusp (x.nu s) := hiff.2 hg
      rw [rg _ hg', rg x hg, lpTw_eq ha]
      exact H2 x hx hg _ _
    · have hg' : ¬ GoodCusp (x.nu s) := fun q => hg (hiff.1 q)
      have d : (x.nu s).1 = x.1 := ((clBasic _ x).2.1 _ (isSmoothChar_absPow (s : ℂ))).1
      rw [rb _ hg', rb x hg, d, (he x hx.1).1 s, WD.lpTw_add]
  · by_cases hg : GoodCusp x
    · rw [hcen x hx hg ω hω σ]
    · rw [rb x hg]
      exact (he x hx.1).2 ω hω _ (hJ _ (two x hx hg)).2.1 (hJ _ (two x hx hg)).2.2.1 σ
  · have hg' : GoodCusp (x.tw χ hχ) := ((clBasic _ x).2.1 χ hχ).2.2.1.2 hg
    rw [rg _ hg', rg x hg]
    exact H2 x hx hg χ hχ
  · have hg' : GoodCusp y := ((clBasic _ x).2.2.2.2.2.2 y hd).2.2.2.1.2 hg
    rw [rg y hg', rg x hg]
    exact H.dual hx hg hd
  · have hd : x.1 = y.1 := by rw [← (hirr x hx).2, ← (hirr y hy).2, eq]
    rw [rg y hgy] at eq
    by_cases hgx : GoodCusp x
    · rw [rg x hgx] at eq
      by_cases h1 : y.1 = 1
      · obtain ⟨χ', hχ', rfl⟩ := ((clBasic _ y).2.2.2.2.1 h1).2
        obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 (hd.trans h1)).2
        rw [H1, H1] at eq
        have p := (parOne E Ω A w h a ha χ hχ).2.2.2.1
        have q := (parOne E Ω A w h a ha χ' hχ').2.2.2.1
        have key : χ = χ' := by
          refine MonoidHom.ext fun u => ?_
          obtain ⟨σ, rfl⟩ := ha.surj u
          refine Units.ext ?_
          rw [← p σ, ← q σ, eq]
        subst key
        rfl
      · rcases good_cases hy hgy with h1' | ⟨hq, v, χ', hχ', hv, hvd, rfl⟩
        · exact absurd h1' h1
        · rcases good_cases hx hgx with h1' | ⟨-, u, χ, hχ, hu, hud, rfl⟩
          · exact absurd (hd.symm.trans h1') h1
          · exact H.tw_inj hq hu hud hv hvd hχ hχ' eq
    · exfalso
      have hx2 := two x hx hgx
      rw [rb x hgx] at eq
      rcases good_cases hy hgy with h1' | ⟨hq, v, χ, hχ, hv, hvd, rfl⟩
      · omega
      · rw [H2 v hv (goodCusp_self hq hvd) χ hχ] at eq
        have e2 := congrArg (fun V => V.lpTw (-(e x))) eq
        rw [WD.lpTw_add, add_neg_cancel, WD.lpTw_zero, lpTw_eq ha,
          twist_twist ha _ hχ (isSmoothChar_absPow _) (hχ.mul (isSmoothChar_absPow _))] at e2
        exact (hJ _ hx2).2.2.2 hq (r₀ v) _ _ (H3 hq v hv hvd).tame e2
  · rcases good_cases hx hg with h1 | ⟨hq, -, -, -, -, -, -⟩
    · obtain ⟨χ, hχ, rfl⟩ := ((clBasic _ x).2.2.2.2.1 h1).2
      obtain ⟨-, -, -, -, p5, p6, -⟩ := parOne E Ω A w h a ha χ hχ
      rw [rg _ hg, H1]
      exact (p6 (p5.1 hd)).tame
    · rw [rg x hg]
      exact (H3 hq x hx hd).tame
  · intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hInf
    subst hσ
    have hd : DZ (cls σ) := DiscreteGroups.sglob.DzType.lDepth E w g i hi n τ σ hInf
    have hq : ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i := ⟨g, inferInstance, i, hi⟩
    rw [rg _ (goodCusp_self hq hd)]
    exact (H3 hq _ hx hd).type g i hi n hn D R hR θ hθ τ hτ hN σ rfl hInf

end UpperTheory.Zero.LLC

end
