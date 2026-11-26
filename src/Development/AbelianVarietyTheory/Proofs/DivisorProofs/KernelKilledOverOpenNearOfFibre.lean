module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightZeroCocycleEqLogDerivativeCombAddCob

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowSubNsmulMemAugIdealSq
open TensorProduct Polynomial

namespace GlobalTheory

theorem convPow_sub_nsmul_mem_augIdeal_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (ε : B →ₐ[A] A) (Δ : B →ₐ[A] B ⊗[A] B) (α : ℕ → (B →ₐ[A] B)), (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → α 0 = (Algebra.ofId A B).comp ε → (∀ n, α (n+1) = (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ) → ∀ n, ∀ x ∈ RingHom.ker ε, α n x - (n : B) * x ∈ (RingHom.ker ε) ^ 2 := by
  intro A B _ _ _ ε Δ α hL hR h0 hS
  have hεu : ∀ a : A, ε (algebraMap A B a) = a := fun a => by simp
  have hL' : ∀ b, Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hL b
  have hR' : ∀ b, Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hR b

  have hε : ∀ n b, ε (α n b) = ε b := by
    intro n
    induction n with
    | zero => intro b; rw [h0]; simp [hεu]
    | succ n ih =>
      intro b
      have key : ∀ t : B ⊗[A] B,
          ε (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _) t) =
          ε (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t) := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul b c => simp [Algebra.TensorProduct.lift_tmul, ih, hεu]
        | add s t hs ht => simp only [map_add (f := _), hs, ht]
      rw [hS n, AlgHom.comp_apply, key, hL' b]

  have hright : ∀ (ψ : B →ₐ[A] B) (t : B ⊗[A] B),
      Algebra.TensorProduct.lift ψ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t =
      ψ (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
        (fun _ _ => Commute.all _ _) t) := by
    intro ψ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp [Algebra.TensorProduct.lift_tmul]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]

  have gen : ∀ (φ : B →ₐ[A] B), (∀ b, ε (φ b) = ε b) → ∀ t : B ⊗[A] B,
      Algebra.TensorProduct.lift φ (AlgHom.id A B) (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift φ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t
        + Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) ((Algebra.ofId A B).comp ε)
            (fun _ _ => Commute.all _ _) t ∈ RingHom.ker ε ^ 2 := by
    intro φ hφ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply,
        Algebra.ofId_apply]
      have e : φ b * c - algebraMap A B (ε b) * c - φ b * algebraMap A B (ε c)
          + algebraMap A B (ε b) * algebraMap A B (ε c)
          = (φ b - algebraMap A B (ε b)) * (c - algebraMap A B (ε c)) := by ring
      rw [e, sq]
      exact Ideal.mul_mem_mul (by rw [RingHom.mem_ker]; simp [hφ, hεu])
        (by rw [RingHom.mem_ker]; simp [hεu])
    | add s t hs ht =>
      have e := add_mem hs ht
      simp only [map_add (f := _)]
      convert e using 1
      abel
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [h0]
    simp [RingHom.mem_ker.mp hx]
  | succ n ih =>
    intro x hx
    have E := gen (α n) (hε n) (Δ x)
    rw [hL' x, hright (α n) (Δ x), hright ((Algebra.ofId A B).comp ε) (Δ x), hR' x] at E
    have hx0 : ε x = 0 := by simpa using hx
    have h4 : ((Algebra.ofId A B).comp ε) x = 0 := by simp [hx0]
    rw [h4, add_zero] at E
    rw [hS n, AlgHom.comp_apply]
    convert add_mem E (ih x hx) using 1
    push_cast
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalSequenceContinuityAll
open TensorProduct Polynomial

namespace GlobalTheory

theorem torsion_of_one_tmul_eq_zero (D K M : Type) [CommRing D] [IsDomain D] [Field K]
    [Algebra D K] [FaithfulSMul D K] [AddCommGroup M] [Module D M] (m : M)
    (h : (1 : K) ⊗ₜ[D] m = 0) : ∃ d : D, d ≠ 0 ∧ d • m = 0 := by
  letI : Algebra (FractionRing D) K := FractionRing.liftAlgebra D K
  haveI : IsScalarTower D (FractionRing D) K := FractionRing.isScalarTower_liftAlgebra D K
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing D) K)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap (FractionRing D) K).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  have h2 : (1 : FractionRing D) ⊗ₜ[D] m = 0 := by
    have := congrArg ((g.restrictScalars D).rTensor M) h
    simpa [hg1] using this
  obtain ⟨⟨d, hd⟩, hdm⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors D)
    (TensorProduct.mk D (FractionRing D) M 1)).1 h2
  exact ⟨d, nonZeroDivisors.ne_zero hd, hdm⟩

theorem exists_not_mem_ker_smul_mem_map_of_one_tmul_eq_zero (A B K : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Field K] [Algebra A K] (b : B) (h : (1 : K) ⊗ₜ[A] b = 0) :
    ∃ f : A, f ∉ RingHom.ker (algebraMap A K) ∧
      f • b ∈ (RingHom.ker (algebraMap A K)).map (algebraMap A B) := by
  set P := RingHom.ker (algebraMap A K) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  letI : Algebra (A ⧸ P) K := (RingHom.kerLift (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A (A ⧸ P) K := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  haveI : FaithfulSMul (A ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) K).2 (RingHom.kerLift_injective _)
  let I := P.map (algebraMap A B)
  let q : B →ₗ[A] B ⧸ I := (Ideal.Quotient.mkₐ A I).toLinearMap
  let Φ : K ⊗[A] B →ₗ[A] K ⊗[A ⧸ P] (B ⧸ I) :=
    (TensorProduct.mapOfCompatibleSMul (A ⧸ P) A A K (B ⧸ I)) ∘ₗ q.lTensor K
  have h1 : (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) = 0 := by
    have hΦ : Φ ((1 : K) ⊗ₜ[A] b) = (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) := rfl
    rw [← hΦ, h, map_zero]
  obtain ⟨d, hd0, hdb⟩ := torsion_of_one_tmul_eq_zero (A ⧸ P) K (B ⧸ I) _ h1
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨f, fun hf => hd0 (Ideal.Quotient.eq_zero_iff_mem.2 hf), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : Ideal.Quotient.mk I (f • b) = (Ideal.Quotient.mk P f) • Ideal.Quotient.mk I b := by
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl
  rw [this, hdb]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNotMemSmulEqZeroOfSubmodule
open TensorProduct Polynomial

namespace GlobalTheory.NakAug

theorem eval_notMem_of_monic {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] (p : A[X])
    (hmon : p.Monic) (hc : ∀ k, p.coeff k ∈ P ^ (p.natDegree - k)) (t : A) (ht : t ∉ P) :
    p.eval t ∉ P := by
  intro hmem
  rw [eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hmem
  have hs : ∑ i ∈ Finset.range p.natDegree, p.coeff i * t ^ i ∈ P := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hc i)
  have : t ^ p.natDegree ∈ P := by
    have := P.sub_mem hmem hs
    simpa using this
  exact ht (Ideal.IsPrime.mem_of_pow_mem inferInstance _ this)

theorem exists_notMem_smul_eq_zero {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (P : Ideal A) [P.IsPrime] (t : A) (ht : t ∉ P)
    (h : ∀ m : M, t • m ∈ P • (⊤ : Submodule A M)) :
    ∃ g : A, g ∉ P ∧ ∀ m : M, g • m = 0 := by
  obtain ⟨p, hmon, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A
      (algebraMap A (Module.End A M) t) P (by
        rintro _ ⟨m, rfl⟩
        simpa [Module.algebraMap_end_apply] using h m)
  refine ⟨p.eval t, eval_notMem_of_monic P p hmon hc t ht, fun m => ?_⟩
  rw [aeval_algebraMap_apply_eq_algebraMap_eval] at h0
  have := congrArg (fun φ : Module.End A M => φ m) h0
  simpa [Module.algebraMap_end_apply] using this

theorem exists_notMem_smul_eq_zero_of_submodule {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (P : Ideal A) [P.IsPrime] (N : Submodule A M) (hN : N.FG) (t : A) (ht : t ∉ P)
    (h : ∀ m ∈ N, t • m ∈ P • N) :
    ∃ g : A, g ∉ P ∧ ∀ m ∈ N, g • m = 0 := by
  haveI : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  obtain ⟨g, hg, h0⟩ := exists_notMem_smul_eq_zero (M := N) P t ht (fun m => by
    have hm := h m m.2
    have hmap : P • N = (P • (⊤ : Submodule A N)).map N.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [hmap] at hm
    obtain ⟨z, hz, hzm⟩ := hm
    have : z = t • m := Subtype.ext (by simpa using hzm)
    exact this ▸ hz)
  exact ⟨g, hg, fun m hm => by simpa using congrArg Subtype.val (h0 ⟨m, hm⟩)⟩

theorem exists_uniform_notMem {A M M' : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M] (P : Ideal A) [hP : P.IsPrime]
    (S : Submodule A M') (D : M →ₗ[A] M') (h : ∀ b, ∃ f : A, f ∉ P ∧ f • D b ∈ S) :
    ∃ f : A, f ∉ P ∧ ∀ b, f • D b ∈ S := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  have key : ∀ t : Finset M, ∃ f : A, f ∉ P ∧ ∀ b ∈ t, f • D b ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert a t ha ih =>
      obtain ⟨F, hF, hFt⟩ := ih
      obtain ⟨fa, hfa, hfaa⟩ := h a
      refine ⟨fa * F, fun hm => (hP.mem_or_mem hm).elim hfa hF, fun b hb => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hfaa
      · rw [mul_smul]; exact S.smul_mem _ (hFt b hb)
  obtain ⟨f, hf, hfs⟩ := key s
  refine ⟨f, hf, fun b => ?_⟩
  have hle : Submodule.span A (s : Set M) ≤ S.comap (f • D) := by
    rw [Submodule.span_le]
    intro b hb
    exact hfs b hb
  have hb : b ∈ Submodule.span A (s : Set M) := hs ▸ Submodule.mem_top
  simpa using hle hb

theorem augmentation_agrees_after_inverting
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    (P : Ideal A) [hP : P.IsPrime] (ε : B →ₐ[A] A) (α : B →ₐ[A] B) (d : ℕ) (hd : (d : A) ∉ P)
    (h2 : ∀ x ∈ RingHom.ker ε, α x - (d : B) * x ∈ (RingHom.ker ε) ^ 2)
    (h3 : ∀ b, ∃ f : A, f ∉ P ∧ f • (α b - algebraMap A B (ε b)) ∈ P.map (algebraMap A B)) :
    ∃ g : A, g ∉ P ∧ ∀ b, g • (α b - algebraMap A B (ε b)) = 0 := by
  classical
  set J : Ideal B := RingHom.ker ε with hJdef
  set Q : Ideal B := P.map (algebraMap A B) with hQdef
  haveI : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B

  let D : B →ₗ[A] B := α.toLinearMap - (Algebra.linearMap A B).comp ε.toLinearMap
  have hDapp : ∀ b, D b = α b - algebraMap A B (ε b) := fun b => rfl
  obtain ⟨f, hf, hfD⟩ := exists_uniform_notMem P (Q.restrictScalars A) D
    (fun b => by simpa only [hDapp, Submodule.restrictScalars_mem] using h3 b)
  have hmemJ : ∀ x, x ∈ J ↔ ε x = 0 := fun x => RingHom.mem_ker
  have hφ : ∀ b, b - algebraMap A B (ε b) ∈ J := fun b => by
    rw [hmemJ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hαφ : ∀ b, α (b - algebraMap A B (ε b)) = α b - algebraMap A B (ε b) := fun b => by
    rw [map_sub, AlgHom.commutes]
  have hαJ : ∀ x ∈ J, α x ∈ J := fun x hx => by
    have h := h2 x hx
    have e : α x = (α x - (d : B) * x) + (d : B) * x := by ring
    rw [e]
    exact J.add_mem (Ideal.pow_le_self two_ne_zero h) (J.mul_mem_left _ hx)

  have hfαQ : ∀ x ∈ J, algebraMap A B f * α x ∈ Q := fun x hx => by
    have h := hfD x
    rw [hDapp, (hmemJ x).mp hx, map_zero, sub_zero, Algebra.smul_def] at h
    exact h

  have hL1 : ∀ y ∈ Q, y ∈ J → y ∈ P • J.restrictScalars A := fun y hyQ hyJ => by
    let φ : B →ₗ[A] B := LinearMap.id - (Algebra.linearMap A B).comp ε.toLinearMap
    have hy : y ∈ P • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]; exact hyQ
    have h1 : φ y ∈ (P • (⊤ : Submodule A B)).map φ := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at h1
    have hle : (⊤ : Submodule A B).map φ ≤ J.restrictScalars A := by
      rintro _ ⟨b, -, rfl⟩
      exact hφ b
    have hφy : φ y = y := by
      show y - algebraMap A B (ε y) = y
      rw [(hmemJ y).mp hyJ, map_zero, sub_zero]
    rw [hφy] at h1
    exact Submodule.smul_mono le_rfl hle h1

  have hs : ∃ s : A, s ∉ P ∧ ∀ x ∈ J, algebraMap A B s * x ∈ J ^ 2 := by
    let L : B →ₗ[A] B ⧸ J ^ 2 := (Ideal.Quotient.mkₐ A (J ^ 2)).toLinearMap
    have hL : ∀ x, L x = Ideal.Quotient.mk (J ^ 2) x := fun x => rfl
    let N : Submodule A (B ⧸ J ^ 2) := (J.map (Ideal.Quotient.mk (J ^ 2))).restrictScalars A
    have hNfg : N.FG := IsNoetherian.noetherian N
    obtain ⟨s, hs, hs0⟩ := exists_notMem_smul_eq_zero_of_submodule P N hNfg (f * d)
      (fun hm => (hP.mem_or_mem hm).elim hf hd) (fun m hm => by
        obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hm
        have e1 : (f * (d : A)) • Ideal.Quotient.mk (J ^ 2) x
            = L (algebraMap A B f * α x) := by
          rw [← hL, ← map_smul, hL, hL, Ideal.Quotient.eq, Algebra.smul_def, map_mul, map_natCast]
          have : algebraMap A B f * (d : B) * x - algebraMap A B f * α x
              = - (algebraMap A B f * (α x - (d : B) * x)) := by ring
          rw [this]
          exact (J ^ 2).neg_mem ((J ^ 2).mul_mem_left _ (h2 x hx))
        rw [e1]
        have hy := hL1 _ (hfαQ x hx) (J.mul_mem_left _ (hαJ x hx))
        have h1 : L (algebraMap A B f * α x) ∈ (P • J.restrictScalars A).map L :=
          Submodule.mem_map_of_mem hy
        rw [Submodule.map_smul''] at h1
        refine Submodule.smul_mono le_rfl ?_ h1
        rintro _ ⟨z, hz, rfl⟩
        exact Ideal.mem_map_of_mem _ hz)
    refine ⟨s, hs, fun x hx => ?_⟩
    have h0 := hs0 _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk (J ^ 2)) hx)
    rw [← hL, ← map_smul, hL, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def] at h0
    exact h0
  obtain ⟨s, hsP, hsJ⟩ := hs

  set K : Ideal B := J.map α with hKdef
  have hKfg : (K.restrictScalars A).FG := IsNoetherian.noetherian _
  have hJ2 : ∀ y ∈ J ^ 2, algebraMap A B f * α y ∈ Q * K := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun y1 hy1 y2 hy2 => ?_) (fun a b ha hb => ?_)
    · rw [map_mul, ← mul_assoc]
      exact Ideal.mul_mem_mul (hfαQ y1 hy1) (Ideal.mem_map_of_mem α hy2)
    · rw [map_add (f := _), mul_add]; exact Ideal.add_mem _ ha hb
  have hKt : ∀ m ∈ K.restrictScalars A, (s * f) • m ∈ P • K.restrictScalars A := by
    intro m hm
    rw [← Ideal.smul_restrictScalars, Submodule.restrictScalars_mem, Ideal.smul_eq_mul,
      Algebra.smul_def]
    rw [Submodule.restrictScalars_mem] at hm
    refine Submodule.span_induction (p := fun m _ => algebraMap A B (s * f) * m ∈ Q * K)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨x, hx, rfl⟩
      have e : algebraMap A B (s * f) * α x = algebraMap A B f * α (algebraMap A B s * x) := by
        rw [map_mul, map_mul, AlgHom.commutes]; ring
      rw [e]; exact hJ2 _ (hsJ x hx)
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact Ideal.add_mem _ hx hy
    · intro b x _ hx; rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ b hx
  obtain ⟨g, hg, hg0⟩ := exists_notMem_smul_eq_zero_of_submodule P (K.restrictScalars A) hKfg
    (s * f) (fun hm => (hP.mem_or_mem hm).elim hsP hf) hKt
  refine ⟨g, hg, fun b => ?_⟩
  rw [← hαφ]
  exact hg0 _ (Ideal.mem_map_of_mem α (hφ b))

end GlobalTheory.NakAug
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FiniteKilled

variable {S' : Scheme.{0}} {A B : CommRingCat.{0}} (jU : Spec A ⟶ S') {Z : Over S'}
  (jW : Spec B ⟶ Z.left) (φ : A ⟶ B)

def tst {R : CommRingCat.{0}} (χ : A ⟶ R) : Over S' := Over.mk (Spec.map χ ≫ jU)

def tmap {R R' : CommRingCat.{0}} {χ : A ⟶ R} {χ' : A ⟶ R'} (σ : R ⟶ R') (h : χ ≫ σ = χ') :
    tst jU χ' ⟶ tst jU χ :=
  Over.homMk (Spec.map σ) (by simp [tst, ← h, Spec.map_comp])

variable {jU jW φ}

def pt (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) {R : CommRingCat.{0}} {χ : A ⟶ R} (ψ : B ⟶ R)
    (h : φ ≫ ψ = χ) : tst jU χ ⟶ Z :=
  Over.homMk (Spec.map ψ ≫ jW) (by
    simp only [tst, Over.mk_hom, Category.assoc, ← hc, ← Spec.map_comp_assoc, h])

theorem tmap_pt (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) {R R' : CommRingCat.{0}} {χ : A ⟶ R}
    {χ' : A ⟶ R'} (σ : R ⟶ R') (h : χ ≫ σ = χ') (ψ : B ⟶ R) (h' : φ ≫ ψ = χ) :
    tmap jU σ h ≫ pt hc ψ h' = pt hc (ψ ≫ σ) (by rw [← Category.assoc, h', h]) := by
  ext1
  change Spec.map σ ≫ Spec.map ψ ≫ jW = Spec.map (ψ ≫ σ) ≫ jW
  rw [Spec.map_comp, Category.assoc]

theorem pt_inj (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) [IsOpenImmersion jW] {G : Over S'} (i : Z ⟶ G)
    [Mono i] {R : CommRingCat.{0}} {χ : A ⟶ R} (ψ ψ' : B ⟶ R) (h : φ ≫ ψ = χ) (h' : φ ≫ ψ' = χ)
    (e : pt hc ψ h ≫ i = pt hc ψ' h' ≫ i) : ψ = ψ' := by
  have e1 := congrArg CommaMorphism.left (cancel_mono i |>.mp e)
  simp only [pt, Over.homMk_left] at e1
  exact Spec.map_injective ((cancel_mono jW).mp e1)

end GlobalTheory.FiniteKilled

end

noncomputable section

namespace GlobalTheory.FiniteKilled

noncomputable def powAlg {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (ε : B →ₐ[A] A)
    (Δ : B →ₐ[A] B ⊗[A] B) (n : ℕ) : B →ₐ[A] B :=
  Nat.rec ((Algebra.ofId A B).comp ε)
    (fun _ a => (Algebra.TensorProduct.lift a (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ) n

variable {S' : Scheme.{0}} {A B : CommRingCat.{0}} {jU : Spec A ⟶ S'} {Z : Over S'}
  {jW : Spec B ⟶ Z.left} {φ : A ⟶ B}

theorem pt_congr (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) {R : CommRingCat.{0}} {χ : A ⟶ R} {ψ ψ' : B ⟶ R}
    (h : φ ≫ ψ = χ) (e : ψ = ψ') : pt hc ψ h = pt hc ψ' (e ▸ h) := by
  subst e; rfl

theorem exists_alg [Algebra A B] (hφ : φ = CommRingCat.ofHom (algebraMap A B))
    (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) [IsOpenImmersion jW] {G : Over S'} [GrpObj G] (i : Z ⟶ G) [Mono i]
    (hone : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R), ∃ z : tst jU χ ⟶ Z, z ≫ i = 1)
    (hmul : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (a b : tst jU χ ⟶ Z), ∃ c : tst jU χ ⟶ Z,
      c ≫ i = (a ≫ i) * (b ≫ i))
    (hfac : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (z : tst jU χ ⟶ Z), ∃ (ψ : B ⟶ R) (h : φ ≫ ψ = χ),
      z = pt hc ψ h) :
    ∃ (ε : B →ₐ[A] A) (Δ : B →ₐ[A] B ⊗[A] B),
      (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
        (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B ∧
      (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
        (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B ∧
      ∀ n (h : φ ≫ CommRingCat.ofHom (powAlg ε Δ n).toRingHom = φ),
        pt hc (CommRingCat.ofHom (powAlg ε Δ n).toRingHom) h ≫ i =
          (pt hc (𝟙 B) (Category.comp_id φ) ≫ i) ^ n := by
  subst hφ

  have und : ∀ {R : Type} [CommRing R] [Algebra A R] (f : B →ₐ[A] R),
      CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom f.toRingHom =
        CommRingCat.ofHom (algebraMap A R) := by
    intro R _ _ f; ext a; simp

  obtain ⟨e0, he0⟩ := hone A (𝟙 A)
  obtain ⟨εc, hε, rfl⟩ := hfac A (𝟙 A) e0
  let ε : B →ₐ[A] A :=
    { εc.hom with commutes' := fun a => congrArg (fun f => f.hom a) hε }
  have hεc : CommRingCat.ofHom ε.toRingHom = εc := rfl
  have hunit : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (σ : A ⟶ R) (h : CommRingCat.ofHom (algebraMap A B) ≫ εc ≫ σ = χ),
      pt hc (εc ≫ σ) h ≫ i = 1 := by
    intro R χ σ h
    have h1 : 𝟙 A ≫ σ = χ := by rw [← h, ← Category.assoc, hε]
    rw [← tmap_pt hc σ h1 εc hε, Category.assoc, he0, comp_one]

  let R2 := CommRingCat.of (B ⊗[A] B)
  let χ2 : A ⟶ R2 := CommRingCat.ofHom (algebraMap A (B ⊗[A] B))
  let inl : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let inr : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  obtain ⟨c, hcm⟩ := hmul R2 χ2 (pt hc (CommRingCat.ofHom inl.toRingHom) (und inl))
    (pt hc (CommRingCat.ofHom inr.toRingHom) (und inr))
  obtain ⟨Δc, hΔ, rfl⟩ := hfac R2 χ2 c
  let Δ : B →ₐ[A] B ⊗[A] B :=
    { Δc.hom with commutes' := fun a => congrArg (fun f => f.hom a) hΔ }

  have key : ∀ {R : Type} [CommRing R] [Algebra A R] (f g : B →ₐ[A] R),
      pt hc (CommRingCat.ofHom ((Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).comp Δ).toRingHom)
          (und _) ≫ i =
        (pt hc (CommRingCat.ofHom f.toRingHom) (und f) ≫ i) *
          (pt hc (CommRingCat.ofHom g.toRingHom) (und g) ≫ i) := by
    intro R _ _ f g
    let L : R2 ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
    have hL : χ2 ≫ L = CommRingCat.ofHom (algebraMap A R) := by
      ext a; exact (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).commutes a
    have e1 : Δc ≫ L = CommRingCat.ofHom
        ((Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).comp Δ).toRingHom := rfl
    have e2 : CommRingCat.ofHom inl.toRingHom ≫ L = CommRingCat.ofHom f.toRingHom := by
      ext b; simp [L, inl]
    have e3 : CommRingCat.ofHom inr.toRingHom ≫ L = CommRingCat.ofHom g.toRingHom := by
      ext b; simp [L, inr]
    rw [pt_congr hc _ e1.symm, ← tmap_pt hc L hL Δc hΔ, Category.assoc, hcm, comp_mul,
      ← Category.assoc, ← Category.assoc, tmap_pt, tmap_pt, pt_congr hc _ e2, pt_congr hc _ e3]
  have hηε : ∀ (h : CommRingCat.ofHom (algebraMap A B) ≫
      CommRingCat.ofHom ((Algebra.ofId A B).comp ε).toRingHom = CommRingCat.ofHom (algebraMap A B)),
      pt hc (CommRingCat.ofHom ((Algebra.ofId A B).comp ε).toRingHom) h ≫ i = 1 := by
    intro h
    have e : CommRingCat.ofHom ((Algebra.ofId A B).comp ε).toRingHom = εc ≫ CommRingCat.ofHom (algebraMap A B) := by
      ext b; rfl
    rw [pt_congr hc h e]
    exact hunit _ _ _ _
  have hid : CommRingCat.ofHom (AlgHom.id A B).toRingHom = 𝟙 B := by ext b; rfl
  have hu : ∀ h, pt hc (CommRingCat.ofHom (AlgHom.id A B).toRingHom) h = pt hc (𝟙 B) (Category.comp_id _) :=
    fun h => pt_congr hc h hid
  refine ⟨ε, Δ, ?_, ?_, ?_⟩
  · have k := key ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
    rw [hηε, _root_.one_mul] at k
    have := pt_inj hc i _ _ (und _) (und _) k
    ext b
    exact congrArg (fun f => f.hom b) this
  · have k := key (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
    rw [hηε, _root_.mul_one] at k
    have := pt_inj hc i _ _ (und _) (und _) k
    ext b
    exact congrArg (fun f => f.hom b) this
  · intro n
    induction n with
    | zero => intro h; rw [pow_zero]; exact hηε h
    | succ n ih =>
      intro h
      have k := key (powAlg ε Δ n) (AlgHom.id A B)
      rw [ih (und _), hu (und _), ← pow_succ] at k
      exact k

end GlobalTheory.FiniteKilled

end

namespace GlobalTheory.FiniteKilled

theorem isUnit_of_basicOpen_eq_top' (X : Scheme.{0}) (r : Γ(X, ⊤)) (h : X.basicOpen r = ⊤) : IsUnit r := by
  have hu := X.toRingedSpace.isUnit_res_basicOpen r
  have := hu.map (X.presheaf.map (homOfLE h.ge).op).hom
  have e : ∀ y, (X.presheaf.map (homOfLE h.ge).op).hom
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y) = y := by
    intro y
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rw [show (homOfLE (X.basicOpen_le r)).op ≫ (homOfLE h.ge).op = 𝟙 (Opposite.op (⊤ : X.Opens)) from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]
    rfl
  exact (e r) ▸ this

theorem spec_inv_appTop {B : CommRingCat.{0}} (t : B ⟶ B) :
    (Scheme.ΓSpecIso B).inv ≫ (Spec.map t).appTop = t ≫ (Scheme.ΓSpecIso B).inv := by
  have := Scheme.ΓSpecIso_naturality t
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  simp

theorem spec_eq_of_unit {X : Scheme.{0}} {B : CommRingCat.{0}} (k : X ⟶ Spec B) (α β : B ⟶ B) (b0 : B)
    (hu : IsUnit (((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom b0))
    (h : ∀ b, b0 * (α.hom b - β.hom b) = 0) : k ≫ Spec.map α = k ≫ Spec.map β := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Category.assoc, ← Category.assoc, spec_inv_appTop, spec_inv_appTop, Category.assoc, Category.assoc]
  ext b
  have e := congrArg ((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom (h b)
  rw [map_mul, map_sub, map_zero, hu.mul_right_eq_zero, sub_eq_zero] at e
  exact e

theorem isUnit_of_range {X S : Scheme.{0}} {U : S.Opens} (hU : IsAffineOpen U) {B : CommRingCat.{0}}
    (k : X ⟶ Spec B) (φ : Γ(S, U) ⟶ B) (g : Γ(S, U))
    (hr : ∀ x, (k ≫ Spec.map φ ≫ hU.fromSpec).base x ∈ S.basicOpen g) :
    IsUnit (((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom (φ.hom g)) := by
  have e1 : ((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom (φ.hom g) =
      (k ≫ Spec.map φ).appTop.hom ((Scheme.ΓSpecIso Γ(S, U)).inv.hom g) := by
    have := Scheme.ΓSpecIso_naturality φ
    rw [← Iso.eq_comp_inv] at this
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [this]
    simp only [CommRingCat.comp_apply]
    congr 2
    exact congrArg φ.hom (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(S, U)) g).symm
  rw [e1]
  apply isUnit_of_basicOpen_eq_top'
  have e2 := Scheme.preimage_basicOpen (k ≫ Spec.map φ) ((Scheme.ΓSpecIso Γ(S, U)).inv.hom g)
  have e3 := Scheme.preimage_basicOpen hU.fromSpec g
  rw [IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply, Scheme.basicOpen_res_eq] at e3
  change X.basicOpen ((k ≫ Spec.map φ).app ⊤ _) = ⊤
  rw [← e2, ← e3, eq_top_iff]
  intro x _
  exact hr x

end GlobalTheory.FiniteKilled

namespace GlobalTheory.FiniteKilled

theorem killed_near : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (Z : Over S') (i : Z ⟶ G) (V₀ : S'.Opens) (d : ℕ) (s : S'), Mono i → s ∈ V₀ → IsFinite (Z.hom ∣_ V₀) → (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) → (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) → (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) → IsUnit ((d : ℕ) : S'.residueField s) → (∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s), T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1) → ∃ V : S'.Opens, s ∈ V ∧ V ≤ V₀ ∧ ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V : Set S') → (z ≫ i) ^ d = 1 := by
  intro S' _ G _ _ Z i V₀ d s hi hs hfin hone hmul hinv hd hfib

  obtain ⟨U, hU, hsU, hUV⟩ := exists_isAffineOpen_mem_and_subset hs
  have hUV : U ≤ V₀ := hUV
  have hfU : IsFinite (Z.hom ∣_ U) := by
    haveI : MorphismProperty.RespectsIso @IsFinite :=
      MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f (_ : IsIso f) => inferInstance)
    have h1 : IsFinite (Z.hom ∣_ V₀ ∣_ (V₀.ι ⁻¹ᵁ U)) := inferInstance
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) (morphismRestrictRestrict _ _ _),
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hUV] at h1
    exact h1
  haveI : IsAffine U := hU
  set W : Z.left.Opens := Z.hom ⁻¹ᵁ U with hWdef
  have hW : IsAffineOpen W := by
    have h1 := (IsAffineHom.isAffine_preimage (f := Z.hom ∣_ U) ⊤ (isAffineOpen_top _)).image_of_isOpenImmersion
      (Z.hom ⁻¹ᵁ U).ι
    rwa [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top] at h1
  let A : CommRingCat.{0} := Γ(S', U)
  let B : CommRingCat.{0} := Γ(Z.left, W)
  let φ : A ⟶ B := Z.hom.appLE U W le_rfl
  letI : Algebra A B := φ.hom.toAlgebra
  have hφ : φ = CommRingCat.ofHom (algebraMap A B) := rfl
  haveI hfinAB : Module.Finite A B := by
    have h1 := IsFinite.finite_app (Z.hom ∣_ U) ⊤ (isAffineOpen_top _)
    rw [morphismRestrict_app'] at h1
    have gen : ∀ (U₁ : S'.Opens) (W₁ : Z.left.Opens) (e₁ : U₁ = U) (e₂ : W₁ = W) (hle : W₁ ≤ Z.hom ⁻¹ᵁ U₁),
        (Z.hom.appLE U₁ W₁ hle).hom.Finite → φ.hom.Finite := by
      rintro _ _ rfl rfl _ h; exact h
    exact gen _ _ (Scheme.Opens.ι_image_top U) (by simp [W]) _ h1
  have hS : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let jU := hU.fromSpec
  let jW := hW.fromSpec
  have hc : Spec.map φ ≫ jU = jW ≫ Z.hom := IsAffineOpen.SpecMap_appLE_fromSpec Z.hom hU hW le_rfl

  have hrange : ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (U : Set S') →
      ∃ k : T.left ⟶ Spec B, k ≫ jW = z.left := by
    intro T z hT
    refine ⟨IsOpenImmersion.lift jW z.left ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    rw [hW.range_fromSpec]
    show Z.hom.base (z.left.base x) ∈ U
    rw [← Scheme.Hom.comp_apply, Over.w z]
    exact hT ⟨x, rfl⟩
  have hrT : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R), Set.range (tst jU χ).hom.base ⊆ (U : Set S') := by
    rintro R χ _ ⟨x, rfl⟩
    rw [← hU.range_fromSpec]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ x).symm⟩
  have hfac : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (z : tst jU χ ⟶ Z), ∃ (ψ : B ⟶ R) (h : φ ≫ ψ = χ),
      z = pt hc ψ h := by
    intro R χ z
    obtain ⟨k, hk⟩ := hrange _ z (hrT R χ)
    have hk' : Spec.map (Spec.preimage (k : Spec R ⟶ Spec B)) = k := Spec.map_preimage _
    have h : φ ≫ Spec.preimage k = χ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hk', ← cancel_mono jU]
      erw [Category.assoc, hc, ← Category.assoc, hk, Over.w z]
      rfl
    refine ⟨Spec.preimage k, h, ?_⟩
    ext1
    change z.left = Spec.map (Spec.preimage k) ≫ jW
    rw [hk']
    exact hk.symm
  obtain ⟨ε, Δ, hc1, hc2, hpow⟩ := exists_alg hφ hc i
    (fun R χ => hone _ ((hrT R χ).trans hUV)) (fun R χ a b => hmul _ a b ((hrT R χ).trans hUV)) hfac
  let α := powAlg ε Δ
  have hund : ∀ n, φ ≫ CommRingCat.ofHom (α n).toRingHom = φ := fun n => by
    ext a; exact (α n).commutes a
  have hcot := GlobalTheory.convPow_sub_nsmul_mem_augIdeal_sq A B ε Δ α hc1 hc2 rfl (fun n => rfl)

  let κ := S'.residueField s
  let χκ : A ⟶ κ := S'.presheaf.germ U s hsU ≫ S'.residue s
  letI : Algebra A κ := χκ.hom.toAlgebra
  let R := CommRingCat.of (κ ⊗[A] B)
  let incl : B →ₐ[A] κ ⊗[A] B := Algebra.TensorProduct.includeRight
  let incL : κ →ₐ[A] κ ⊗[A] B := Algebra.TensorProduct.includeLeft
  let χR : A ⟶ R := CommRingCat.ofHom (algebraMap A (κ ⊗[A] B))
  have hincl : φ ≫ CommRingCat.ofHom incl.toRingHom = χR := by ext a; exact incl.commutes a
  have hTk : (tst jU χR).hom = Spec.map (CommRingCat.ofHom incL.toRingHom) ≫ S'.fromSpecResidueField s := by
    rw [Scheme.fromSpecResidueField, ← hU.fromSpecStalk_eq_fromSpecStalk hsU, IsAffineOpen.fromSpecStalk]
    change Spec.map χR ≫ jU = _
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
  have hfibk : (pt hc (CommRingCat.ofHom incl.toRingHom) hincl ≫ i) ^ d = 1 := hfib _ _ ⟨_, hTk⟩
  have hpt : ∀ n, pt hc (CommRingCat.ofHom (α n).toRingHom ≫ CommRingCat.ofHom incl.toRingHom)
      (by rw [← Category.assoc, hund n, hincl]) ≫ i = (pt hc (CommRingCat.ofHom incl.toRingHom) hincl ≫ i) ^ n := by
    intro n
    rw [← tmap_pt hc _ hincl _ (hund n), Category.assoc, hpow n (hund n), comp_pow, ← Category.assoc, tmap_pt,
      pt_congr hc _ (Category.id_comp _)]
  have heq : CommRingCat.ofHom (α d).toRingHom ≫ CommRingCat.ofHom incl.toRingHom =
      CommRingCat.ofHom (α 0).toRingHom ≫ CommRingCat.ofHom incl.toRingHom :=
    pt_inj hc i _ _ _ _ (by rw [hpt d, hpt 0, hfibk, pow_zero])
  have hzero : ∀ b : B, (1 : κ) ⊗ₜ[A] (α d b - algebraMap A B (ε b)) = 0 := by
    intro b
    have := congrArg (fun f => f.hom b) heq
    rw [TensorProduct.tmul_sub, sub_eq_zero]
    exact this
  let P : Ideal A := RingHom.ker (algebraMap A κ)
  have hfibP : ∀ b, ∃ f : A, f ∉ P ∧ f • (α d b - algebraMap A B (ε b)) ∈ P.map (algebraMap A B) :=
    fun b => GlobalTheory.exists_not_mem_ker_smul_mem_map_of_one_tmul_eq_zero A B κ _ (hzero b)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hdP : (d : A) ∉ P := by
    rw [RingHom.mem_ker, map_natCast]; exact hd.ne_zero
  obtain ⟨g, hgP, hg⟩ := GlobalTheory.NakAug.augmentation_agrees_after_inverting A B P ε (α d) d hdP (hcot d) hfibP
  refine ⟨S'.basicOpen g, ?_, (S'.basicOpen_le g).trans hUV, ?_⟩
  · rw [Scheme.mem_basicOpen S' g s hsU, ← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    exact hgP (RingHom.mem_ker.mpr h0)
  · intro T z hT
    have hTU : Set.range T.hom.base ⊆ (U : Set S') := hT.trans (S'.basicOpen_le g)
    obtain ⟨k, hk⟩ := hrange T z hTU
    have hkT : k ≫ Spec.map φ ≫ jU = T.hom := by rw [hc, ← Category.assoc, hk, Over.w z]
    let H : T ⟶ tst jU φ := Over.homMk k hkT
    have hz : z = H ≫ pt hc (𝟙 B) (Category.comp_id φ) := by
      ext1
      change z.left = k ≫ Spec.map (𝟙 B) ≫ jW
      rw [Spec.map_id, Category.id_comp, hk]
    have hkey : k ≫ Spec.map (CommRingCat.ofHom (α d).toRingHom) =
        k ≫ Spec.map (CommRingCat.ofHom (α 0).toRingHom) := by
      refine spec_eq_of_unit k _ _ (φ.hom g) (isUnit_of_range hU k φ g ?_) ?_
      · intro x; rw [hkT]; exact hT ⟨x, rfl⟩
      · intro b; have := hg b; rwa [Algebra.smul_def] at this
    have hHeq : H ≫ pt hc (CommRingCat.ofHom (α d).toRingHom) (hund d) =
        H ≫ pt hc (CommRingCat.ofHom (α 0).toRingHom) (hund 0) := by
      ext1
      change k ≫ Spec.map _ ≫ jW = k ≫ Spec.map _ ≫ jW
      rw [← Category.assoc, hkey, Category.assoc]
    rw [hz, Category.assoc, ← comp_pow, ← hpow d (hund d), ← Category.assoc, hHeq, Category.assoc,
      hpow 0 (hund 0), pow_zero, comp_one]

end GlobalTheory.FiniteKilled
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupKilledNearPointOfFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (Z : Over S') (i : Z ⟶ G) (V₀ : S'.Opens) (d : ℕ) (s : S'), Mono i → s ∈ V₀ → IsFinite (Z.hom ∣_ V₀) → (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) → (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) → (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) → IsUnit ((d : ℕ) : S'.residueField s) → (∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s), T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1) → ∃ V : S'.Opens, s ∈ V ∧ V ≤ V₀ ∧ ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V : Set S') → (z ≫ i) ^ d = 1 := by
  first | (exact @GlobalTheory.FiniteKilled.killed_near) | (exact GlobalTheory.FiniteKilled.killed_near) | (intros; apply GlobalTheory.FiniteKilled.killed_near  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibreOpen

theorem eq_one_of_local {S' : Scheme.{0}} {G : Over S'} [GrpObj G] (T : Over S') (x : T ⟶ G)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨U, hp, hx⟩ := h p
  refine ⟨U, hp, ?_⟩
  have h1 : (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ (1 : T ⟶ G) = 1 := MonObj.comp_one _
  rw [← h1] at hx
  exact congrArg (fun q => q.left) hx

theorem unit_residue : ∀ (S' : Scheme.{0}) (W : S'.Opens) (s : S'), s ∈ W → ∀ d : ℕ, IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → IsUnit ((d : ℕ) : S'.residueField s) := by
  intro S' W s hs d hd
  let x : W.toScheme := ⟨s, hs⟩
  have h1 : IsUnit ((d : ℕ) : W.toScheme.residueField x) := by
    have := hd.map (W.toScheme.evaluation ⊤ x trivial).hom
    simpa using this
  have hx : W.ι.base x = s := rfl
  rw [isUnit_iff_ne_zero] at h1 ⊢
  intro h0
  apply h1
  have := congrArg (Scheme.Hom.residueFieldMap W.ι x).hom (hx ▸ h0 : ((d : ℕ) : S'.residueField (W.ι.base x)) = 0)
  simpa using this


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison GlobalTheory.KerKilledLocal in
theorem kerKilledOn_of_global : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (V : S'.Opens), (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → x ^ d = 1) → GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' G _ _ P V h T x hs
  apply down_injective G V
  rw [down_pow, down_one]
  let T' : Over S' := Over.mk (T.hom ≫ V.ι)
  let GV := (Over.pullback V.ι).obj G
  have hr : Set.range T'.hom.base ⊆ (V : Set S') := by
    rintro _ ⟨t, rfl⟩
    have h' : T'.hom.base t ∈ Set.range V.ι.base := ⟨T.hom.base t, rfl⟩
    rwa [Scheme.Opens.range_ι] at h'
  refine h T' (down G V x) hr ?_
  let Y : Over V.toScheme := Over.mk ((snd G T').left ≫ T.hom)
  have w1 : (fst G T').left ≫ G.hom = (G ⊗ T').hom := Over.w (fst G T')
  have w2 : (snd G T').left ≫ (T.hom ≫ V.ι) = (G ⊗ T').hom := Over.w (snd G T')
  let u : Y ⟶ GV := Over.homMk (pullback.lift (fst G T').left ((snd G T').left ≫ T.hom) (by
      rw [w1, Category.assoc, w2])) (pullback.lift_snd _ _ _)
  let v : Y ⟶ T := Over.homMk (snd G T').left rfl
  have heq : (lift u v).left ≫ (lift (snd GV T ≫ x) (fst GV T)).left ≫ pφ₂ V.ι G =
      (lift (snd G T' ≫ down G V x) (fst G T')).left ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply adelic_GL2_ext_of_local_components G
    · simp only [Category.assoc, pφ₂_fst]
      rw [lift_left_fst'_assoc, lift_left_fst']
      simp only [Over.comp_left, Category.assoc]
      rw [lift_left_snd'_assoc]
      rfl
    · simp only [Category.assoc, pφ₂_snd]
      rw [lift_left_snd'_assoc, lift_left_snd', lift_left_fst'_assoc]
      change pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι = _
      rw [pullback.lift_fst]
  obtain ⟨t, ht⟩ := gen_pull3 P (pφ₂ V.ι G) _ (lift u v).left _ (𝟙 _) heq hs
  exact gen_chartPull (chartPullUnpull _ _ rfl) t ht

theorem comp_pow_overScheme_grpObj {S' : Scheme.{0}} {G T T' : Over S'} [GrpObj G] (u : T' ⟶ T) (x : T ⟶ G) :
    ∀ n : ℕ, u ≫ x ^ n = (u ≫ x) ^ n
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj u x n]

theorem kerKilledOn_near_of_fibre : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → ∀ s ∈ W, GlobalTheory.KerKilledNear.FibreKilled d G P s → ∃ V : S'.Opens, s ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym W hamp hd s hs hfib
  obtain ⟨V₀, Z, i, hs₀, hmono, hfin, h1, hmul, hinv, hfac, hloc⟩ := GlobalTheory.T.exists_finite_kernel_near_diagonal_ample S' G P hA hP hg₁ hg₂ hsym W hamp s hs
  have hfibZ : ∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s),
      T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1 := by
    rintro T z ⟨f, hf⟩
    have hT : Set.range T.hom.base ⊆ (V₀ : Set S') := by
      rintro _ ⟨p, rfl⟩
      have e : (f ≫ S'.fromSpecResidueField s).base p = s :=
        Set.mem_singleton_iff.mp (Scheme.range_fromSpecResidueField s ▸ Set.mem_range_self (f.base p))
      rw [hf, e]
      exact hs₀
    refine eq_one_of_local T _ fun p => ?_
    obtain ⟨U, hp, c, hc⟩ := hloc T z hT p
    refine ⟨U, hp, ?_⟩
    rw [comp_pow_overScheme_grpObj]
    exact hfib (Over.mk (U.ι ≫ T.hom)) _ ⟨U.ι ≫ f, by simp [hf]⟩ ⟨c, hc⟩
  obtain ⟨V, hsV, hVV₀, hV⟩ := GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre S' G Z i V₀ d s hmono hs₀ hfin h1 hmul hinv (unit_residue S' W s hs d hd) hfibZ
  refine ⟨V, hsV, kerKilledOn_of_global d S' G P V fun T x hT hx => ?_⟩
  obtain ⟨z, rfl⟩ := hfac T x (hT.trans hVV₀) hx
  exact hV T z hT

end GlobalTheory.KerKilledFibreOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelKilledOverOpen_near_of_fibre : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → ∀ s ∈ W, GlobalTheory.KerKilledNear.FibreKilled d G P s → ∃ V : S'.Opens, s ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  first | (exact @GlobalTheory.KerKilledFibreOpen.kerKilledOn_near_of_fibre) | (exact GlobalTheory.KerKilledFibreOpen.kerKilledOn_near_of_fibre) | (intros; apply GlobalTheory.KerKilledFibreOpen.kerKilledOn_near_of_fibre  <;> assumption)
end
