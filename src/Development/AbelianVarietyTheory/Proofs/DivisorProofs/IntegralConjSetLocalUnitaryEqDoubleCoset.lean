module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdjoinLatticeImageEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpolyStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqOfStableLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqOfStableLattices
open Polynomial Matrix GlobalTheory.LatOrb

noncomputable section

namespace GlobalTheory.LatOrb.Stab

theorem polyStable {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (hM : ∀ v ∈ M, γ *ᵥ v ∈ M) (r : O[X]) :
    ∀ v ∈ M, aeval γ (r.map (algebraMap O K)) *ᵥ v ∈ M := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [Polynomial.map_add (f := _), map_add (f := _), Matrix.add_mulVec]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial k a =>
    intro v hv
    have hpow : ∀ v ∈ M, (γ ^ k) *ᵥ v ∈ M := by
      induction k with
      | zero => intro v hv; simpa using hv
      | succ k ih =>
        intro v hv
        rw [pow_succ, ← Matrix.mulVec_mulVec]
        exact ih _ (hM v hv)
    rw [Polynomial.map_monomial, aeval_monomial, ← Matrix.mulVec_mulVec,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
      algebraMap_smul]
    exact M.smul_mem a (hpow v hv)

end GlobalTheory.LatOrb.Stab

namespace GlobalTheory.LatOrb.Stab

theorem exists_unit_eq_matLat : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by
  intro O K _ _ _ _ _ _ _ n P₀ hcop γ hchar M₁ M₂ hL₁ hL₂ hs₁ hs₂
  have hsep : γ.charpoly.Separable := by rw [hchar]; exact Polynomial.Separable.map hcop
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.T.exists_cyclicVector_of_separable_charpoly' n γ hsep
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra K (Matrix (Fin n) (Fin n) K), A = Algebra.adjoin K {γ} :=
    ⟨_, rfl⟩
  have memA : ∀ a : Matrix (Fin n) (Fin n) K, a ∈ A ↔ ∃ p : K[X], aeval γ p = a := by
    intro a; rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; rfl
  have commA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, rfl⟩ := (memA a).1 ha
    obtain ⟨q, rfl⟩ := (memA b).1 hb
    rw [← map_mul, ← map_mul, mul_comm]
  letI : CommRing A := { A.toRing with mul_comm := fun x y => Subtype.ext (commA _ x.2 _ y.2) }
  haveI : Module.Finite K A := inferInstance
  haveI : IsReduced A := by
    refine ⟨fun a ⟨m, hm⟩ => ?_⟩
    obtain ⟨f, hf⟩ := (memA a).1 a.2
    have h0 : aeval γ (f ^ m) = 0 := by
      rw [map_pow, hf]
      exact congrArg Subtype.val hm
    have hsq : Squarefree (minpoly K γ) :=
      (hsep.of_dvd (Matrix.minpoly_dvd_charpoly γ)).squarefree
    have h1 : minpoly K γ ∣ f := hsq.isRadical m f (minpoly.dvd K γ h0)
    apply Subtype.ext
    rw [← hf]
    exact (minpoly.dvd_iff).1 h1

  let φ : A →ₗ[K] (Fin n → K) :=
    { toFun := fun a => (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  have hφ : ∀ a : A, φ a = (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀ := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [hφ] at ha
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    obtain ⟨p, rfl⟩ := hv₀ u
    obtain ⟨q, hq⟩ := (memA a).1 a.2
    change (a : Matrix (Fin n) (Fin n) K) *ᵥ (aeval γ p *ᵥ v₀) = (0 : Matrix (Fin n) (Fin n) K) *ᵥ _
    rw [Matrix.mulVec_mulVec, ← hq, ← map_mul, mul_comm, map_mul, hq, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_zero, Matrix.zero_mulVec]
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨p, rfl⟩ := hv₀ u
    exact ⟨⟨aeval γ p, (memA _).2 ⟨p, rfl⟩⟩, rfl⟩
  let e : A ≃ₗ[K] (Fin n → K) := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ a : A, e a = (a : Matrix (Fin n) (Fin n) K) *ᵥ v₀ := fun _ => rfl
  let eO : A ≃ₗ[O] (Fin n → K) := e.restrictScalars O
  let J : Submodule O (Fin n → K) → Submodule O A := fun M => M.map (eO.symm : (Fin n → K) →ₗ[O] A)
  have memJ : ∀ M y, y ∈ J M ↔ (y : Matrix (Fin n) (Fin n) K) *ᵥ v₀ ∈ M := by
    intro M y
    simp only [J, Submodule.mem_map_equiv]
    rfl
  have latJ : ∀ M, IsLatV O M → GlobalTheory.UnitLemma.IsLat O K (J M) := by
    intro M hM
    refine ⟨hM.1.map _, ?_⟩
    have hcoe : ((J M : Submodule O A) : Set A) = (e.symm : (Fin n → K) →ₗ[K] A) '' (M : Set _) := by
      ext y; simp [J, Submodule.mem_map]; rfl
    rw [hcoe, Submodule.span_image, hM.2, Submodule.map_top, LinearEquiv.range]
  have stJ : ∀ M, (∀ v ∈ M, γ *ᵥ v ∈ M) →
      ∀ a ∈ integralClosure O A, ∀ y ∈ J M, a * y ∈ J M := by
    intro M hM a ha y hy
    have hint : IsIntegral O (a : Matrix (Fin n) (Fin n) K) :=
      (ha : IsIntegral O a).map (A.val.restrictScalars O)
    obtain ⟨p, hp⟩ := (memA _).1 a.2
    rw [← hp] at hint
    obtain ⟨r, hr⟩ := GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly n P₀ hcop γ hchar p hint
    rw [memJ] at hy ⊢
    change ((a : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K)) *ᵥ v₀ ∈ M
    rw [← Matrix.mulVec_mulVec, ← hp, hr]
    exact polyStable γ M hM r _ hy
  haveI : IsPrincipalIdealRing (integralClosure O A) :=
    GlobalTheory.UnitLemma.PrincipalLatDVR.isPrincipalIdealRing_integralClosure (E := K)
  set Λ : Submodule O A := Subalgebra.toSubmodule (integralClosure O A)

  have back : ∀ M (c : Aˣ), J M = GlobalTheory.UnitLemma.mulLat O (c : A) Λ →
      M = matLat O ((c : A) : Matrix (Fin n) (Fin n) K) (Λ.map (eO : A →ₗ[O] (Fin n → K))) := by
    intro M c hc
    ext v
    obtain ⟨y, rfl⟩ := hsurj v
    rw [mem_matLat]
    have h1 : φ y ∈ M ↔ y ∈ J M := by rw [memJ]; rfl
    rw [h1, hc]
    simp only [GlobalTheory.UnitLemma.mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨eO l, ⟨l, hl, rfl⟩, ?_⟩
      change ((c : A) : Matrix (Fin n) (Fin n) K) *ᵥ ((l : Matrix (Fin n) (Fin n) K) *ᵥ v₀) =
        (((c : A) * l : A) : Matrix (Fin n) (Fin n) K) *ᵥ v₀
      rw [Matrix.mulVec_mulVec]; rfl
    · rintro ⟨_, ⟨l, hl, rfl⟩, hv⟩
      refine ⟨l, hl, hinj ?_⟩
      rw [← hv]
      change (((c : A) * l : A) : Matrix (Fin n) (Fin n) K) *ᵥ v₀ =
        ((c : A) : Matrix (Fin n) (Fin n) K) *ᵥ ((l : Matrix (Fin n) (Fin n) K) *ᵥ v₀)
      rw [Matrix.mulVec_mulVec]; rfl
  obtain ⟨a₁, h₁⟩ :=
    GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_of_isPrincipalIdealRing (E := K) (J M₁) (latJ M₁ hL₁) (stJ M₁ hs₁)
  obtain ⟨a₂, h₂⟩ :=
    GlobalTheory.UnitLemma.PrincipalLat.eq_mulLat_of_isPrincipalIdealRing (E := K) (J M₂) (latJ M₂ hL₂) (stJ M₂ hs₂)
  obtain ⟨p, hp⟩ := (memA _).1 ((a₂ * a₁⁻¹ : Aˣ) : A).2
  refine ⟨p, ?_, ?_⟩
  · rw [hp]; exact (Units.isUnit (a₂ * a₁⁻¹)).map A.val
  · rw [back M₂ a₂ h₂, back M₁ a₁ h₁, ← matLat_mul, hp]
    congr 1
    change ((a₂ : A) : Matrix (Fin n) (Fin n) K) = (((a₂ * a₁⁻¹ : Aˣ) : A) * (a₁ : A) : A).1
    rw [← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.LatOrb.Stab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqOfStableLatticesStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_of_stable_lattices : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by
  first | exact @GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat | exact GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat | (intros; apply GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEq
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbGL

variable {K : Type} [Field K] (V : ValuationSubring K)

theorem mem_range_iff (x : K) : x ∈ (algebraMap V K).range ↔ x ∈ V := by
  constructor
  · rintro ⟨a, rfl⟩; exact a.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

theorem matLat_le_of_entries {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ V) :
    matLat V g (stdLat V n) ≤ stdLat V n := by
  intro v hv
  rw [mem_matLat] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [mem_stdLat] at hu ⊢
  intro i
  have hu' := fun j => (mem_range_iff V _).1 (hu j)
  apply (mem_range_iff V _).2
  simp only [Matrix.mulVec, dotProduct]
  exact V.toSubring.sum_mem fun j _ => V.toSubring.mul_mem (hg i j) (hu' j)

theorem entries_of_matLat_le {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : matLat V g (stdLat V n) ≤ stdLat V n) (i j : Fin n) : g i j ∈ V := by
  have hs : (Pi.single j (1 : K) : Fin n → K) ∈ stdLat V n := by
    rw [mem_stdLat]
    intro l
    rw [mem_range_iff]
    by_cases h : l = j
    · subst h; simp [V.one_mem]
    · simp [Pi.single_apply, h, V.zero_mem]
  have hm : g *ᵥ (Pi.single j (1 : K)) ∈ stdLat V n := hg ((mem_matLat _ _ _).2 ⟨_, hs, rfl⟩)
  rw [mem_stdLat] at hm
  have := (mem_range_iff V _).1 (hm i)
  simpa [Matrix.mulVec_single] using this

theorem matLat_mono {n : ℕ} (g : Matrix (Fin n) (Fin n) K) {M N : Submodule V (Fin n → K)}
    (h : M ≤ N) : matLat V g M ≤ matLat V g N := Submodule.map_mono h

end GlobalTheory.LatOrbGL


open GlobalTheory.LatOrbGL in
theorem GlobalTheory.LatOrb.mem_GLint_iff_matLat_std :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  intro K _ V n k
  constructor
  · rintro ⟨g, rfl⟩
    set k := Formalism.UG.bc V.toSubring.subtype g with hk
    have e1 : ∀ i j, k.val i j ∈ V := by
      intro i j; exact ((g : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    have e2 : ∀ i j, (k⁻¹).val i j ∈ V := by
      intro i j; rw [hk, ← map_inv]; exact (((g⁻¹ : GL (Fin n) V.toSubring) : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    apply le_antisymm (matLat_le_of_entries V _ e1)
    have : k.val * (k⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc stdLat V n = matLat V (k.val * (k⁻¹).val) (stdLat V n) := by rw [this, matLat_one]
      _ = _ := matLat_mul _ _ _
      _ ≤ _ := GlobalTheory.LatOrbGL.matLat_mono V _ (matLat_le_of_entries V _ e2)
  · intro h
    have e1 := entries_of_matLat_le V k.val h.le
    have h2 : matLat V (k⁻¹ : GL (Fin n) K).val (stdLat V n) = stdLat V n := by
      conv_lhs => rw [← h]
      rw [← matLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, matLat_one]
    have e2 := entries_of_matLat_le V (k⁻¹ : GL (Fin n) K).val h2.le
    let A : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨k.val i j, e1 i j⟩
    let B : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨(k⁻¹ : GL (Fin n) K).val i j, e2 i j⟩
    have hA : (RingHom.mapMatrix V.toSubring.subtype) A = k.val := by ext i j; rfl
    have hB : (RingHom.mapMatrix V.toSubring.subtype) B = (k⁻¹ : GL (Fin n) K).val := by ext i j; rfl
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) V.toSubring.subtype) := by
      intro X Y hXY; ext i j; exact congrFun (congrFun hXY i) j
    have hAB : A * B = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    have hBA : B * A = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEqStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq : ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  first | exact @GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | exact GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | (intros; apply GlobalTheory.LatOrb.mem_GLint_iff_matLat_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitary
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem herm_mulVec_right {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (y u : Fin n → K) :
    herm σ y (g *ᵥ u) = herm σ ((g.map σ)ᵀ *ᵥ y) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem selfDual_matLat_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K)
    (_hinv : ∀ x, σ (σ x) = x) (hO : ∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : (g.map σ)ᵀ * g = 1) :
    SelfDual O σ (matLat O g (stdLat O n)) := by
  have hg' : g * (g.map σ)ᵀ = 1 := mul_eq_one_comm.mp hg
  have hσO : ∀ z ∈ (algebraMap O K).range, σ z ∈ (algebraMap O K).range := by
    rintro z ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hO a
    exact ⟨b, hb.symm⟩
  intro y
  rw [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩ x hx
    rw [mem_matLat] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [herm_mulVec_right, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
    unfold herm
    refine Subring.sum_mem _ (fun k _ => Subring.mul_mem _ ((mem_stdLat u).mp hu k) (hσO _ ((mem_stdLat v).mp hv k)))
  · intro h
    refine ⟨(g.map σ)ᵀ *ᵥ y, ?_, by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]⟩
    rw [mem_stdLat]
    intro j
    have hx : g *ᵥ (Pi.single j 1 : Fin n → K) ∈ matLat O g (stdLat O n) := by
      rw [mem_matLat]
      refine ⟨Pi.single j 1, ?_, rfl⟩
      rw [mem_stdLat]
      intro i
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
    have := h _ hx
    rw [herm_mulVec_right] at this
    simpa [herm, Pi.single_apply, map_one] using this

end GlobalTheory.LatOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitaryStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDual_image_standardLattice_unitary : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K), (g.map σ)ᵀ * g = 1 →
    SelfDual O σ (matLat O g (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.selfDual_matLat_stdLat | exact GlobalTheory.LatOrb.selfDual_matLat_stdLat | (intros; apply GlobalTheory.LatOrb.selfDual_matLat_stdLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGL
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbIsLat

theorem single_mem_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (i : Fin n) :
    (Pi.single i (1 : K) : Fin n → K) ∈ stdLat O n := by
  rw [mem_stdLat]
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem stdLat_eq_span {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    stdLat O n = Submodule.span O (Set.range fun i : Fin n => (Pi.single i (1 : K) : Fin n → K)) := by
  apply le_antisymm
  · intro v hv
    rw [mem_stdLat] at hv
    choose a ha using hv
    have hv' : v = ∑ i, a i • (Pi.single i (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_stdLat n i

theorem stdLat_fg {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    (stdLat O n : Submodule O (Fin n → K)).FG := by
  rw [stdLat_eq_span]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.LatOrbIsLat

open GlobalTheory.LatOrbIsLat in
theorem GlobalTheory.LatOrb.matLat_stdLat_isLatV : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  intro O K _ _ _ n g
  refine ⟨(stdLat_fg n).map _, ?_⟩
  rw [eq_top_iff]
  intro v _
  set w : Fin n → K := (g⁻¹ : GL (Fin n) K).val *ᵥ v with hw
  have hgw : g.val *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hw' : w = ∑ i, w i • (Pi.single i (1 : K) : Fin n → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ i, w i • Matrix.mulVecLin g.val (Pi.single i (1 : K)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, ← hw']
    rw [Matrix.mulVecLin_apply, hgw]
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show _ ∈ matLat O g.val (stdLat O n)
  rw [mem_matLat]
  exact ⟨_, single_mem_stdLat n i, rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGLStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFullRankLattice_image_standardLattice_GL : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.matLat_stdLat_isLatV | exact GlobalTheory.LatOrb.matLat_stdLat_isLatV | (intros; apply GlobalTheory.LatOrb.matLat_stdLat_isLatV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixImageAdjointMulEqOfSelfDualLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixImageAdjointMulEqOfSelfDualLattices
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem herm_mulVec_eq_adj {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (y m : Fin n → K) :
    herm σ y (x *ᵥ m) = herm σ ((x.map σ)ᵀ *ᵥ y) m := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem matLat_adj_mul_eq_of_selfDual : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  intro O K _ _ _ σ _ n x hx M hM hxM

  have key : ∀ y, y ∈ matLat O x M ↔ (x.map σ)ᵀ *ᵥ y ∈ M := by
    intro y
    rw [hxM y, hM ((x.map σ)ᵀ *ᵥ y)]
    constructor
    · intro h m hm
      rw [← herm_mulVec_eq_adj]
      exact h _ ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
    · intro h w hw
      obtain ⟨m, hm, rfl⟩ := (mem_matLat x M w).1 hw
      rw [herm_mulVec_eq_adj]
      exact h m hm
  have hdet : IsUnit ((x.map σ)ᵀ * x).det := by
    have e : (x.map σ).det = σ x.det := (RingHom.map_det σ x).symm
    rw [Matrix.det_mul, Matrix.det_transpose, e]
    refine IsUnit.mul ?_ ((Matrix.isUnit_iff_isUnit_det x).1 hx)
    have h0 : x.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det x).1 hx).ne_zero
    exact isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 h0)
  ext u
  rw [mem_matLat]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [← Matrix.mulVec_mulVec]
    exact (key _).1 ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
  · intro hu
    set A := (x.map σ)ᵀ * x with hA
    refine ⟨A⁻¹ *ᵥ u, ?_, ?_⟩
    · have h1 : (x.map σ)ᵀ *ᵥ (x *ᵥ (A⁻¹ *ᵥ u)) ∈ M := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hA,
          Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
        exact hu
      obtain ⟨m', hm', hxm'⟩ := (mem_matLat x M _).1 ((key _).2 h1)
      have : m' = A⁻¹ *ᵥ u := by
        have hx' : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hx
        have := congrArg (fun v => x⁻¹ *ᵥ v) hxm'
        simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hx'] using this
      exact this ▸ hm'
    · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]

end GlobalTheory.LatOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixImageAdjointMulEqOfSelfDualLatticesStatement
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  first | exact @GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | exact GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | (intros; apply GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCoset
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.OrbitT

open GlobalTheory.LatOrb

theorem stable_of_conj {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (g : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K)
    (h : matLat O ((g⁻¹ : GL (Fin n) K).val * γ * g.val) (stdLat O n) = stdLat O n) :
    ∀ v ∈ matLat O g.val (stdLat O n), γ *ᵥ v ∈ matLat O g.val (stdLat O n) := by
  intro v hv
  have e : γ * g.val = g.val * ((g⁻¹ : GL (Fin n) K).val * γ * g.val) := by
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : matLat O γ (matLat O g.val (stdLat O n)) = matLat O g.val (stdLat O n) := by
    rw [← matLat_mul, e, matLat_mul, h]
  rw [← h2]
  exact (mem_matLat _ _ _).2 ⟨v, hv, rfl⟩

theorem orbit_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  intro E _ _ _ n w hcc hcv P₀ hcop γ hγ g₁ g₂ h₁ h₂
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  have hσO : ∀ a : w.adicCompletionIntegers E, ∃ b : w.adicCompletionIntegers E,
      cj w (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a) =
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) b := by
    intro a
    refine ⟨⟨cj w a, ?_⟩, rfl⟩
    have ha := a.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hcv]; exact ha
  have hK : ∀ h : UL n w, h ∈ KL n w ↔ matLat (w.adicCompletionIntegers E) h.1.val
      (stdLat (w.adicCompletionIntegers E) n) = stdLat (w.adicCompletionIntegers E) n := by
    intro h
    exact (Subgroup.mem_subgroupOf).trans (GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq (w.adicCompletionIntegers E) n h.1)
  have st : ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w → ∀ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n), γ.1.val *ᵥ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n) := by
    intro g hg
    have h := (hK _).1 hg
    have e : ((g⁻¹ * γ * g : UL n w).1.val) = (g.1⁻¹ : GLw n w).val * γ.1.val * g.1.val := by simp
    rw [e] at h
    exact stable_of_conj g.1 γ.1.val h
  obtain ⟨t, htU, htc, htM⟩ : ∃ t : GLw n w, t ∈ UL n w ∧ t * γ.1 = γ.1 * t ∧
      matLat (w.adicCompletionIntegers E) t.val (matLat (w.adicCompletionIntegers E) g₁.1.val
        (stdLat (w.adicCompletionIntegers E) n)) = matLat (w.adicCompletionIntegers E) g₂.1.val
        (stdLat (w.adicCompletionIntegers E) n) := by
    obtain ⟨p, hpu, hp⟩ := GlobalTheory.T.exists_unit_eq_of_stable_lattices n P₀ hcop γ.1.val hγ _ _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1) (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₂.1) (st g₁ h₁) (st g₂ h₂)
    by_cases hs : IsSplitAt w
    · refine ⟨hpu.unit, by simp [UL, hs], ?_, hp.symm⟩
      ext : 1
      simp only [Units.val_mul, IsUnit.unit_spec]
      have e1 : aeval γ.1.val p * γ.1.val = aeval γ.1.val (p * X) := by rw [map_mul, aeval_X]
      have e2 : γ.1.val * aeval γ.1.val p = aeval γ.1.val (X * p) := by rw [map_mul, aeval_X]
      rw [e1, e2, mul_comm]
    · have hUL : ∀ h : UL n w, ((h.1.val).map (cj w))ᵀ * h.1.val = 1 := by
        intro h
        have := h.2
        simp only [UL, hs, if_false] at this
        simpa [UJ, cT] using this
      have sd : ∀ g : UL n w, SelfDual (w.adicCompletionIntegers E) (cj w)
          (matLat (w.adicCompletionIntegers E) g.1.val (stdLat (w.adicCompletionIntegers E) n)) :=
        fun g => GlobalTheory.T.isSelfDual_image_standardLattice_unitary (cj w) hcc hσO n _ (hUL g)
      have hc := GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices (cj w) hcc n (aeval γ.1.val p) hpu _ (sd g₁) (hp ▸ sd g₂)
      obtain ⟨t, ht1, htc, htM⟩ := GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq n P₀ hcop γ.1.val hγ (cj w) hcc hσO (hUL γ) _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1)
        (st g₁ h₁) p hpu hc
      have htu : IsUnit t := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse ht1)
      refine ⟨htu.unit, ?_, ?_, by rw [hp]; exact htM⟩
      · show _ ∈ UL n w
        simp only [UL, hs, if_false]
        show cT (cj w) _ * 1 * _ = 1
        simpa [cT] using ht1
      · ext : 1
        simpa using htc
  refine ⟨⟨t, htU⟩, ?_, (⟨t, htU⟩ * g₁)⁻¹ * g₂, ?_, by group⟩
  · show (⟨t, htU⟩ : UL n w) * γ = γ * (⟨t, htU⟩ : UL n w)
    exact Subtype.ext htc
  · rw [hK]
    have e : (((⟨t, htU⟩ : UL n w) * g₁)⁻¹ * g₂ : UL n w).1.val =
        (g₁.1⁻¹ : GLw n w).val * ((t⁻¹ : GLw n w).val * g₂.1.val) := by simp [mul_assoc]
    rw [e, matLat_mul, matLat_mul, ← htM, ← matLat_mul (a := ((t⁻¹ : GLw n w).val)), Units.inv_mul, matLat_one,
      ← matLat_mul, Units.inv_mul, matLat_one]

end GlobalTheory.BCT.OrbitT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCosetStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  exact @GlobalTheory.BCT.OrbitT.orbit_main
end
