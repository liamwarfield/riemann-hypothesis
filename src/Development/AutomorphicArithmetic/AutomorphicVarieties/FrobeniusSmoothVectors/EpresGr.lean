module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OrdOfFlag

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def pq (a : Fin 3) : ZMod 2 := ((w 3 a : ℤ) : ZMod 2)

theorem pw_eq (a b : Fin 3) : pw a b = pq a - pq b := Int.cast_sub _ _

def GrM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (α β : Fin 3 → ZMod 2)
    (M : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, M a b ∈ evp σ (α a - β b)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

namespace Box

structure Gr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (B : Box F 3 R) (σ : R →ₐ[O] R)
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ pq pq (B.r s).mat
  g : ∀ v, GrM σ (π v) pq (B.g v : Matrix (Fin 3) (Fin 3) R)

variable {K : Type} [CommRing K]

structure Ev (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, (B.r s).mat ∈ adp K 0
  g : ∀ v a b, π v a ≠ pq b → (B.g v : Matrix (Fin 3) (Fin 3) K) a b = 0
  stab : ∀ j s, adp K j ≤ (adp K j).comap (B.ad s)

variable {B : Box F 3 K} {π : F.V → Fin 3 → ZMod 2}

def Ev.ad (h : B.Ev π) (j : ZMod 2) : Representation K F.Γ (adp K j) := B.ad.subrepresentation (adp K j) (h.stab j)

@[simp] theorem Ev.ad_apply (h : B.Ev π) (j : ZMod 2) (s : F.Γ) (X : adp K j) :
    ((h.ad j s X : adp K j) : Matrix (Fin 3) (Fin 3) K) = B.ad s X := rfl


variable (B) in
def bp (j : ZMod 2) (v : F.V) : Submodule K (adp K j) := (B.b v).comap (adp K j).subtype

end Box

section CO

variable {O : Type} [CommRing O] [IsLocalRing O] {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C]
  [Algebra O C]

structure SetLift.Gr {p : C' →ₐ[O] C} {B : Box F 3 C} (D : SetLift p B) (σ' : C' →ₐ[O] C')
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ' pq pq (D.r s : Matrix (Fin 3) (Fin 3) C')
  g : ∀ v, GrM σ' (π v) pq (D.g v : Matrix (Fin 3) (Fin 3) C')
  t : ∀ v s, GrM σ' (π v) (π v) (D.t v s : Matrix (Fin 3) (Fin 3) C')

def formp (σ' : C' →ₐ[O] C') (K : Ideal C') (j : ZMod 2) :
    Submodule (ResidueField O) (K →ₗ[O] ResidueField O) where
  carrier := {u | ∀ i, i ≠ j → ∀ y : K, (y : C') ∈ evp σ' i → u y = 0}
  add_mem' h h' i e y hy := by simp [h i e y hy, h' i e y hy]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c u h i e y hy := by simp [h i e y hy]


variable (O) in
def HasObsG {R : Type} [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) (H : Type) [AddCommGroup H]
    [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (σ' : C' →ₐ[O] C'), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ → (∀ y, σ' (σ' y) = y) → (∀ y, p (σ' y) = σ (p y)) →
    ∃ ob : formp σ' (RingHom.ker p) j →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u.1 y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

end CO

end UpperTheory.V.Fr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

namespace Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (Q : Type) [CommRing Q] [Algebra k Q]

structure Low (y a : F.G0 → Q) : Prop where
  lcy : IsLocallyConstant y
  lca : IsLocallyConstant a
  muly : ∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h
  mula : ∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + y (F.star g) * y h + (((F.Ψ g)⁻¹ : kˣ) : k) • a h
  pol : ∀ g, a (F.star g) = a g
  nor : y F.g0 = y (F.star F.g0)
  loc : ∀ v, ∃ α β γ : Q, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α ∧
    y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β ∧
    a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ -
      (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • (α * β)

variable {F Q} {Q' : Type} [CommRing Q'] [Algebra k Q'] {y a : F.G0 → Q}

theorem Low.map (h : F.Low Q y a) (φ : Q →ₐ[k] Q') : F.Low Q' (fun g => φ (y g)) (fun g => φ (a g)) := by
  refine
    { lcy := h.lcy.comp φ
      lca := h.lca.comp φ
      muly g g' := by simp only [h.muly, map_add (f := _), map_smul]
      mula g g' := by simp only [h.mula, map_add (f := _), map_smul, map_mul]
      pol g := by simp only [h.pol]
      nor := congrArg φ h.nor
      loc := ?_ }
  intro v
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨φ α, φ β, φ γ, fun s => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H s
  exact ⟨by rw [h1, map_smul], by rw [h2, map_smul], by rw [h3, map_sub, map_smul, map_smul, map_mul]⟩

theorem Low.comb (h : F.Low Q y a) (t : Q) {b : F.G0 → Q} (hb : b ∈ F.strS Q) :
    F.Low Q (fun g => t * y g) (fun g => t ^ 2 * a g + b g) := by
  refine
    { lcy := h.lcy.comp (t * ·)
      lca := (h.lca.comp (t ^ 2 * ·)).add hb.1
      muly g g' := by simp only [h.muly, Algebra.smul_def]; ring
      mula g g' := by simp only [h.mula, hb.2.1 g g', Algebra.smul_def]; ring
      pol g := by simp only [h.pol, hb.2.2.1 g]
      nor := congrArg (t * ·) h.nor
      loc := ?_ }
  intro v
  obtain ⟨α, β, γ, H⟩ := h.loc v
  obtain ⟨δ, H'⟩ := hb.2.2.2 v
  refine ⟨t * α, t * β, t ^ 2 * γ + δ, fun s => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H s
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; simp only [Algebra.smul_def]; ring
  · rw [h2]; simp only [Algebra.smul_def]; ring
  · rw [h3, H' s]; simp only [Algebra.smul_def]; ring

theorem Low.zero : F.Low Q 0 0 :=
  ⟨IsLocallyConstant.const 0, IsLocallyConstant.const 0, by simp, by simp, fun _ => rfl, rfl,
    fun _ => ⟨0, 0, 0, by simp⟩⟩

theorem Low.strS (h : F.Low Q 0 a) : a ∈ F.strS Q := by
  refine ⟨h.lca, fun g g' => by simpa using h.mula g g', h.pol, fun v => ?_⟩
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨γ, fun s => ?_⟩
  obtain ⟨-, h2, h3⟩ := H s
  rw [h3, mul_comm α, ← smul_mul_assoc, ← h2]
  simp

theorem strS_mul (t : Q) (ha : a ∈ F.strS Q) : (fun g => t * a g) ∈ F.strS Q :=
  strS_map (LinearMap.mulLeft k t) ha

end Frame

namespace Space

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}
  {Q Q' : Type} [CommRing Q] [Algebra (ResidueField O) Q] [CommRing Q'] [Algebra (ResidueField O) Q']

structure FPt (S : Space O F n) (ξ : S.A →+* Q) : Prop where
  x0 : S.x0 ≤ RingHom.ker ξ
  alg : ∀ c : O, ξ (algebraMap O S.A c) = algebraMap (ResidueField O) Q (residue O c)

theorem FPt.comp {S : Space O F n} {ξ : S.A →+* Q} (h : S.FPt ξ) (φ : Q →ₐ[ResidueField O] Q') :
    S.FPt ((φ : Q →+* Q').comp ξ) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have : ξ x = 0 := h.x0 hx
    show φ (ξ x) = 0
    rw [this, map_zero]
  · intro c
    show φ (ξ _) = _
    rw [h.alg, AlgHom.commutes]

structure At (S : Space O F 3) (ξ : S.A →+* Q) (y a : F.G0 → Q) : Prop where
  fpt : S.FPt ξ
  low : S.u.triM ≤ RingHom.ker ξ
  hy : ∀ g, ξ (S.u.r g 1 0) = y g
  ha : ∀ g, ξ (S.u.r g 2 0) = a g

theorem At.comp {S : Space O F 3} {ξ : S.A →+* Q} {y a : F.G0 → Q} (h : S.At ξ y a) (φ : Q →ₐ[ResidueField O] Q') :
    S.At ((φ : Q →+* Q').comp ξ) (fun g => φ (y g)) (fun g => φ (a g)) := by
  refine ⟨h.fpt.comp φ, ?_, fun g => congrArg φ (h.hy g), fun g => congrArg φ (h.ha g)⟩
  intro x hx
  have : ξ x = 0 := h.low hx
  show φ (ξ x) = 0
  rw [this, map_zero]

end Space

end UpperTheory.V.Fr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zpow_w_ne' {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ w n i ≠ a ^ w n j := by
  have h1 : a ≠ 1 := fun h => ha (by rw [h, one_pow])
  have h2 : a ≠ a⁻¹ := fun h => ha (by rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel a)
  have h3 : (1 : kˣ) ≠ a⁻¹ := fun h => h1 (by rw [← inv_inv a, ← h, inv_one])
  rcases hn with rfl | rfl
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]
  · fin_cases i <;> fin_cases j <;> simp_all [UpperTheory.V.Fr.w] <;> simp_all [eq_comm]

private theorem residue_eq {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x y : R} (h : res O R x = res O R y) : residue R x = residue R y := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← res_eq_zero_iff O R, map_sub, h, sub_self]

private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : UpperTheory.V.W.HasFlag r.toHomUnits κ) (s : H) :
    (r s).charpoly = ∏ i, (Polynomial.X - Polynomial.C (κ i s : k)) := by
  obtain ⟨g, hg⟩ := h
  have e : ((g * r.toHomUnits s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = (g : Matrix (Fin n) (Fin n) k) * r s * (g : Matrix (Fin n) (Fin n) k)⁻¹ := by
    simp [Matrix.coe_units_inv]
  have hc := Matrix.charpoly_units_conj g (r s)
  rw [← hc, ← e, Matrix.charpoly_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [(hg s).2 i]
  · intro i j hij
    exact (hg s).1 i j hij

theorem UpperTheory.V.Fr.o1 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ v g, (S.u.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (S.u.ψ v i g : S.A)) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S v g
  obtain ⟨g₀, hg⟩ := hF.f3 v
  have h4 : ∀ i, res O S.R (S.ρ.ψ v i g₀) = ((F.Ψ (F.loc v g₀) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun i => S.lift.2.1.2 v i g₀
  have hfl : UpperTheory.V.W.HasFlag (S.ρ.r.comp (F.loc0 v)).toHomUnits (S.ρ.ψ v) := by
    refine flag_loc _ _ g₀ (fun i j hij => ?_) ?_ (fun s => S.ρ.ord v s)
    · by_contra hu
      have h2 : (S.ρ.ψ v i g₀ : S.R) - S.ρ.ψ v j g₀ ∈ maximalIdeal S.R := hu
      have h3 := (res_eq_zero_iff O S.R _).2 h2
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact zpow_w_ne' hn _ hg i j hij (Units.ext h3)
    · have hd : ((S.ρ.r.comp (F.loc0 v)) g₀).map (residue S.R) =
          Matrix.diagonal fun i => residue S.R (S.ρ.ψ v i g₀) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          refine residue_eq (O := O) ?_
          rw [h4]
          exact S.lift.2.1.1 (F.loc0 v g₀) i
        · rw [Matrix.diagonal_apply_ne _ hij, ← map_zero (residue S.R)]
          refine residue_eq (O := O) ?_
          rw [map_zero]
          exact S.lift.2.2 (F.loc0 v g₀) i j hij
      rw [hd, Matrix.charpoly_diagonal]
  have h := charpoly_flag' _ _ hfl g
  refine Polynomial.map_injective (S.A.val : S.A →+* S.R) Subtype.val_injective ?_
  rw [← Matrix.charpoly_map, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section LC

variable {T A C : Type} [TopologicalSpace T] [CommRing A] [CommRing C] {n : ℕ}

private theorem lc_matrix {B : Type} {f : T → Matrix (Fin n) (Fin n) B}
    (h : ∀ a b, IsLocallyConstant fun s => f s a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hall : ∀ᶠ y in nhds x, ∀ a b, f y a b = f x a b :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
      (IsLocallyConstant.iff_eventually_eq _).1 (h a b) x
  filter_upwards [hall] with y hy
  ext a b
  exact hy a b

private theorem lc_gl {I : Ideal A} {f : T → GL (Fin n) A} (h : ∀ a b, AdicCont I fun s => f s a b) (N : ℕ) :
    IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s) := by
  apply IsLocallyConstant.desc _ (fun u : GL (Fin n) (A ⧸ I ^ N) => (u : Matrix (Fin n) (Fin n) (A ⧸ I ^ N)))
  · apply lc_matrix
    intro a b
    simpa [Function.comp_def] using h a b N
  · exact fun u v huv => Units.ext huv

private theorem mem_ker (p : A →+* C) {u : GL (Fin n) A} (h : GeneralLinearGroup.map p u = 1) (i j : Fin n) :
    ((u : Matrix (Fin n) (Fin n) A) - 1) i j ∈ RingHom.ker p := by
  rw [RingHom.mem_ker]
  have he := congrArg (fun v : GL (Fin n) C => (v : Matrix (Fin n) (Fin n) C) i j) h
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at he
  rw [Matrix.sub_apply, map_sub, he, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem lc_ker [IsNoetherianRing A] {I K : Ideal A} (hs : I * K = ⊥) {f : T → GL (Fin n) A}
    (hf : ∀ s a b, ((f s : Matrix (Fin n) (Fin n) A) - 1) a b ∈ K)
    (h : ∀ N, IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s)) :
    IsLocallyConstant fun s => (f s : Matrix (Fin n) (Fin n) A) - 1 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (K : Submodule A A)
  have h0 : ∀ x ∈ I ^ (k + 1), x ∈ K → x = 0 := by
    intro x hxm hxK
    have hx : x ∈ I ^ (k + 1) • (⊤ : Submodule A A) ⊓ (K : Submodule A A) := by
      refine ⟨?_, hxK⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hxm
    rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
    have hle : I • (I ^ k • (⊤ : Submodule A A) ⊓ (K : Submodule A A)) ≤ I • (K : Submodule A A) :=
      Submodule.smul_mono le_rfl inf_le_right
    have hx' := hle hx
    rw [Ideal.smul_eq_mul, hs] at hx'
    exact (Submodule.mem_bot A).1 hx'
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (h (k + 1)) s] with s' hs'
  ext a b
  have he := congrArg
    (fun v : GL (Fin n) (A ⧸ I ^ (k + 1)) => (v : Matrix (Fin n) (Fin n) (A ⧸ I ^ (k + 1))) a b) hs'
  simp only [GeneralLinearGroup.map_apply] at he
  have hd := Ideal.Quotient.eq.1 he
  have hK : (f s' : Matrix (Fin n) (Fin n) A) a b - (f s : Matrix (Fin n) (Fin n) A) a b ∈ K := by
    have := sub_mem (hf s' a b) (hf s a b)
    simpa [Matrix.sub_apply] using this
  rw [Matrix.sub_apply, Matrix.sub_apply, sub_eq_zero.1 (h0 _ hd hK)]

private theorem map_sgn (f : A →+* C) (s : ℤˣ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (sgnAct n A s g) = sgnAct n C s (GeneralLinearGroup.map f g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · simp
  · simpa using map_theta f g

private theorem lc_hom {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : ∀ᶠ z in nhds (1 : G), z ∈ (φ.ker : Set G) := h.mem_nhds (one_mem _)
  have hc : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have := (continuous_const_mul x⁻¹).tendsto x
    rwa [inv_mul_cancel] at this
  filter_upwards [hc.eventually h1] with y hy
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy
  exact hy.symm

end LC

theorem UpperTheory.V.Fr.pr_omk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B), maximalIdeal C' * RingHom.ker p = ⊥ → (∀ x i j, D.om x i j ∈ RingHom.ker p) ∧ (∀ v s i j, D.a v s i j ∈ RingHom.ker p) ∧ IsLocallyConstant D.om ∧ ∀ v, IsLocallyConstant (D.a v) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D hker
  have hgrp : ∀ s t, (B.r (s * t)).left = (B.r s).left * sgnAct n C (F.del s) (B.r t).left := by
    intro s t
    rw [map_mul, SemidirectProduct.mul_left, B.nu]
  have hom1 : ∀ x : F.Γ × F.Γ, GeneralLinearGroup.map (p : C' →+* C)
      (D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹) = 1 := by
    intro x
    rw [map_mul, map_mul, map_inv, map_sgn, D.r_map, D.r_map, D.r_map, hgrp, mul_inv_cancel]
  have ha1 : ∀ v s, GeneralLinearGroup.map (p : C' →+* C)
      (D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹) = 1 := by
    intro v s
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, D.r_map, D.g_map, D.t_map]
    group
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  have hrc : ∀ N, IsLocallyConstant fun s : F.Γ =>
      GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.r s) :=
    fun N => lc_gl (fun a b => D.r_cont a b) N
  have hdel : IsLocallyConstant F.del := lc_hom F.del hF.del_open
  refine ⟨fun x i j => mem_ker _ (hom1 x) i j, fun v s i j => mem_ker _ (ha1 v s) i j, ?_, ?_⟩
  · have := lc_ker hker
      (f := fun x : F.Γ × F.Γ => D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹)
      (fun x a b => mem_ker _ (hom1 x) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have e2 := (hrc N).comp_continuous (continuous_snd (X := F.Γ) (Y := F.Γ))
        have e3 := (hrc N).comp_continuous (continuous_mul (M := F.Γ))
        have e4 := hdel.comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have := IsLocallyConstant.comp₂
          (IsLocallyConstant.comp₂ e1 (IsLocallyConstant.comp₂ e4 e2
            fun s g => sgnAct n _ s g) (· * ·)) e3 (fun a b => a * b⁻¹)
        convert this using 1
        funext x
        simp [Function.comp, map_sgn])
    exact this
  · intro v
    have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
    have := lc_ker hker
      (f := fun s : F.Gv v => D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹)
      (fun s a b => mem_ker _ (ha1 v s) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous hloc
        have e2 := lc_gl (fun a b => D.t_cont v a b) N
        have := IsLocallyConstant.comp₂ e1 e2 (fun a b => a *
          ((GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹ * b *
            GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹)
        convert this using 1
        funext s
        simp [Function.comp])
    exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_open :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R), B.Cont (maximalIdeal R) → IsOpen ((B.bar O).r.ker : Set F.Γ) ∧ IsOpen ((B.bar O).ad.ker : Set F.Γ) ∧ IsLocallyConstant fun s => ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ B hB
  have hent : ∀ i j, IsLocallyConstant fun s => ((B.bar O).r s).mat i j := fun i j => by
    have hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0 := fun a ha => by
      rw [pow_one] at ha
      exact (res_eq_zero_iff O R a).2 ha
    exact (hB i j 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)
  have hmat : IsLocallyConstant fun s => ((B.bar O).r s).mat := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h : ∀ᶠ y in nhds x, ∀ i j, ((B.bar O).r y).mat i j = ((B.bar O).r x).mat i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hent i j).eventually_eq x
    exact h.mono fun y hy => Matrix.ext hy
  have hr : IsOpen ((B.bar O).r.ker : Set F.Γ) := by
    have e : ((B.bar O).r.ker : Set F.Γ) =
        {s | ((B.bar O).r s).mat = 1} ∩ (F.del.ker : Set F.Γ) := by
      ext s
      constructor
      · intro hs
        have hs' : (B.bar O).r s = 1 := hs
        refine ⟨?_, ?_⟩
        · show ((B.bar O).r s).mat = 1
          rw [hs']
          rfl
        · show F.del s = 1
          rw [← (B.bar O).nu s, hs']
          rfl
      · rintro ⟨h1, h2⟩
        show (B.bar O).r s = 1
        refine SemidirectProduct.ext (Units.ext h1) ?_
        rw [(B.bar O).nu s]
        exact h2
    rw [e]
    exact (hmat.isOpen_fiber 1).inter hF.del_open
  refine ⟨hr, Subgroup.isOpen_mono (fun s hs => ?_) hr, hmat⟩
  have hs' : (B.bar O).r s = 1 := hs
  show GG.ad n (ResidueField O) ((B.bar O).r s) = 1
  rw [hs', map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOfbox
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def diagHom {H C : Type} [Group H] [CommRing C] {n : ℕ} (m : H →* Matrix (Fin n) (Fin n) C)
    (h : ∀ s, UpT (m s)) (i : Fin n) : H →* C where
  toFun s := m s i i
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [h s i b h', zero_mul]
      · rw [h t b i h', mul_zero]
    · simp

private def conjHom {H R : Type} [Group H] [Monoid R] (u : Rˣ) (m : H →* R) : H →* R where
  toFun s := (u : R) * m s * ((u⁻¹ : Rˣ) : R)
  map_one' := by simp
  map_mul' s t := by simp [mul_assoc]

private theorem cont_conj {X C : Type} [TopologicalSpace X] [CommRing C] {n : ℕ} (I : Ideal C)
    (m : X → Matrix (Fin n) (Fin n) C) (hm : ∀ i j, AdicCont I fun s => m s i j) (a b : Matrix (Fin n) (Fin n) C)
    (i j : Fin n) : AdicCont I fun s => (a * m s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * m s * b) i j)) = ∑ q, ∑ p, fun s => Ideal.Quotient.mk (I ^ N) (a i p) * Ideal.Quotient.mk (I ^ N) (m s p q) * Ideal.Quotient.mk (I ^ N) (b q j) := by
    funext s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun q _ => ?_)
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun p _ => ?_)
  exact ((IsLocallyConstant.const _).mul (hm p q N)).mul (IsLocallyConstant.const _)

theorem UpperTheory.V.Fr.pr_ofbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (B : Box F n C), (B.r F.c).mat = 1 → (∀ i j, i ≠ j → ((B.r F.g0).mat - (B.r (F.star F.g0)).mat) i j = 0) → B.Cont I → ∃ ρ : NRep F n C, B.Of ρ ∧ ρ.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I B hc hdg hcont
  let rr : F.G0 →* Matrix (Fin n) (Fin n) C := (Units.coeHom _).comp (glPart F.del B.r B.nu)
  let m : ∀ v, F.Gv v →* Matrix (Fin n) (Fin n) C := fun v => conjHom (B.g v) (rr.comp (F.loc0 v))
  have hup : ∀ v s, UpT (m v s) := fun v s => B.tri v s
  let ψ : (v : F.V) → Fin n → F.Gv v →* Cˣ := fun v i => (diagHom (m v) (hup v) i).toHomUnits
  have hpol : ∀ g : F.G0, rr (F.star g) = Jmat (R := C) n * (rr g)ᵀ * Jmat (R := C) n := by
    intro g
    have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
    have hs : ((F.star g : F.G0) : F.Γ) = F.c * (↑g)⁻¹ * F.c := by
      show ((F.conj g⁻¹ : F.G0) : F.Γ) = _
      rw [Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hcc]
      rfl
    have hPl : (B.r F.c).left = 1 := Units.ext hc
    have hPr : (B.r F.c).right = -1 := by rw [B.nu, hF.del_c]
    have hX : (B.r (↑g)⁻¹).left = (glPart F.del B.r B.nu g)⁻¹ := by
      rw [← map_inv]
      rfl
    show ((B.r ↑(F.star g)).left : Matrix (Fin n) (Fin n) C) = _
    rw [hs, map_mul, map_mul, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    simp only [hPl, hPr, map_one, mul_one, one_mul, sgnAct_neg_one, hX, theta_val, inv_inv]
    rfl
  have hord : ∀ v (g : Fin n → F.Gv v), ordProd (fun s => rr (F.loc0 v s)) (fun i s => ((ψ v i s : Cˣ) : C)) g = 0 := by
    intro v g
    have hf : UpperTheory.V.W.HasFlag (rr.comp (F.loc0 v)).toHomUnits (ψ v) := ⟨B.g v, fun s => ⟨fun i j hij => hup v s i j hij, fun i => rfl⟩⟩
    exact (ord_of_flag (rr.comp (F.loc0 v)) (ψ v) hf).1 g
  refine ⟨⟨rr, ψ, hpol, fun i j hij => hdg i j hij, hord⟩, ⟨hc, fun s => rfl, fun v i s => rfl⟩, ?_, ?_⟩
  · intro i j N
    exact (hcont i j N).comp_continuous continuous_subtype_val
  · intro v i
    exact cont_conj I (fun s => (B.r (F.loc v s)).mat) (fun p q N => (hcont p q N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))) ↑(B.g v) ↑(B.g v)⁻¹ i i
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgTwist
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_rev (n : ℕ) (i : Fin n) : w n i.rev = - w n i := by
  have := i.isLt
  simp only [w, Fin.val_rev]
  split_ifs <;> omega

private theorem J_apply {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Xᵀ * Jmat (R := K) n) i j = X j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : ∀ k : Fin n, (j = k.rev) ↔ (k = j.rev) := by
    intro k
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def tw {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun X := Matrix.of fun i j => ((u ^ (w n i - w n j) : Kˣ) : K) * X i j
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  map_mul' X Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : w n i - w n j = (w n i - w n a) + (w n a - w n j) := by ring
    rw [this, _root_.zpow_add, Units.val_mul]
    ring
  map_zero' := by ext i j; simp
  map_add' X Y := by ext i j; simp [mul_add]
  commutes' c := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]

private theorem tw_apply {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    tw n u X i j = ((u ^ (w n i - w n j) : Kˣ) : K) * X i j := rfl

private theorem ordProd_tw {H K : Type} [CommRing K] {n : ℕ} (u : Kˣ)
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => tw n u (r s)) ψ g = tw n u (ordProd r ψ g) := by
  unfold ordProd
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp

theorem UpperTheory.V.Fr.alg_twist :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {K : Type} [CommRing K] (u : Kˣ) (ρ : NRep F n K), ∃ ρ' : NRep F n K, (∀ g i j, ρ'.r g i j = ((u ^ (w n i - w n j) : Kˣ) : K) * ρ.r g i j) ∧ ρ'.ψ = ρ.ψ := by
  intro l _ k _ F n K _ u ρ
  refine ⟨⟨(tw n u).toRingHom.toMonoidHom.comp ρ.r, ρ.ψ, ?_, ?_, ?_⟩, fun g i j => rfl, rfl⟩
  · intro g
    ext i j
    rw [J_apply]
    show tw n u (ρ.r (F.star g)) i j = tw n u (ρ.r g) j.rev i.rev
    rw [tw_apply, tw_apply, ρ.pol, J_apply, w_rev, w_rev]
    congr 3
    ring
  · intro i j h
    have := ρ.diag i j h
    rw [Matrix.sub_apply] at this ⊢
    show tw n u (ρ.r F.g0) i j - tw n u (ρ.r (F.star F.g0)) i j = 0
    rw [tw_apply, tw_apply, ← mul_sub, this, mul_zero]
  · intro v g
    have := ordProd_tw u (fun s => ρ.r (F.loc0 v s)) (fun i s => ((ρ.ψ v i s : Kˣ) : K)) g
    exact this.trans (by rw [ρ.ord, map_zero])
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSqz
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (μ : ResidueField O →+ C), IsSq O μ → ∃ e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C, (∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ) ∧ (∀ X Y, e (X + Y) = e X * e Y) ∧ (∀ X, (e X)⁻¹ = e (-X)) ∧ (∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)), A * X.map μ = (A.map (res O C) * X).map μ ∧ X.map μ * A = (X * A.map (res O C)).map μ) ∧ ∀ (x : GG (m := n) (R := C)) (X : Matrix (Fin n) (Fin n) (ResidueField O)), x * GG.ofGL (e X) = GG.ofGL (e ((GG.map (res O C : C →+* ResidueField O) x).adFun X)) * x := by
  intro O _ _ C _ _ _ n μ hμ
  have hsq : ∀ c d, μ c * μ d = 0 := by
    intro c d
    have h := hμ.mul (μ c) d
    rw [(res_eq_zero_iff O C _).2 (hμ.mem c), zero_mul, map_zero] at h
    exact h.symm
  have hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      A * X.map μ = (A.map (res O C) * X).map μ := by
    intro A X
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hμ.mul]
  have hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      X.map μ * A = (X * A.map (res O C)).map μ := by
    intro A X
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (X i k), hμ.mul, mul_comm]
  have hsqM : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), X.map μ * Y.map μ = 0 := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply, hsq]
  have hadd : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), (X + Y).map μ = X.map μ + Y.map μ := by
    intro X Y
    ext i j
    simp
  have hzero : (0 : Matrix (Fin n) (Fin n) (ResidueField O)).map μ = 0 := by
    ext i j
    simp
  have hu : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O),
      (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ := by
    intro X Y
    rw [hadd, show (1 + X.map μ) * (1 + Y.map μ) = 1 + (X.map μ + Y.map μ) + X.map μ * Y.map μ by
      noncomm_ring, hsqM, add_zero]
  let e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C := fun X =>
    ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hu, add_neg_cancel, hzero, add_zero],
      by rw [hu, neg_add_cancel, hzero, add_zero]⟩
  have he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ := fun X => rfl
  have hemul : ∀ X Y, e (X + Y) = e X * e Y := by
    intro X Y
    apply Units.ext
    rw [Units.val_mul, he, he, he, hu]
  have heinv : ∀ X, (e X)⁻¹ = e (-X) := fun X => Units.ext rfl
  have hconj : ∀ (g : GL (Fin n) C) (h : GL (Fin n) (ResidueField O))
      (Y : Matrix (Fin n) (Fin n) (ResidueField O)),
      (g : Matrix (Fin n) (Fin n) C).map (res O C) = (h : Matrix (Fin n) (Fin n) (ResidueField O)) →
      g * e Y = e ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y *
        (↑h⁻¹ : Matrix (Fin n) (Fin n) (ResidueField O))) * g := by
    intro g h Y hh
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hL, hR, hh, Matrix.mul_assoc ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y),
      Units.inv_mul, Matrix.mul_one]
  have hJ : (Jmat (R := C) n).map (res O C) = Jmat (R := ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have htheta : ∀ Y, theta (e Y) = e (thetaLie Y) := by
    intro Y
    apply Units.ext
    rw [theta_val, heinv, he, he, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, ← Matrix.transpose_map, hL, hJ, hR, hJ]
    rw [show thetaLie Y = Jmat (R := ResidueField O) n * (-Y)ᵀ * Jmat (R := ResidueField O) n by
      simp [thetaLie, Matrix.transpose_neg]]
  refine ⟨e, he, hemul, heinv, fun A X => ⟨hL A X, hR A X⟩, ?_⟩
  intro x X
  obtain ⟨g, s⟩ := x
  have hh : (g : Matrix (Fin n) (Fin n) C).map (res O C) =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  have had : GG.adFun (GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))) X =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) *
        (if s = 1 then X else thetaLie X) *
        (↑(GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG (m := n) (R := C))).left⁻¹ :
          Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  rw [had]
  refine SemidirectProduct.ext ?_ ?_
  · simp only [GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one, ite_eq_left rfl]
      exact hconj _ _ X hh
    · rw [sgnAct_neg_one, ite_eq_right (by decide), htheta]
      exact hconj _ _ _ hh
  · simp only [GG.ofGL, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ConjVal
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

private noncomputable def ee (F : Frame l k) (u : ℤˣ) : F.Γ := if u = 1 then 1 else F.c

private theorem ee_one : ee F 1 = 1 := if_pos rfl

private theorem ee_neg : ee F (-1) = F.c := if_neg (by decide)

private noncomputable def pr (hc : F.del F.c = -1) (s : F.Γ) : F.G0 :=
  ⟨s * ee F (F.del s), by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (F.del s) with h | h
    · rw [h, ee_one, map_one, mul_one]
    · rw [h, ee_neg, hc]; simp⟩

private theorem pr_val (hc : F.del F.c = -1) (s : F.Γ) : (pr hc s : F.Γ) = s * ee F (F.del s) := rfl

private theorem pr_coe (hc : F.del F.c = -1) (s : F.G0) : pr hc s = s := by
  apply Subtype.ext
  have h : F.del s = 1 := s.2
  rw [pr_val, h, ee_one, mul_one]

private theorem conj_val (s : F.G0) : (F.conj s : F.Γ) = F.c * s * F.c⁻¹ := rfl

private theorem del_lc (ho : IsOpen (F.del.ker : Set F.Γ)) : IsLocallyConstant F.del := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) := ho.preimage (by fun_prop)
  filter_upwards [h1.mem_nhds (show x⁻¹ * x ∈ F.del.ker by simp)] with y hy
  have h2 : F.del (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem pr_cont (hc : F.del F.c = -1) (ho : IsOpen (F.del.ker : Set F.Γ)) : Continuous (pr hc) :=
  Continuous.subtype_mk (continuous_id.mul ((del_lc ho).comp (ee F)).continuous) _

private theorem theta_r {n : ℕ} {C : Type} [CommRing C] (ρ : NRep F n C) (g : F.G0) :
    theta (ρ.r.toHomUnits g) = ρ.r.toHomUnits (F.conj g) := by
  apply Units.ext
  rw [theta_val, ← map_inv, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, ← ρ.pol, Frame.star, inv_inv]

private noncomputable def rp (hc : F.del F.c = -1) (hs : F.c * F.c = 1) {n : ℕ} {C : Type} [CommRing C]
    (ρ : NRep F n C) : F.Γ →* GG (m := n) (R := C) where
  toFun s := ⟨ρ.r.toHomUnits (pr hc s), F.del s⟩
  map_one' := by
    have h : pr hc (1 : F.Γ) = 1 := pr_coe hc 1
    ext1
    · simp [h]
    · simp
  map_mul' s t := by
    have hi : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hs
    have hs' : ∀ x, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hs, one_mul]
    ext1
    · rw [SemidirectProduct.mul_left]
      dsimp only
      rcases Int.units_eq_one_or (F.del s) with h | h
      · rw [h, sgnAct_one, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, pr_val, pr_val, pr_val, map_mul, h, ee_one, one_mul, mul_one, mul_assoc]
      · rw [h, sgnAct_neg_one, theta_r, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, conj_val, pr_val, pr_val, pr_val, map_mul, h, ee_neg, hi]
        rcases Int.units_eq_one_or (F.del t) with h' | h'
        · rw [h', mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs']
        · rw [h', neg_mul_neg, mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs', hs]
    · simp

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_box :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (ρ : NRep F n C), ρ.Cont I → (∀ v, UpperTheory.V.W.HasFlag (ρ.r.comp (F.loc0 v)).toHomUnits (ρ.ψ v)) → ∃ B : Box F n C, B.Of ρ ∧ B.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I ρ hc hf
  choose g hg using hf
  have hm : ∀ s, (rp hF.del_c hF.c_sq ρ s).mat = ρ.r (pr hF.del_c s) := fun s => rfl
  refine ⟨⟨rp hF.del_c hF.c_sq ρ, fun s => rfl, g, fun v s i j h => ?_⟩, ⟨?_, fun s => ?_, fun v i s => ?_⟩,
    fun i j N => ?_⟩
  · have e : pr hF.del_c (F.loc v s) = F.loc0 v s := pr_coe hF.del_c (F.loc0 v s)
    rw [hm, e]
    exact (hg v s).1 i j h
  · have e : pr hF.del_c F.c = 1 := by
      apply Subtype.ext
      rw [pr_val, hF.del_c, ee_neg, hF.c_sq]
      rfl
    show (rp hF.del_c hF.c_sq ρ F.c).mat = 1
    rw [hm, e, map_one]
  · show (rp hF.del_c hF.c_sq ρ s).mat = _
    rw [hm, pr_coe]
  · exact (hg v s).2 i
  · exact (hc.1 i j N).comp_continuous (pr_cont hF.del_c hF.del_open)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBstab
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C}
    (hM : UpT M) (hN : UpT N) : UpT (M * N) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a < i
  · rw [hM i a ha, zero_mul]
  · rw [hN a j (lt_of_lt_of_le h (not_lt.mp ha)), mul_zero]

theorem UpperTheory.V.Fr.pr_bstab :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (C : Type) [CommRing C] (B : Box F n C) (v : F.V) (s : F.Gv v), ∀ X ∈ B.b v, B.ad (F.loc v s) X ∈ B.b v := by
  intro l _ k _ F n C _ B v s X hX
  have h1 : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have h2 : (B.r (F.loc v s⁻¹)).left = (B.r (F.loc v s)).left⁻¹ := by
    rw [map_inv, map_inv, SemidirectProduct.inv_left, h1, inv_one, sgnAct_one]
  have t1 := B.tri v s
  have t2 := B.tri v s⁻¹
  have t3 := upT_mul (upT_mul t1 hX) t2
  simp only [GG.mat, h2] at t3
  show UpT ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).adFun X *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))
  have hg : ∀ Y : Matrix (Fin n) (Fin n) C,
      (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * ((B.g v : Matrix (Fin n) (Fin n) C) * Y) = Y :=
    fun Y => Units.inv_mul_cancel_left _ Y
  simp only [Matrix.mul_assoc, hg] at t3
  simp only [GG.adFun, GG.mat, h1, if_true, Matrix.mul_assoc]
  exact t3
end
