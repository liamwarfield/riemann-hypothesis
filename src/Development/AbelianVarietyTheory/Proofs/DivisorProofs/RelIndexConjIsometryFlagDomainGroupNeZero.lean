module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfFgAndSpanningLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenExists
namespace GlobalTheory.DenominatorExistence

open NumberField

theorem den_exists {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := hc.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have h' : (y.natAbs : ℤ) = y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = (y : E) := congrArg _ h'
    rw [Int.cast_natCast] at h2
    rw [h2, ← zsmul_eq_mul]; exact hint
  · have h' : (y.natAbs : ℤ) = -y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = ((-y : ℤ) : E) := congrArg _ h'
    rw [Int.cast_natCast, Int.cast_neg] at h2
    rw [h2, neg_mul, ← zsmul_eq_mul]; exact hint.neg

theorem main {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ Λ' : Submodule (RingOfIntegers E) (Fin r → E)) (hfg : Λ'.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by

  have key : ∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ n • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
      rw [smul_add]
      refine Λ.add_mem ?_ ?_
      · rw [mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hax b
      · rw [mul_comm, mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hby a
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨d, hd, hdc⟩ := den_exists c
      refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
      have e1 : (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x)
          = ((d : E) * c) • (a • x) := by
        rw [← algebraMap_smul E]; rfl
      have e : (d * a) • (c • x) = (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x) := by
        rw [e1, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul]
        congr 1
        push_cast; ring
      rw [e]; exact Λ.smul_mem _ hax
  obtain ⟨s, hs⟩ := hfg
  classical
  choose f hfpos hfmem using key
  refine ⟨∏ x ∈ s, f x, Finset.prod_pos (fun x _ => hfpos x), ?_⟩
  intro v hv
  rw [Nat.cast_smul_eq_nsmul]
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s f hx, mul_nsmul]
    exact Λ.toAddSubmonoid.nsmul_mem (hfmem x) _
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Λ.add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Λ.smul_mem o hx

end GlobalTheory.DenominatorExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfFgAndSpanningLattice
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem exists_pos_nat_smul_mem_of_fg_of_span_eq_top :
    ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)),
      Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
        ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistence.main
  | exact _root_.GlobalTheory.DenominatorExistence.main
  | (apply _root_.GlobalTheory.DenominatorExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistence.main ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfFgAndSpanningLatticeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)), Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by
  first | exact @GlobalTheory.exists_pos_nat_smul_mem_of_fg_of_span_eq_top | exact GlobalTheory.exists_pos_nat_smul_mem_of_fg_of_span_eq_top | (intros; apply GlobalTheory.exists_pos_nat_smul_mem_of_fg_of_span_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRelIndexStabilizerCommensurableLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRelIndexStabilizerCommensurableLatti
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.LatticeCongr

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

def sqMul (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) : Submodule (𝓞 E) (Fin r → E) :=
  Λ.map ((((n : E) ^ 2) • LinearMap.id : (Fin r → E) →ₗ[E] (Fin r → E)).restrictScalars (𝓞 E))

theorem mem_sqMul {Λ : Submodule (𝓞 E) (Fin r → E)} {n : ℕ} {x : Fin r → E} :
    x ∈ sqMul Λ n ↔ ∃ y ∈ Λ, ((n : E) ^ 2) • y = x := by
  simp [sqMul]

def sqSub (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) : Submodule (𝓞 E) Λ :=
  Submodule.comap Λ.subtype (sqMul Λ n)

def act (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) : Λ →ₗ[𝓞 E] Λ :=
  ((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)).restrict
    fun x hx => (h x).1 hx

@[simp] theorem act_apply (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) (x : Λ) :
    ((act Λ γ h x : Λ) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E).mulVec x := rfl

theorem act_sqSub (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) :
    sqSub Λ n ≤ (sqSub Λ n).comap (act Λ γ h) := by
  intro x hx
  simp only [sqSub, Submodule.mem_comap, Submodule.subtype_apply, act_apply] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := mem_sqMul.1 hx
  exact mem_sqMul.2 ⟨_, (h y).1 hy, by rw [← hxy, Matrix.mulVec_smul]⟩

def rep (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) (G : Subgroup (GL (Fin r) E))
    (hG : ∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) :
    G →* Module.End (𝓞 E) (Λ ⧸ sqSub Λ n) where
  toFun g := (sqSub Λ n).mapQ (sqSub Λ n) (act Λ g (hG g g.2)) (act_sqSub Λ n _ _)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp]
    congr 1
    ext
    simp
  map_mul' g g' := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      Module.End.mul_apply]
    congr 1
    ext
    simp [Matrix.mulVec_mulVec]

end GlobalTheory.LatticeCongr

namespace GlobalTheory.LatticeCongr

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem mulVec_mem_of_rep_eq_one {Λ Λ' : Submodule (𝓞 E) (Fin r → E)} {n : ℕ} (hn : 0 < n)
    (h1 : ∀ v ∈ Λ', (n : E) • v ∈ Λ) (h2 : ∀ v ∈ Λ, (n : E) • v ∈ Λ')
    {G : Subgroup (GL (Fin r) E)}
    (hG : ∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ)
    (g : G) (hg : rep Λ n G hG g = 1) (x : Fin r → E) (hx : x ∈ Λ') :
    ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
  have hu : (Submodule.Quotient.mk (act Λ g (hG g g.2) ⟨(n : E) • x, h1 x hx⟩) : Λ ⧸ sqSub Λ n) =
      Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩ :=
    LinearMap.congr_fun hg (Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩)
  rw [Submodule.Quotient.eq] at hu
  obtain ⟨y, hy, hyx⟩ := mem_sqMul.1 hu
  change ((n : E) ^ 2) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec ((n : E) • x) -
    (n : E) • x at hyx
  rw [Matrix.mulVec_smul] at hyx
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hy' : (n : E) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x - x := by
    apply smul_right_injective _ hn'
    simp only [smul_smul, smul_sub, ← pow_two]
    exact hyx
  have : ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x = x + (n : E) • y := by
    rw [hy']; abel
  rw [this]
  exact Λ'.add_mem hx (h2 y hy)

theorem exists_relIndex_ne_zero_stab : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (n : ℕ), 0 < n → Λ.FG → (∀ v ∈ Λ', (n : E) • v ∈ Λ) → (∀ v ∈ Λ, (n : E) • v ∈ Λ') → ∀ G : Subgroup (GL (Fin r) E), (∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) → ∃ K : Subgroup (GL (Fin r) E), K.relIndex G ≠ 0 ∧ ∀ γ ∈ K, ∀ x, x ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
  intro E _ _ r Λ Λ' n hn hfg h1 h2 G hG
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ (Λ ⧸ sqSub Λ n) := Module.Finite.trans (𝓞 E) _
  haveI : Finite (Λ ⧸ sqSub Λ n) := Module.finite_of_fg_torsion _ fun z => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨⟨((n : ℤ) ^ 2), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change ((n : ℤ) ^ 2) • (Submodule.mkQ (sqSub Λ n) y) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (((((n : ℤ) ^ 2) • y : Λ)) : Fin r → E) ∈ sqMul Λ n
    refine mem_sqMul.2 ⟨y, y.2, ?_⟩
    rw [AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul E]
    push_cast
    rfl
  haveI : Finite (Module.End (𝓞 E) (Λ ⧸ sqSub Λ n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  set φ := (rep Λ n G hG).toHomUnits with hφ
  have key : ∀ γ ∈ φ.ker.map G.subtype, ∀ x ∈ Λ',
      (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
    rintro γ ⟨g, hg, rfl⟩ x hx
    refine mulVec_mem_of_rep_eq_one hn h1 h2 hG g ?_ x hx
    have := congrArg Units.val (MonoidHom.mem_ker.1 hg)
    simpa [hφ] using this
  refine ⟨φ.ker.map G.subtype, ?_, ?_⟩
  · show (Subgroup.comap G.subtype (φ.ker.map G.subtype)).index ≠ 0
    rw [Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
    exact Subgroup.FiniteIndex.index_ne_zero
  · intro γ hγ x
    refine ⟨key γ hγ x, fun h => ?_⟩
    have := key γ⁻¹ (inv_mem hγ) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at this

end GlobalTheory.LatticeCongr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRelIndexStabilizerCommensurableLattiStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_relIndex_stabilizer_commensurable_lattice : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (n : ℕ), 0 < n → Λ.FG → (∀ v ∈ Λ', (n : E) • v ∈ Λ) → (∀ v ∈ Λ, (n : E) • v ∈ Λ') → ∀ G : Subgroup (GL (Fin r) E), (∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) → ∃ K : Subgroup (GL (Fin r) E), K.relIndex G ≠ 0 ∧ ∀ γ ∈ K, ∀ x, x ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
  first | exact @GlobalTheory.LatticeCongr.exists_relIndex_ne_zero_stab | exact GlobalTheory.LatticeCongr.exists_relIndex_ne_zero_stab | (intros; apply GlobalTheory.LatticeCongr.exists_relIndex_ne_zero_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZero
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArithIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def moveLin (δ : GL (Fin r) E) : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) :=
  ((δ : Matrix (Fin r) (Fin r) E).mulVecLin).restrictScalars (𝓞 E)

omit [IsCMField E] in
theorem moveLin_apply (δ : GL (Fin r) E) (v : Fin r → E) :
    moveLin δ v = (δ : Matrix (Fin r) (Fin r) E).mulVec v := rfl

omit [NumberField E] [IsCMField E] in
theorem inv_mulVec_mulVec (δ : GL (Fin r) E) (v : Fin r → E) :
    ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
      ((δ : Matrix (Fin r) (Fin r) E).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

omit [NumberField E] [IsCMField E] in
theorem mulVec_inv_mulVec (δ : GL (Fin r) E) (v : Fin r → E) :
    (δ : Matrix (Fin r) (Fin r) E).mulVec
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

omit [IsCMField E] in
theorem mem_map_moveLin (δ : GL (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (y : Fin r → E) :
    y ∈ L.map (moveLin δ) ↔
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [moveLin_apply, inv_mulVec_mulVec]
    exact hx
  · intro h
    exact ⟨_, h, by rw [moveLin_apply, mulVec_inv_mulVec]⟩

omit [IsCMField E] in
theorem span_map_moveLin (δ : GL (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E))
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span E ((L.map (moveLin δ) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) = ⊤ := by
  have hsurj : Function.Surjective (δ : Matrix (Fin r) (Fin r) E).mulVecLin := fun y =>
    ⟨_, mulVec_inv_mulVec δ y⟩
  have : ((L.map (moveLin δ) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) =
      (δ : Matrix (Fin r) (Fin r) E).mulVecLin '' (L : Set (Fin r → E)) := by
    rw [Submodule.map_coe]; rfl
  rw [this, ← Submodule.map_span, hL, Submodule.map_top, LinearMap.range_eq_top]
  exact hsurj

theorem isUStab_conj (X₂ X : Data E r) (δ : GL (Fin r) E) (hG : X₂.Gm = X.Gm)
    (hδ : ∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v)
      ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hK : ∀ x, x ∈ X₂.Λ.map (moveLin δ) ↔
      (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ X₂.Λ.map (moveLin δ)) :
    IsUStab X₂.Gm X₂.Λ (δ⁻¹ * γ * δ) := by
  have hval : ∀ x, (((δ⁻¹ * γ * δ : GL (Fin r) E)) : Matrix (Fin r) (Fin r) E).mulVec x =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
        ((γ : Matrix (Fin r) (Fin r) E).mulVec ((δ : Matrix (Fin r) (Fin r) E).mulVec x)) := by
    intro x
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [hval, hval, ← hδ, mulVec_inv_mulVec, mulVec_inv_mulVec, hG, (X.Γ_stab γ hγ).1, ← hG, hδ]
  · rw [hval, ← mem_map_moveLin, ← hK, mem_map_moveLin, inv_mulVec_mulVec]


omit [NumberField E] [IsCMField E] in
theorem relIndex_ne_zero_of_reps (Γ₂ A : Subgroup (GL (Fin r) E)) (δ : GL (Fin r) E)
    (S : Finset (GL (Fin r) E))
    (h : ∀ γ ∈ A, ∃ s ∈ S, s⁻¹ * (δ⁻¹ * γ * δ) ∈ Γ₂) :
    (Γ₂.map (MulAut.conj δ).toMonoidHom).relIndex A ≠ 0 := by
  classical
  set H := Γ₂.map (MulAut.conj δ).toMonoidHom with hH
  choose! f hfS hf using h
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    refine Finite.of_injective
      (fun q : A ⧸ H.subgroupOf A => (⟨f (q.out : A), hfS _ q.out.2⟩ : S)) ?_
    intro p q hpq
    have hpq' : f (p.out : A) = f (q.out : A) := congrArg Subtype.val hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have ha := hf _ p.out.2
    have hb := hf _ q.out.2
    rw [hpq'] at ha
    have hc := Γ₂.mul_mem (Γ₂.inv_mem ha) hb
    refine ⟨_, hc, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_map_conj_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ : GL (Fin r) E), X₂.Gm = X.Gm → (∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w) → (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 := by
  intro E _ _ _ r X₂ X δ hG hδ
  set Λ' := X₂.Λ.map (moveLin δ) with hΛ'
  have hfg : Λ'.FG := X₂.Λ_fg.map _
  have hsp := span_map_moveLin δ X₂.Λ X₂.Λ_span
  obtain ⟨n₁, hn₁, h₁⟩ := GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice X.Λ Λ' hfg X.Λ_span
  obtain ⟨n₂, hn₂, h₂⟩ := GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice Λ' X.Λ X.Λ_fg hsp
  have hnat : ∀ (L : Submodule (𝓞 E) (Fin r → E)) (k : ℕ) (v : Fin r → E), v ∈ L →
      (k : E) • v ∈ L := by
    intro L k v hv
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv k
  have hA : ∀ v ∈ Λ', ((n₁ * n₂ : ℕ) : E) • v ∈ X.Λ := by
    intro v hv
    have := hnat _ n₂ _ (h₁ v hv)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm n₂] at this
  have hB : ∀ v ∈ X.Λ, ((n₁ * n₂ : ℕ) : E) • v ∈ Λ' := by
    intro v hv
    have := hnat _ n₁ _ (h₂ v hv)
    rwa [smul_smul, ← Nat.cast_mul] at this
  obtain ⟨K, hK, hKΛ⟩ := GlobalTheory.T.exists_finite_relIndex_stabilizer_commensurable_lattice X.Λ Λ' (n₁ * n₂) (Nat.mul_pos hn₁ hn₂) X.Λ_fg hA hB X.Γ
    (fun γ hγ => (X.Γ_stab γ hγ).2)
  obtain ⟨S, hS⟩ := X₂.Γ_index
  have hAH : (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex (X.Γ ⊓ K) ≠ 0 :=
    relIndex_ne_zero_of_reps X₂.Γ (X.Γ ⊓ K) δ S fun γ hγ =>
      hS _ (isUStab_conj X₂ X δ hG hδ hγ.1 (hKΛ γ hγ.2))
  refine Subgroup.relIndex_ne_zero_trans hAH ?_
  rwa [Subgroup.inf_relIndex_left]

end GlobalTheory.ArithIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZeroStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_conj_isometry_flagDomainGroup_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ : GL (Fin r) E), X₂.Gm = X.Gm → (∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w) → (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 := by
  first | exact @GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | exact GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero | (intros; apply GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero <;> assumption)
end
