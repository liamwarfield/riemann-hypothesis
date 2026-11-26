module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
noncomputable section

namespace UpperTheory.V.Loc

open ReciprocityTheory.Gal

def coSub {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : Submodule A V :=
  Submodule.span A {y | ∃ g x, y = ρ g x - ((χ g : Aˣ) : A) • x}

def lSub (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) : Submodule ℤ_[l] X :=
  LinearMap.range (((l : ℤ_[l]) ^ m) • (LinearMap.id : X →ₗ[ℤ_[l]] X))

theorem mem_lSub {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module ℤ_[l] X] {m : ℕ} {x : X} :
    x ∈ lSub l X m ↔ ∃ y, (l : ℤ_[l]) ^ m • y = x := by
  simp only [lSub, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]

def redRep {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] G X) (m : ℕ) : Representation ℤ_[l] G (X ⧸ lSub l X m) :=
  ρ.quotient (lSub l X m) fun g _ hx => by
    obtain ⟨y, rfl⟩ := mem_lSub.1 hx
    exact mem_lSub.2 ⟨ρ g y, (map_smul _ _ _).symm⟩

theorem redRep_mk {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] G X) (m : ℕ) (g : G) (x : X) :
    redRep ρ m g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := rfl

theorem mem_lSub_pi {l : ℕ} [Fact l.Prime] {n m : ℕ} {x : Fin n → ℤ_[l]} :
    x ∈ lSub l (Fin n → ℤ_[l]) m ↔ ∀ i, PadicInt.toZModPow m (x i) = 0 := by
  rw [mem_lSub]
  have key : ∀ a : ℤ_[l], PadicInt.toZModPow m a = 0 ↔ (l : ℤ_[l]) ^ m ∣ a := by
    intro a
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  simp only [key]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => by simp [Pi.smul_apply, smul_eq_mul, hy i]⟩

theorem isOpen_lSub_pi (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    IsOpen ((lSub l (Fin n → ℤ_[l]) m : Submodule ℤ_[l] (Fin n → ℤ_[l])) : Set (Fin n → ℤ_[l])) := by
  have hset : ((lSub l (Fin n → ℤ_[l]) m : Submodule ℤ_[l] (Fin n → ℤ_[l])) : Set (Fin n → ℤ_[l])) =
      ⋂ i, (fun x : Fin n → ℤ_[l] => x i) ⁻¹' Metric.closedBall (0 : ℤ_[l]) ((l : ℝ) ^ (-(m : ℤ))) := by
    ext x
    simp only [SetLike.mem_coe, mem_lSub_pi, Set.mem_iInter, Set.mem_preimage, mem_closedBall_zero_iff]
    refine forall_congr' fun i => ?_
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (IsUltrametricDist.isOpen_closedBall _
      (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))).preimage (continuous_apply i)

instance discrete_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    DiscreteTopology ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
  QuotientAddGroup.discreteTopology (N := (lSub l (Fin n → ℤ_[l]) m).toAddSubgroup) (isOpen_lSub_pi l n m)

theorem card_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Nat.card ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) = l ^ (m * n) := by
  let f : (Fin n → ℤ_[l]) →+ (Fin n → ZMod (l ^ m)) :=
    AddMonoidHom.compLeft (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toAddMonoidHom (Fin n)
  have hf : Function.Surjective f := by
    intro z
    choose k hk using fun i => ZMod.intCast_surjective (z i)
    exact ⟨fun i => (k i : ℤ_[l]), funext fun i => by simp [f, hk i]⟩
  have hk : f.ker = (lSub l (Fin n → ℤ_[l]) m).toAddSubgroup := by
    ext x
    simp [f, mem_lSub_pi, funext_iff]
  have e : ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) ≃ (Fin n → ZMod (l ^ m)) :=
    ((QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hf)).toEquiv
  rw [Nat.card_congr e]
  simp [Nat.card_fun, pow_mul]

instance finite_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
  Nat.finite_of_card_ne_zero (by rw [card_quot_lSub]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

theorem contAction_redRep {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {n : ℕ}
    {ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])} (h : ContAction ρ) (m : ℕ) : ContAction (redRep ρ m) := by
  unfold ReciprocityTheory.Gal.ContAction at h ⊢
  rw [← (IsOpenQuotientMap.id.prodMap (lSub l (Fin n → ℤ_[l]) m).isOpenQuotientMap_mkQ).continuous_comp_iff]
  refine ((lSub l (Fin n → ℤ_[l]) m).continuous_mkQ.comp h).congr ?_
  intro p
  exact (redRep_mk ρ m p.1 p.2).symm

def FinLevel (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation ℤ_[l] G M), ContAction ρ →
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ n, 3 ≤ n → Subsingleton (Hn ρ n)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ d ∧
      Nat.card (H2 ρ) = Nat.card (M ⧸ coSub χ ρ)

def FinLevelMod (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ) :
    Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation (ZMod (l ^ r)) G M), ContAction ρ →
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ n, 3 ≤ n → Subsingleton (Hn ρ n)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ d ∧
      Nat.card (H2 ρ) = Nat.card (H0dual
        ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ)

def Grows (l : ℕ) (a : ℕ → ℕ) (s : ℕ) : Prop := ∃ C : ℕ, ∀ m, 0 < m → l ^ (m * s) ≤ a m ∧ a m ≤ l ^ (m * s + C)

end UpperTheory.V.Loc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
variable {Q : Type} [Field Q] {G V V' B : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
  [AddCommGroup B] [Module Q B]

private def fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (r g) (a g) - LinearMap.id)

private theorem mem_fixT {V : Type} [AddCommGroup V] [Module Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B)
    (x : V ⊗[Q] B) : x ∈ fixT r a ↔ ∀ g, AlgebraTensorModule.map (r g) (a g) x = x := by
  simp [fixT, Submodule.mem_iInf, sub_eq_zero]

private theorem prodLeft_act (r : V →ₗ[Q] V) (r' : V' →ₗ[Q] V') (a : B →ₗ[Q] B) (x : (V × V') ⊗[Q] B) :
    TensorProduct.prodLeft Q Q V V' B (AlgebraTensorModule.map (r.prodMap r') a x) =
      (AlgebraTensorModule.map r a (TensorProduct.prodLeft Q Q V V' B x).1,
        AlgebraTensorModule.map r' a (TensorProduct.prodLeft Q Q V V' B x).2) := by
  induction x with
  | tmul v b => obtain ⟨v, v'⟩ := v; simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

private theorem fixT_map (r : G → V →ₗ[Q] V) (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) :
    (fixT (fun g => (r g).prodMap (r' g)) a).map (TensorProduct.prodLeft Q Q V V' B).toLinearMap =
      (fixT r a).prod (fixT r' a) := by
  ext y
  obtain ⟨x, rfl⟩ := (TensorProduct.prodLeft Q Q V V' B).surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_prod, mem_fixT, mem_fixT, mem_fixT,
    ← forall_and]
  refine forall_congr' fun g => ?_
  rw [← (TensorProduct.prodLeft Q Q V V' B).injective.eq_iff, prodLeft_act, Prod.ext_iff]

private def prodEquiv' {M N : Type} [AddCommGroup M] [Module Q M] [AddCommGroup N] [Module Q N]
    (p : Submodule Q M) (q : Submodule Q N) : ↥(p.prod q) ≃ₗ[Q] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fixT_finite [FiniteDimensional Q V] (r : G → V →ₗ[Q] V) (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) : Module.Finite Q ↥(fixT r a) := by
  rcases Nat.eq_zero_or_pos (finrank Q V) with h0 | h0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    infer_instance
  · exact Module.finite_of_finrank_pos (h ▸ Nat.mul_pos (Nat.pos_of_ne_zero hn) h0)

private theorem fixT_prod [FiniteDimensional Q V] [FiniteDimensional Q V'] (r : G → V →ₗ[Q] V)
    (r' : G → V' →ₗ[Q] V') (a : G → B →ₗ[Q] B) {n : ℕ} (hn : n ≠ 0)
    (h : finrank Q ↥(fixT r a) = n * finrank Q V) (h' : finrank Q ↥(fixT r' a) = n * finrank Q V') :
    finrank Q ↥(fixT (fun g => (r g).prodMap (r' g)) a) = n * finrank Q (V × V') := by
  haveI := fixT_finite r a hn h
  haveI := fixT_finite r' a hn h'
  rw [← LinearEquiv.finrank_map_eq (TensorProduct.prodLeft Q Q V V' B), fixT_map,
    (prodEquiv' _ _).finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end

theorem UpperTheory.V.Loc.isCrys_isDR_prod :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] (ρ : Representation A G V) (ρ' : Representation A G V'), ContAction ρ → ContAction ρ' → (IsCr φ ρ → IsCr φ ρ' → IsCr φ (ρ.prod ρ')) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ (ρ.prod ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _
  have ho : IsOpen (φ.range : Set (GQ l)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ ho
  have h1 : φ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : (φ.range ⊔ Iq l).index ≠ 0 := fun h =>
    h1 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_left))
  exact ⟨fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQ (φ g)).toLinearMap) h2 h h',
    fun h h' => fixT_prod (fun g => resCoef ℚ_[l] ρ g) (fun g => resCoef ℚ_[l] ρ' g)
      (fun g => ((PP l).actQdR (φ g)).toLinearMap) h1 h h'⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsMonicUnitCoeffZeroAnnihilatingOfSpectrumNo
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem exists_monic_integral_unit_root {l : ℕ} [Fact l.Prime] (a : Om l) (ha : ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (X - C a) ∣ Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have hm : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
  have hs : spectralNorm ℚ_[l] (Om l) a = 1 := ha
  have hc : ∀ n, ‖(minpoly ℚ_[l] a).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hm).1 (le_of_eq hs)
  have h0 : ‖(minpoly ℚ_[l] a).coeff 0‖ = 1 := by
    have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (Om l) a
    rw [hs] at h
    have hpos : (0 : ℝ) < (minpoly ℚ_[l] a).natDegree := by
      exact_mod_cast minpoly.natDegree_pos hint
    have h2 := congrArg (fun t : ℝ => t ^ (((minpoly ℚ_[l] a).natDegree : ℕ) : ℝ)) h
    simp only [Real.one_rpow] at h2
    rw [← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one] at h2
    exact h2.symm
  have hl : minpoly ℚ_[l] a ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨Q, hQm, ?_, ?_⟩
  · rw [PadicInt.isUnit_iff]
    rw [← hQ, coeff_map] at h0
    exact h0
  · rw [← Polynomial.map_map, hQ, dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap]
    exact minpoly.aeval _ _

private theorem aux_mul {l : ℕ} [Fact l.Prime] (s : Multiset (Om l)) (hs : ∀ a ∈ s, ‖a‖ = 1) :
    ∃ Q : ℤ_[l][X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
      (s.map (fun a => X - C a)).prod ∣
        Q.map ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, monic_one, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨Q, h1, h2, h3⟩ := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    obtain ⟨R, g1, g2, g3⟩ := exists_monic_integral_unit_root a (hs a (Multiset.mem_cons_self a s))
    refine ⟨R * Q, g1.mul h1, ?_, ?_⟩
    · rw [mul_coeff_zero]; exact g2.mul h2
    · rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul]
      exact mul_dvd_mul g3 h3

theorem UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), (∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ‖a‖ = 1) → ∃ P : ℤ_[l][X], P.Monic ∧ IsUnit (P.coeff 0) ∧ aeval F (P.map ((algebraMap ℚ_[l] ↥L).comp (algebraMap ℤ_[l] ℚ_[l]))) = 0 := by
  intro l _ L d F hF
  set χ := (F.map (algebraMap ↥L (Om l))).charpoly with hχ
  have hχm : χ.Monic := Matrix.charpoly_monic _
  obtain ⟨Q, h1, h2, h3⟩ := aux_mul χ.roots (fun a ha =>
    hF a (Matrix.mem_spectrum_iff_isRoot_charpoly.2 ((mem_roots hχm.ne_zero).1 ha)))
  refine ⟨Q, h1, h2, ?_⟩
  rw [← (IsAlgClosed.splits χ).eq_prod_roots_of_monic hχm, hχ, Matrix.charpoly_map,
    IsScalarTower.algebraMap_eq ℚ_[l] L (Om l), RingHom.comp_assoc, ← Polynomial.map_map,
    map_dvd_map'] at h3
  obtain ⟨R, hR⟩ := h3
  rw [hR, map_mul, Matrix.aeval_self_charpoly, zero_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmConj
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem kur_map {l : ℕ} [Fact l.Prime] (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    g x ∈ MaximalUnramifiedExtension l := by
  have h1 : g x ∈ (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    (Set.mem_image_of_mem _ hx :)
  rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map] at h1
  refine (IntermediateField.adjoin_le_iff.mpr ?_) h1
  rintro _ ⟨y, ⟨m, hm, hlm, hy⟩, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hy, map_one]⟩

private theorem iq_normal (l : ℕ) [Fact l.Prime] : (Iq l).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (kur_map g⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

section Gen

variable {Q Γ G A V B : Type} [Field Q] [Group Γ] [Group G] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V]
  [Module Q V] [IsScalarTower Q A V] [CommRing B] [Algebra Q B] (α : Γ →* (B ≃ₐ[Q] B))

private noncomputable def cj (c : Γ) : V ⊗[Q] B ≃ₗ[A] V ⊗[Q] B :=
  AlgebraTensorModule.congr (LinearEquiv.refl A V) (α c).toLinearEquiv

private theorem cj_act (c g : Γ) (f : V →ₗ[A] V) (x : V ⊗[Q] B) :
    AlgebraTensorModule.map f (α (c * g * c⁻¹)).toLinearMap (cj (A := A) α c x) =
      cj (A := A) α c (AlgebraTensorModule.map f (α g).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    have h : α (c * g * c⁻¹) (α c b) = α c (α g b) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
    simp only [cj, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul, LinearEquiv.refl_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearEquiv_apply, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem cj_one (c : Γ) (v : V) : cj (A := A) α c (v ⊗ₜ[Q] (1 : B)) = v ⊗ₜ[Q] (1 : B) := by
  simp [cj]

private theorem finrank_inv (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) :
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) =
    finrank A ↥(⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
        (α (φ g)).toLinearMap - (LinearMap.id : V ⊗[Q] B →ₗ[A] V ⊗[Q] B))) := by
  symm
  refine ((cj (A := A) α c).ofSubmodules _ _ ?_).finrank_eq
  ext x
  obtain ⟨y, rfl⟩ := (cj (A := A) (V := V) α c).surjective x
  rw [Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, (cj α c).injective.eq_iff]

private theorem cob_iff (c : Γ) (φ : G →* Γ) (ρ : Representation A G V) (z : G → V) :
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g)
        (α (((MulAut.conj c).toMonoidHom.comp φ) g)).toLinearMap x - x) ↔
    (∃ x : V ⊗[Q] B, ∀ g, z g ⊗ₜ[Q] (1 : B) = AlgebraTensorModule.map (ρ g) (α (φ g)).toLinearMap x - x) := by
  rw [(cj (A := A) (V := V) α c).surjective.exists]
  refine exists_congr fun y => forall_congr' fun g => ?_
  have : ((MulAut.conj c).toMonoidHom.comp φ) g = c * φ g * c⁻¹ := rfl
  rw [this, cj_act, ← map_sub, ← cj_one (A := A) α c, (cj α c).injective.eq_iff, cj_one]

private theorem index_conj (c : Γ) (φ : G →* Γ) (N : Subgroup Γ) [hN : N.Normal] :
    (((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N).index = (φ.range ⊔ N).index := by
  have h1 : N.map (MulAut.conj c).toMonoidHom = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy c
    · intro hx
      refine ⟨c⁻¹ * x * c⁻¹⁻¹, hN.conj_mem x hx c⁻¹, ?_⟩
      simp [mul_assoc]
  have h2 : ((MulAut.conj c).toMonoidHom.comp φ).range ⊔ N = (φ.range ⊔ N).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_sup, h1, MonoidHom.range_comp]
  rw [h2]
  exact Subgroup.index_map_of_bijective (MulAut.conj c).bijective _

end Gen

theorem UpperTheory.V.Loc.admissible_conjugate :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (c : GQ l), (IsCr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsCr φ ρ) ∧ (IsDr ((MulAut.conj c).toMonoidHom.comp φ) ρ ↔ IsDr φ ρ) ∧ UpperTheory.V.Loc.finiteCocycles ((MulAut.conj c).toMonoidHom.comp φ) ρ = UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro l _ G _ _ _ φ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ c
  refine ⟨?_, ?_, ?_⟩
  · haveI := iq_normal l
    have h1 : finrank ℚ_[l] ↥(Dcr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Dcr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQ c φ (resCoef ℚ_[l] ρ)
    rw [IsCr, IsCr, h1, index_conj]
  · have h1 : finrank ℚ_[l] ↥(Ddr ((MulAut.conj c).toMonoidHom.comp φ) (resCoef ℚ_[l] ρ)) =
        finrank ℚ_[l] ↥(Ddr φ (resCoef ℚ_[l] ρ)) := finrank_inv (PP l).actQdR c φ (resCoef ℚ_[l] ρ)
    have h2 := index_conj c φ ⊥
    rw [sup_bot_eq, sup_bot_eq] at h2
    rw [IsDr, IsDr, h1, h2]
  · ext z
    exact and_congr_right fun _ => cob_iff (PP l).actQ c φ ρ z
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteFieldEnoughRootsOfUnity
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.finite_field_enough_roots_of_unity (k : Type) [Field k] [Finite k] :
    HasEnoughRootsOfUnity k (Nat.card kˣ) := by
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have htop : rootsOfUnity (Nat.card kˣ) k = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [mem_rootsOfUnity]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top]

private theorem UpperTheory.V.Loc.mem_closure_of_kernel_containment {G k J : Type} [Group G] [Field k] [Finite k] [Finite J]
    (χ : J → G →* kˣ) (ω : G →* kˣ) (h : ∀ g, (∀ j, χ j g = 1) → ω g = 1) :
    ω ∈ Subgroup.closure (Set.range χ) := by
  classical
  let Φ : G →* (J → kˣ) := Pi.monoidHom χ
  let A := Φ.range
  have hker : Φ.ker ≤ ω.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g fun j => congrFun hg j
  let ψ : A →* kˣ := (QuotientGroup.lift Φ.ker ω hker).comp
    (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  have hψ : ∀ g, ψ (Φ.rangeRestrict g) = ω g := by
    intro g
    have hs : (QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)
        = (g : G ⧸ Φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift Φ.ker ω hker
      ((QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)) = ω g
    rw [hs]
    rfl
  let e : J → (A →* kˣ) := fun j => (Pi.evalMonoidHom (fun _ : J => kˣ) j).comp A.subtype
  have he : ∀ j, (e j).comp Φ.rangeRestrict = χ j := fun j => by
    ext g
    rfl
  have hω : ω = ψ.comp Φ.rangeRestrict := by
    ext g
    rw [MonoidHom.comp_apply, hψ]
  haveI : Finite (A →* kˣ) :=
    Finite.of_injective (fun f : A →* kˣ => (f : A → kˣ)) DFunLike.coe_injective
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI := UpperTheory.V.Loc.finite_field_enough_roots_of_unity k
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent A) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    refine Subtype.ext (funext fun j => ?_)
    simp [pow_card_eq_one']
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent (A →* kˣ)) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun f => ?_
    refine MonoidHom.ext fun a => ?_
    simp [pow_card_eq_one']
  have hS : ψ ∈ Subgroup.closure (Set.range e) := by
    rw [← CommGroup.forall_monoidHom_apply_eq_one_iff k]
    intro η hη
    have ha : CommGroup.monoidHomMonoidHomEquiv A k η = 1 := by
      refine Subtype.ext (funext fun j => ?_)
      have hj := CommGroup.apply_monoidHomMonoidHomEquiv k (e j) η
      rw [hη _ (Subgroup.subset_closure ⟨j, rfl⟩)] at hj
      exact hj
    rw [← CommGroup.apply_monoidHomMonoidHomEquiv k ψ η, ha, map_one]
  have key : ∀ φ ∈ Subgroup.closure (Set.range e),
      φ.comp Φ.rangeRestrict ∈ Subgroup.closure (Set.range χ) := by
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [he]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    | one =>
      rw [MonoidHom.one_comp]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [MonoidHom.mul_comp]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [MonoidHom.inv_comp]
      exact inv_mem hx
  rw [hω]
  exact key ψ hS

theorem UpperTheory.V.Loc.v0e :
    ∀ {G k ι : Type} [Group G] [Field k] [Finite k] [Finite ι] (κ : ι → G →* kˣ) (ω : G →* kˣ), (∃ g, (∀ i j, κ i g = κ j g) ∧ ω g ≠ 1) ↔ ω ∉ Subgroup.closure (Set.range fun q : ι × ι => κ q.1 / κ q.2) := by
  intro G k ι _ _ _ _ κ ω
  constructor
  · rintro ⟨g, hg, hω⟩ hmem
    apply hω
    refine Subgroup.closure_induction (p := fun x _ => x g = 1) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨q, rfl⟩
      simp [hg q.1 q.2]
    · rfl
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro x _ hx
      simp [hx]
  · intro hn
    by_contra hc
    apply hn
    refine UpperTheory.V.Loc.mem_closure_of_kernel_containment _ ω fun g hg => ?_
    by_contra hne
    refine hc ⟨g, fun i j => ?_, hne⟩
    have := hg (i, j)
    simpa [div_eq_one] using this
end
