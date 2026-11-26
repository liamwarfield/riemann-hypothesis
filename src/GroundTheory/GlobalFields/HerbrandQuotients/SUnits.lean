module

public import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsRep

@[expose] public section

section -- merged from GroundTheory.GlobalFields.HerbrandQuotients.SUnitsExact
namespace GroundTheory.Global

open GroundTheory.GroupCoh

variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

theorem hasHerbrandQuotient_cycSubOne_of_finite [Module.Finite ℤ A] (ρ : Representation ℤ G A)
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) :=
  hasCyclicHerbrand_of_finite ρ hσ

theorem cycHerbrand_eq_mul_of_exact (ρA : Representation ℤ G A) (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {i : A →+ B} {p : B →+ C} (hi : Function.Injective i)
    (hex : Function.Exact i p) [Finite (C ⧸ p.range)]
    (hiG : ∀ g a, i (ρA g a) = ρB g (i a)) (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ := by
  have hfS : ∀ x ∈ p.range, cycSubOne ρC σ x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycSubOne ρB σ b, by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]⟩
  have hgS : ∀ x ∈ p.range, cycNorm ρC x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycNorm ρB b, by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]⟩
  have : p.range.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hR := (hasHerbrandQuotient_restrictEnd_iff p.range hfS hgS (cycSubOne_cycNorm ρC σ)
    (cycNorm_cycSubOne ρC σ)).2 hC
  have hex' : Function.Exact i p.rangeRestrict := by
    intro b
    rw [← hex b]
    constructor
    · intro h
      simpa using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa using h)
  rw [cycHerbrand, cycHerbrand, cycHerbrand, ← herbrandQuotient_restrictEnd p.range hfS hgS
    (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)]
  exact herbrandQuotient_eq_mul_of_shortExact hi p.rangeRestrict_surjective hex'
    (fun a => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hiG])
    (fun a => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hiG])
    (fun b => Subtype.ext (by
      change p (cycSubOne ρB σ b) = cycSubOne ρC σ (p b)
      rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]))
    (fun b => Subtype.ext (by
      change p (cycNorm ρB b) = cycNorm ρC (p b)
      rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]))
    (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hR

theorem cycHerbrand_eq_of_surjective_of_finite_ker (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {p : B →+ C} (hp : Function.Surjective p)
    [Finite p.ker] (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρC σ := by
  have hfK : ∀ x ∈ p.ker, cycSubOne ρB σ x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [cycSubOne_apply, map_sub, hpG, hx, map_zero, sub_zero]
  have hgK : ∀ x ∈ p.ker, cycNorm ρB x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cycNorm_apply, map_sum]
    simp [hpG, hx]
  have hfgK : ∀ x, restrictEnd (cycSubOne ρB σ) p.ker hfK
      (restrictEnd (cycNorm ρB) p.ker hgK x) = 0 := fun x =>
    Subtype.ext (by
      change cycSubOne ρB σ (cycNorm ρB x.val) = 0
      exact cycSubOne_cycNorm ρB σ x.val)
  have hgfK : ∀ x, restrictEnd (cycNorm ρB) p.ker hgK
      (restrictEnd (cycSubOne ρB σ) p.ker hfK x) = 0 := fun x =>
    Subtype.ext (by
      change cycNorm ρB (cycSubOne ρB σ x.val) = 0
      exact cycNorm_cycSubOne ρB σ x.val)
  have hA : HasHerbrandQuotient (restrictEnd (cycSubOne ρB σ) p.ker hfK)
      (restrictEnd (cycNorm ρB) p.ker hgK) := hasHerbrandQuotient_of_finite _ _
  have hex : Function.Exact p.ker.subtype p := by
    intro b
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycHerbrand, cycHerbrand,
    herbrandQuotient_eq_mul_of_shortExact p.ker.subtype_injective hp hex
      (fun _ => rfl) (fun _ => rfl)
      (fun b => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG])
      (fun b => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG])
      (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hC,
    herbrandQuotient_eq_one_of_finite hfgK hgfK, one_mul]

theorem cycHerbrand_prod (ρA : Representation ℤ G A) (ρB : Representation ℤ G B) (σ : G)
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hB : HasHerbrandQuotient (cycSubOne ρB σ) (cycNorm ρB)) :
    cycHerbrand (ρA.prod ρB) σ = cycHerbrand ρA σ * cycHerbrand ρB σ := by
  have : Finite (B ⧸ (AddMonoidHom.snd A B).range) := by
    rw [AddMonoidHom.range_eq_top.2 (fun b => ⟨(0, b), rfl⟩)]
    infer_instance
  refine cycHerbrand_eq_mul_of_exact ρA (ρA.prod ρB) ρB σ (i := AddMonoidHom.inl A B)
    (p := AddMonoidHom.snd A B) (fun a a' h => congrArg Prod.fst h) ?_ (fun g a => ?_)
    (fun g b => rfl) hA hB
  · rintro ⟨a, b⟩
    simp only [AddMonoidHom.coe_snd, Set.mem_range, AddMonoidHom.inl_apply, Prod.ext_iff]
    constructor
    · rintro rfl
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨a', -, rfl⟩
      rfl
  · exact Prod.ext rfl (map_zero (ρB g)).symm

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.HerbrandQuotients.UnitsHerbrandValue
section -- merged from GroundTheory.GlobalFields.HerbrandQuotients.UnitsHerbrand
namespace GroundTheory.Global

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct

noncomputable section

section Log

open scoped Classical

variable (L : Type*) [Field L] [NumberField L]

def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun x w := (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L)))
  map_zero' := by
    funext w
    simp
  map_add' x y := by
    funext w
    simp only [toMul_add, Units.val_mul, map_mul, Pi.add_apply]
    rw [Real.log_mul (pos_at_place _ w).ne' (pos_at_place _ w).ne', mul_add]

omit [NumberField L] in
theorem fullLog_apply (x : Additive (𝓞 L)ˣ) (w : InfinitePlace L) :
    fullLog L x w = (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 L) L (x.toMul : 𝓞 L))) :=
  rfl

theorem sum_fullLog (x : Additive (𝓞 L)ˣ) : ∑ w, fullLog L x w = 0 :=
  sum_mult_mul_log x.toMul

def logLattice : Submodule ℤ (InfinitePlace L → ℝ) :=
  LinearMap.range (fullLog L).toIntLinearMap

def logProj : (InfinitePlace L → ℝ) →ₗ[ℝ] logSpace L :=
  LinearMap.funLeft ℝ ℝ Subtype.val

theorem logProj_fullLog (x : Additive (𝓞 L)ˣ) : logProj L (fullLog L x) = logEmbedding L x :=
  rfl

theorem fullLog_eq_zero_iff (x : Additive (𝓞 L)ˣ) : fullLog L x = 0 ↔ x.toMul ∈ torsion L := by
  constructor
  · intro h
    rw [← logEmbedding_eq_zero_iff, ofMul_toMul, ← logProj_fullLog, h, map_zero]
  · intro h
    rw [mem_torsion] at h
    funext w
    rw [fullLog_apply, h w, Real.log_one, mul_zero, Pi.zero_apply]

theorem logProj_mem_unitLattice (m : logLattice L) : logProj L m ∈ unitLattice L := by
  obtain ⟨x, hx⟩ := m.2
  rw [← hx]
  exact ⟨x, trivial, rfl⟩

def logLatticeEquiv : logLattice L ≃ₗ[ℤ] unitLattice L :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (unitLattice L) ((logProj L).restrictScalars ℤ ∘ₗ (logLattice L).subtype)
      (logProj_mem_unitLattice L)) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro m hm
      obtain ⟨x, hx⟩ := m.2
      have h1 : logEmbedding L x = 0 := by
        rw [← logProj_fullLog]
        have := congrArg Subtype.val hm
        simp only [ZeroMemClass.coe_zero] at this
        change logProj L (fullLog L x) = 0
        rw [show fullLog L x = (m : InfinitePlace L → ℝ) from hx]
        exact this
      rw [← ofMul_toMul x, logEmbedding_eq_zero_iff, ← fullLog_eq_zero_iff] at h1
      apply Subtype.ext
      rw [← hx]
      exact h1
    · rintro ⟨y, x, -, rfl⟩
      exact ⟨⟨fullLog L x, x, rfl⟩, rfl⟩

instance : Module.Free ℤ (logLattice L) :=
  have := ZLattice.module_free ℝ (unitLattice L)
  Module.Free.of_equiv (logLatticeEquiv L).symm

instance : Module.Finite ℤ (logLattice L) :=
  have := ZLattice.module_finite ℝ (unitLattice L)
  Module.Finite.equiv (logLatticeEquiv L).symm

theorem finrank_logLattice : finrank ℤ (logLattice L) = rank L :=
  (logLatticeEquiv L).finrank_eq.trans (unitLattice_rank L)

theorem linearIndependent_logLattice_basis {ι : Type*} (b : Basis ι ℤ (logLattice L)) :
    LinearIndependent ℝ (fun i => (b i : InfinitePlace L → ℝ)) := by
  apply LinearIndependent.of_comp (logProj L)
  have := ((b.map (logLatticeEquiv L)).ofZLatticeBasis ℝ (unitLattice L)).linearIndependent
  convert this using 1
  · funext i
    rw [Basis.ofZLatticeBasis_apply, Basis.map_apply]
    rfl

end Log

section Galois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem mult_smul (g : L ≃ₐ[K] L) (w : InfinitePlace L) : (g • w).mult = w.mult := by
  have := isReal_smul_iff (σ := g) (w := w)
  unfold mult
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.mp h1) h2
  · exact absurd (this.mpr h2) h1
  · rfl

omit [NumberField K] [NumberField L] in
theorem fullLog_unitsRep (g : L ≃ₐ[K] L) (x : Additive (𝓞 L)ˣ) :
    fullLog L (unitsRep K L g x) = funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (fullLog L x) := by
  funext w
  rw [funPermRep_apply, fullLog_apply, fullLog_apply, mult_smul, unitsRep_apply, toMul_ofMul,
    InfinitePlace.smul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  rfl

omit [NumberField K] [NumberField L] in
theorem funPermRep_mem_logLattice (g : L ≃ₐ[K] L) {m : InfinitePlace L → ℝ}
    (hm : m ∈ logLattice L) : funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m ∈ logLattice L := by
  obtain ⟨x, rfl⟩ := hm
  exact ⟨unitsRep K L g x, fullLog_unitsRep g x⟩

variable (K L) in
def logLatticeRep : Representation ℤ (L ≃ₐ[K] L) (logLattice L) where
  toFun g := ((funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g).restrictScalars ℤ).restrict
    fun _ hm => funPermRep_mem_logLattice g hm
  map_one' := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((1 : L ≃ₐ[K] L)⁻¹ • w) = (m : InfinitePlace L → ℝ) w
    rw [inv_one, one_smul]
  map_mul' g h := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    funext w
    change (m : InfinitePlace L → ℝ) ((g * h)⁻¹ • w) = (m : InfinitePlace L → ℝ) (h⁻¹ • g⁻¹ • w)
    rw [mul_inv_rev, mul_smul]

omit [NumberField K] [NumberField L] in
theorem coe_logLatticeRep (g : L ≃ₐ[K] L) (m : logLattice L) :
    (logLatticeRep (K := K) (L := L) g m : InfinitePlace L → ℝ) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m :=
  rfl

variable [FiniteDimensional K L]

omit [NumberField K] in
theorem cycHerbrand_unitsRep_eq_logLattice {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (unitsRep K L) σ = cycHerbrand (logLatticeRep (K := K) (L := L)) σ := by
  let p : Additive (𝓞 L)ˣ →+ logLattice L := (fullLog L).toIntLinearMap.rangeRestrict.toAddMonoidHom
  have hp : Function.Surjective p := (fullLog L).toIntLinearMap.surjective_rangeRestrict
  have : Finite p.ker := by
    refine Finite.of_injective (β := torsion L)
      (fun x => ⟨(x : Additive (𝓞 L)ˣ).toMul, (fullLog_eq_zero_iff L x).1 ?_⟩) ?_
    · have := congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)
      exact this
    · intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Additive.toMul.injective h)
  exact cycHerbrand_eq_of_surjective_of_finite_ker (unitsRep K L)
    (logLatticeRep (K := K) (L := L)) σ hp
    (fun g x => Subtype.ext (fullLog_unitsRep g x))
    (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)

end Galois

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem piScalarRight_baseChange_funPermRep {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] (g : G) (y : ℝ ⊗[ℤ] (X → ℤ)) :
    TensorProduct.piScalarRight ℤ ℝ ℝ X ((funPermRep ℤ G X g).baseChange ℝ y) =
      funPermRep ℝ G X g (TensorProduct.piScalarRight ℤ ℝ ℝ X y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r f =>
    funext x
    simp [LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul, funPermRep_apply]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]

def logLatticeProdMap : logLattice L × ℤ →ₗ[ℤ] (InfinitePlace L → ℝ) :=
  (logLattice L).subtype.coprod (LinearMap.toSpanSingleton ℤ (InfinitePlace L → ℝ) 1)

omit [NumberField L] in
theorem logLatticeProdMap_apply (m : logLattice L) (n : ℤ) :
    logLatticeProdMap (m, n) = (m : InfinitePlace L → ℝ) + n • (1 : InfinitePlace L → ℝ) :=
  rfl

omit [NumberField K] [NumberField L] in
theorem logLatticeProdMap_comm (g : L ≃ₐ[K] L) (x : logLattice L × ℤ) :
    logLatticeProdMap (((logLatticeRep (K := K) (L := L)).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (logLatticeProdMap x) := by
  obtain ⟨m, n⟩ := x
  funext w
  simp [logLatticeProdMap_apply, Representation.prod_apply_apply, coe_logLatticeRep,
    funPermRep_apply]

theorem linearIndependent_logLattice_one {ι : Type*} (b : Basis ι ℤ (logLattice L)) :
    LinearIndependent ℝ (Sum.elim (fun i => (b i : InfinitePlace L → ℝ))
      (fun _ : Unit => (1 : InfinitePlace L → ℝ))) := by
  classical
  refine LinearIndependent.sum_type (linearIndependent_logLattice_basis L b) ?_ ?_
  · rw [linearIndependent_unique_iff]
    exact one_ne_zero
  · let s : (InfinitePlace L → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => ∑ w, y w
        map_add' := fun y z => by simp [Finset.sum_add_distrib]
        map_smul' := fun c y => by simp [Finset.mul_sum] }
    have hs : Submodule.span ℝ (Set.range fun i => (b i : InfinitePlace L → ℝ)) ≤
        LinearMap.ker s := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := (b i).2
      change ∑ w, (b i : InfinitePlace L → ℝ) w = 0
      rw [← hx]
      exact sum_fullLog L x
    rw [Submodule.disjoint_def]
    intro y hy1 hy2
    rw [Set.range_const, Submodule.mem_span_singleton] at hy2
    obtain ⟨c, rfl⟩ := hy2
    have h1 : s (c • 1) = 0 := hs hy1
    have h2 : s (c • 1) = c * Fintype.card (InfinitePlace L) := by
      simp [s, Finset.sum_const]
    rw [h2] at h1
    have h3 : (Fintype.card (InfinitePlace L) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [mul_eq_zero, or_iff_left h3] at h1
    rw [h1, zero_smul]

theorem cycHerbrand_logLatticeRep_mul_card {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (logLatticeRep (K := K) (L := L)) σ * Fintype.card (L ≃ₐ[K] L) =
      cycHerbrand (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ := by
  classical
  let bM := Module.Free.chooseBasis ℤ (logLattice L)
  let b := bM.prod (Basis.singleton Unit ℤ)
  let B := Algebra.TensorProduct.basis ℝ b
  let E := (logLatticeProdMap (L := L)).liftBaseChange ℝ
  let v := Sum.elim (fun i => (bM i : InfinitePlace L → ℝ))
    (fun _ : Unit => (1 : InfinitePlace L → ℝ))
  have hEB : ∀ j, E (B j) = v j := by
    intro j
    rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]
    rcases j with i | u
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
  have hli : LinearIndependent ℝ v := linearIndependent_logLattice_one bM
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (logLattice L) ⊕ Unit) =
      finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Fintype.card_sum, Fintype.card_unit, Module.finrank_fintype_fun_eq_card,
      ← Module.finrank_eq_card_chooseBasisIndex, finrank_logLattice, rank]
    have : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
    omega
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hsurj : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨B j, hEB j⟩
  have hdim : finrank ℝ (ℝ ⊗[ℤ] (logLattice L × ℤ)) = finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Module.finrank_eq_card_basis B, hcard]
  have hinj : Function.Injective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  have hbij : Function.Bijective E := ⟨hinj, hsurj⟩
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ (InfinitePlace L)
  let e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ) :=
    (LinearEquiv.ofBijective E hbij).trans P.symm
  have hE : ∀ (g : L ≃ₐ[K] L) y, E ((((logLatticeRep (K := K) (L := L)).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (E y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        map_smul, logLatticeProdMap_comm]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]
  have he : ∀ (g : L ≃ₐ[K] L) y, e ((((logLatticeRep (K := K) (L := L)).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g).baseChange ℝ (e y) := by
    intro g y
    apply P.injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [piScalarRight_baseChange_funPermRep, LinearEquiv.apply_symm_apply,
      LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hE]
  rw [← cycHerbrand_eq_of_real_equiv _ _ σ e he,
    cycHerbrand_prod _ _ σ (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
      (hasHerbrandQuotient_cycSubOne_of_finite _ hσ), cycHerbrand_trivial_int]

variable [IsGalois K L]


open scoped Classical in
theorem cycHerbrand_unitsRep {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (unitsRep (K := K) (L := L)) σ =
      (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  have h1 := cycHerbrand_logLatticeRep_mul_card hσ
  rw [cycHerbrand_funPermRep hσ, prod_card_stabilizer_infinitePlace] at h1
  have h2 : (Fintype.card (L ≃ₐ[K] L) : ℚ) = finrank K L := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have h3 : (finrank K L : ℚ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  apply (eq_div_iff h3).2
  rw [cycHerbrand_unitsRep_eq_logLattice hσ, ← h2]
  exact h1

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open NumberField IsDedekindDomain MulAction Module

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

variable (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]


omit [IsGalois K L] in
theorem hasHerbrandQuotient_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    GroundTheory.GroupCoh.HasHerbrandQuotient (cycSubOne (sUnitRep S hS) σ) (cycNorm (sUnitRep S hS)) :=
  hasHerbrandQuotient_cycSubOne_of_finite _ hσ


omit [IsGalois K L] in
theorem finite_quotient_range_valuationVector :
    Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) := by
  have hn : (-(classNumber L : ℤ)) ≠ 0 := by
    simpa using classNumber_ne_zero L
  refine finite_quotient_of_smul_mem _ hn fun y => ⟨SUnit.placeUnitsMap S y, ?_⟩
  change (SUnit.valuationVector S ∘ₗ SUnit.placeUnitsMap S) y = _
  rw [SUnit.valuationVector_comp_placeUnitsMap]
  rfl


omit [IsGalois K L] [Finite S] in
theorem exact_ofUnits_valuationVector :
    Function.Exact (SUnit.ofUnits (K := L) S).toAdditive
      (SUnit.valuationVector (K := L) S).toAddMonoidHom := by
  intro y
  have h := SetLike.ext_iff.1 (SUnit.ker_valuationVector (K := L) S) y
  rw [LinearMap.mem_ker, LinearMap.mem_range] at h
  exact h


open scoped Classical in
theorem cycHerbrand_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (sUnitRep S hS) σ =
      (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
          ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ)) *
        (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  let := stableMulAction S hS
  have : Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S) := Fintype.ofFinite _
  have : Finite ((S → ℤ) ⧸ (SUnit.valuationVector (K := L) S).toAddMonoidHom.range) :=
    finite_quotient_range_valuationVector S
  have h1 := cycHerbrand_eq_mul_of_exact (unitsRep K L) (sUnitRep S hS)
    (funPermRep ℤ (L ≃ₐ[K] L) S) σ
    (i := (SUnit.ofUnits (K := L) S).toAdditive)
    (p := (SUnit.valuationVector (K := L) S).toAddMonoidHom)
    (fun a b h => SUnit.ofUnits_injective S (congrArg Additive.toMul h))
    (exact_ofUnits_valuationVector S) (fun g a => ofUnits_unitsRep S hS g a)
    (fun g b => valuationVector_sUnitRep S hS g b)
    (hasHerbrandQuotient_cycSubOne_of_finite _ hσ) (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
  rw [h1, cycHerbrand_unitsRep hσ, cycHerbrand_funPermRep hσ,
    prod_card_stabilizer_finitePlace S hS]
  ring

end

end GroundTheory.Global
