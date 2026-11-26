module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIrreducibleOfCountableDimensionIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIrreducibleOfCountableDimensionIrreducible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TensIrr

theorem eq_smul_of_ann {V : Type} [AddCommGroup V] [Module ℂ V] (SV : Set (Module.End ℂ V))
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤)
    (v₀ w : V) (hv₀ : v₀ ≠ 0)
    (h : ∀ a ∈ Algebra.adjoin ℂ SV, a v₀ = 0 → a w = 0) : ∃ c : ℂ, w = c • v₀ := by
  let A := Algebra.adjoin ℂ SV
  let ev : V → (A →ₗ[ℂ] V) := fun y =>
    { toFun := fun a => (a : Module.End ℂ V) y
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hev : ∀ y (a : A), ev y a = (a : Module.End ℂ V) y := fun _ _ => rfl
  have hsurj : Function.Surjective (ev v₀) := by
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (ev v₀)) (fun s hs x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact ⟨⟨s * a, mul_mem (Algebra.subset_adjoin hs) a.2⟩, rfl⟩) with h0 | h0
    · exfalso; apply hv₀
      have h1 : ev v₀ 1 ∈ LinearMap.range (ev v₀) := LinearMap.mem_range_self _ _
      rw [h0, Submodule.mem_bot] at h1
      simpa [hev] using h1
    · exact h0
  have hker : LinearMap.ker (ev v₀) ≤ LinearMap.ker (ev w) := fun a ha => by
    rw [LinearMap.mem_ker, hev] at ha ⊢
    exact h a a.2 ha
  let φ : Module.End ℂ V := ((LinearMap.ker (ev v₀)).liftQ (ev w) hker).comp
    (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm.toLinearMap
  have hφ : ∀ a : A, φ ((a : Module.End ℂ V) v₀) = (a : Module.End ℂ V) w := by
    intro a
    have h2 : (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm (ev v₀ a) =
        Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hev v₀, h2, Submodule.liftQ_apply, hev]
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar SV V (fun s => s.1) hrank
    (fun N hN => hirr N (fun a ha x hx => hN ⟨a, ha⟩ x hx)) φ (fun s => by
      ext y
      obtain ⟨a, rfl⟩ := hsurj y
      have h1 : φ ((s.1 * (a : Module.End ℂ V)) v₀) = (s.1 * (a : Module.End ℂ V)) w :=
        hφ ⟨s.1 * a, mul_mem (Algebra.subset_adjoin s.2) a.2⟩
      simp only [Module.End.mul_apply, hev] at h1 ⊢
      rw [h1, hφ a])
  refine ⟨c, ?_⟩
  have h3 := hφ 1
  simp only [OneMemClass.coe_one, Module.End.one_apply] at h3
  rw [← h3, hc]
  simp

theorem rTensor_mem_adjoin {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (SV : Set (Module.End ℂ V)) (N : Submodule ℂ (V ⊗[ℂ] U))
    (hN : ∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) :
    ∀ a ∈ Algebra.adjoin ℂ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hN a ha
  | algebraMap r =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.rTensor_smul, Module.End.one_eq_id,
      LinearMap.rTensor_id]
    simpa using N.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_add, LinearMap.add_apply]
    exact N.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)

theorem tensor_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro V U _ _ _ _ SV SU hrank _ hV hU N hNV hNU
  classical
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨x₁, hx₁N, hx₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let b := Module.Free.chooseBasis ℂ U
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : ∀ (a : Module.End ℂ V) y j, e (LinearMap.rTensor U a y) j = a (e y j) := by
    intro a y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  have hex : ∃ n, ∃ y ∈ N, y ≠ 0 ∧ (e y).support.card = n := ⟨_, x₁, hx₁N, hx₁, rfl⟩
  obtain ⟨x, hxN, hx0, hxc⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ N, (e y).support.card < (e x).support.card → y = 0 := by
    intro y hy hlt
    by_contra hy0
    exact Nat.find_min hex (hxc ▸ hlt) ⟨y, hy, hy0, rfl⟩
  obtain ⟨j₀, hj₀⟩ : (e x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact (LinearEquiv.map_ne_zero_iff e).mpr hx0
  set v₀ := e x j₀ with hv₀def
  have hv₀ : v₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀
  have hA := rTensor_mem_adjoin SV N hNV
  have hcol : ∀ j, ∃ c : ℂ, e x j = c • v₀ := by
    intro j
    refine eq_smul_of_ann SV hrank hV v₀ (e x j) hv₀ (fun a ha hav => ?_)
    have hy := hmin _ (hA a ha x hxN) (by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j₀, hj₀, ?_⟩
        rw [Finsupp.mem_support_iff, not_not, he]
        exact hav
      · intro i hi
        rw [Finsupp.mem_support_iff] at hi ⊢
        intro h0
        apply hi
        rw [he, h0, map_zero])
    have h5 := he a x j
    rw [hy, map_zero, Finsupp.zero_apply] at h5
    exact h5.symm
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hv₀
  let u : U := b.repr.symm ((e x).mapRange ℓ (map_zero ℓ))
  have hxu : x = v₀ ⊗ₜ u := by
    apply e.injective
    ext j
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    simp only [u, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    obtain ⟨c, hc⟩ := hcol j
    rw [hc, map_smul, hℓ, smul_eq_mul, mul_one]
  have hu : u ≠ 0 := by
    intro hu0
    apply hx0
    rw [hxu, hu0, TensorProduct.tmul_zero]
  have hP : N.comap ((TensorProduct.mk ℂ V U).flip u) = ⊤ := by
    rcases hV (N.comap ((TensorProduct.mk ℂ V U).flip u)) (fun a ha v hv => by
      simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hv ⊢
      have h6 := hNV a ha _ hv
      rwa [LinearMap.rTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : v₀ ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply]
        rw [← hxu]; exact hxN
      rw [h0, Submodule.mem_bot] at h7
      exact hv₀ h7
    · exact h0
  have hQ : ∀ v : V, N.comap (TensorProduct.mk ℂ V U v) = ⊤ := by
    intro v
    rcases hU (N.comap (TensorProduct.mk ℂ V U v)) (fun c hc y hy => by
      simp only [Submodule.mem_comap, TensorProduct.mk_apply] at hy ⊢
      have h6 := hNU c hc _ hy
      rwa [LinearMap.lTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : u ∈ N.comap (TensorProduct.mk ℂ V U v) := by
        have h8 : v ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by rw [hP]; trivial
        simpa using h8
      rw [h0, Submodule.mem_bot] at h7
      exact hu h7
    · exact h0
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨m, n, rfl⟩
  have h9 : n ∈ N.comap (TensorProduct.mk ℂ V U m) := by rw [hQ m]; trivial
  simpa using h9

end GlobalTheory.TensIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIrreducibleOfCountableDimensionIrreducibleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_irreducible_of_countable_dimension_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.TensIrr.tensor_irreducible | exact GlobalTheory.TensIrr.tensor_irreducible | (intros; apply GlobalTheory.TensIrr.tensor_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimen
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RestrTensIrr

open GlobalTheory.SmallThetaModules Formalism.MainNotions.KudlaSiegelWeil

variable {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

def fin (s ξ₀ : ∀ i, N i) (S : Finset ι) : Submodule ℂ (RTens s) :=
  Submodule.span ℂ {z | ∃ ξ, (∀ i ∉ S, ξ i = ξ₀ i) ∧ z = pureT s ξ}

theorem restr_of {s ξ₀ ξ : ∀ i, N i} (h0 : Restr s ξ₀) (S : Finset ι) (h : ∀ i ∉ S, ξ i = ξ₀ i) :
    Restr s ξ := by
  refine (h0.union S.finite_toSet).subset fun i hi => ?_
  by_cases hS : i ∈ S
  · exact Or.inr hS
  · left
    simp only [Set.mem_setOf_eq] at hi ⊢
    rwa [h i hS] at hi

theorem fin_mono (s ξ₀ : ∀ i, N i) {S T : Finset ι} (h : S ⊆ T) : fin s ξ₀ S ≤ fin s ξ₀ T := by
  refine Submodule.span_mono ?_
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨ξ, fun i hi => hξ i fun h' => hi (h h'), rfl⟩

theorem fin_stable {s ξ₀ : ∀ i, N i} (h0 : Restr s ξ₀) (S : Finset ι) {i : ι} (hi : i ∈ S)
    (T : Module.End ℂ (RTens s)) (a : Module.End ℂ (N i))
    (hT : ∀ ξ, Restr s ξ → T (pureT s ξ) = pureT s (Function.update ξ i (a (ξ i)))) :
    ∀ x ∈ fin s ξ₀ S, T x ∈ fin s ξ₀ S := by
  have : fin s ξ₀ S ≤ (fin s ξ₀ S).comap T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rw [hT ξ (restr_of h0 S hξ)]
    refine Submodule.subset_span ⟨_, fun k hk => ?_, rfl⟩
    rw [Function.update_of_ne (show k ≠ i by rintro rfl; exact hk hi)]
    exact hξ k hk
  exact fun x hx => this hx

theorem exists_ins (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) :
    ∃ T : Module.End ℂ (RTens s), ∀ ξ, Restr s ξ →
      T (pureT s ξ) = pureT s (Function.update ξ j (f (ξ j) • n)) := by
  obtain ⟨T, hT⟩ := GlobalTheory.TripleAssembly.exists_rtensOp s
    (Function.update (fun i => (LinearMap.id : Module.End ℂ (N i))) j (f.smulRight n))
  refine ⟨T, fun ξ hξ => ?_⟩
  rw [hT ξ hξ]
  congr 1
  funext i
  by_cases h : i = j
  · subst h
    simp
  · simp [Function.update_of_ne h]

def ins (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) : Module.End ℂ (RTens s) :=
  (exists_ins s j f n).choose

theorem ins_pure (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) (ξ : ∀ i, N i) (hξ : Restr s ξ) :
    ins s j f n (pureT s ξ) = pureT s (Function.update ξ j (f (ξ j) • n)) :=
  (exists_ins s j f n).choose_spec ξ hξ

theorem pureT_zero (s : ∀ i, N i) (ξ : ∀ i, N i) (hξ : Restr s ξ) (j : ι) :
    pureT s (Function.update ξ j 0) = 0 := by
  have h := pureT_mlin hξ j 1 0 0
  rw [one_smul, add_zero] at h
  simpa using h.symm

def insL (s : ∀ i, N i) (j : ι) (f : N j →ₗ[ℂ] ℂ) : N j →ₗ[ℂ] Module.End ℂ (RTens s) where
  toFun := ins s j f
  map_add' n m := by
    refine LinearMap.ext_on (pureT_span s) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    simp only [LinearMap.add_apply, ins_pure s j f _ ξ hξ, smul_add]
    have h := pureT_mlin hξ j 1 (f (ξ j) • n) (f (ξ j) • m)
    rwa [one_smul, one_smul] at h
  map_smul' c n := by
    refine LinearMap.ext_on (pureT_span s) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    simp only [LinearMap.smul_apply, RingHom.id_apply, ins_pure s j f _ ξ hξ]
    have h := pureT_mlin hξ j c (f (ξ j) • n) 0
    rw [add_zero, pureT_zero s ξ hξ, add_zero] at h
    rw [smul_comm, h]

def phi (s ξ₀ : ∀ i, N i) (S : Finset ι) (j : ι) (f : N j →ₗ[ℂ] ℂ) : N j ⊗[ℂ] fin s ξ₀ S →ₗ[ℂ] RTens s :=
  TensorProduct.lift ((insL s j f).compl₂ (fin s ξ₀ S).subtype)

theorem phi_tmul (s ξ₀ : ∀ i, N i) (S : Finset ι) (j : ι) (f : N j →ₗ[ℂ] ℂ) (n : N j) (y : fin s ξ₀ S) :
    phi s ξ₀ S j f (n ⊗ₜ y) = ins s j f n y := rfl

theorem claim {s ξ₀ : ∀ i, N i} (h0 : Restr s ξ₀) (hne : ∀ i, ξ₀ i ≠ 0)
    (hrank : ∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) (hnt : ∀ i, Nontrivial (N i))
    (Sv : ∀ i, Set (Module.End ℂ (N i)))
    (hirr : ∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (RTens s))
    (hOp : ∀ i, ∀ a ∈ Sv i, ∀ ξ, Restr s ξ →
      Op i a (pureT s ξ) = pureT s (Function.update ξ i (a (ξ i))))
    (S : Finset ι) : ∀ Q : Submodule ℂ (RTens s), (∀ i ∈ S, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) →
      ∀ x ∈ fin s ξ₀ S, x ∈ Q → x ≠ 0 → fin s ξ₀ S ≤ Q := by
  induction S using Finset.induction_on with
  | empty =>
    intro Q _ x hx hxQ hx0
    have hle : fin s ξ₀ ∅ ≤ ℂ ∙ pureT s ξ₀ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨ξ, hξ, rfl⟩
      have : ξ = ξ₀ := funext fun i => hξ i (Finset.notMem_empty i)
      subst this
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hle hx)
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx0 (zero_smul _ _)
    have hp : pureT s ξ₀ ∈ Q := by
      have := Q.smul_mem c⁻¹ hxQ
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    exact hle.trans ((Submodule.span_singleton_le_iff_mem _ _).mpr hp)
  | insert j S' hj IH =>
    intro Q hQ x hx hxQ hx0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ (hne j)
    have hrange : fin s ξ₀ (insert j S') ≤ LinearMap.range (phi s ξ₀ S' j f) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨ξ, hξ, rfl⟩
      have hη : ∀ i ∉ S', Function.update ξ j (ξ₀ j) i = ξ₀ i := by
        intro i hi
        by_cases e : i = j
        · subst e
          simp
        · rw [Function.update_of_ne e]
          exact hξ i (by simp [e, hi])
      refine ⟨ξ j ⊗ₜ ⟨pureT s (Function.update ξ j (ξ₀ j)), Submodule.subset_span ⟨_, hη, rfl⟩⟩, ?_⟩
      rw [phi_tmul]
      show ins s j f (ξ j) (pureT s (Function.update ξ j (ξ₀ j))) = pureT s ξ
      rw [ins_pure s j f _ _ (restr_of h0 S' hη), Function.update_self, hf, one_smul]
      simp
    have hΦj : ∀ a ∈ Sv j, (phi s ξ₀ S' j f).comp (LinearMap.rTensor (fin s ξ₀ S') a) =
        (Op j a).comp (phi s ξ₀ S' j f) := by
      intro a ha
      refine TensorProduct.ext' fun n y => ?_
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, phi_tmul]
      have key : Set.EqOn (ins s j f (a n)) ((Op j a).comp (ins s j f n))
          {z | ∃ ξ, (∀ i ∉ S', ξ i = ξ₀ i) ∧ z = pureT s ξ} := by
        rintro _ ⟨η, hη, rfl⟩
        have hr := restr_of h0 S' hη
        simp only [LinearMap.comp_apply]
        rw [ins_pure s j f _ η hr, ins_pure s j f _ η hr, hOp j a ha _ (restr_update hr j _)]
        simp [hη j hj, hf]
      exact LinearMap.eqOn_span' key y.2
    have hΦi : ∀ b ∈ {b : Module.End ℂ (fin s ξ₀ S') | ∃ i ∈ S', ∃ a ∈ Sv i,
        ∀ y : fin s ξ₀ S', (b y : RTens s) = Op i a y}, ∃ i ∈ insert j S', ∃ a ∈ Sv i,
        (phi s ξ₀ S' j f).comp (LinearMap.lTensor (N j) b) = (Op i a).comp (phi s ξ₀ S' j f) := by
      rintro b ⟨i, hi, a, ha, hb⟩
      refine ⟨i, Finset.mem_insert_of_mem hi, a, ha, TensorProduct.ext' fun n y => ?_⟩
      simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, phi_tmul, hb]
      have hij : i ≠ j := by
        rintro rfl
        exact hj hi
      have key : Set.EqOn ((ins s j f n).comp (Op i a)) ((Op i a).comp (ins s j f n))
          {z | ∃ ξ, (∀ i ∉ S', ξ i = ξ₀ i) ∧ z = pureT s ξ} := by
        rintro _ ⟨η, hη, rfl⟩
        have hr := restr_of h0 S' hη
        simp only [LinearMap.comp_apply]
        rw [hOp i a ha η hr, ins_pure s j f _ _ (restr_update hr i _), ins_pure s j f _ η hr,
          hOp i a ha _ (restr_update hr j _), Function.update_of_ne hij.symm, Function.update_of_ne hij,
          hη j hj, hf, one_smul, Function.update_comm hij]
      exact LinearMap.eqOn_span' key y.2
    have hU : ∀ M : Submodule ℂ (fin s ξ₀ S'), (∀ b ∈ {b : Module.End ℂ (fin s ξ₀ S') | ∃ i ∈ S', ∃ a ∈ Sv i,
        ∀ y : fin s ξ₀ S', (b y : RTens s) = Op i a y}, ∀ y ∈ M, b y ∈ M) → M = ⊥ ∨ M = ⊤ := by
      intro M hM
      by_cases hM0 : M = ⊥
      · exact Or.inl hM0
      right
      obtain ⟨y, hyM, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
      have hst : ∀ i ∈ S', ∀ a ∈ Sv i, ∀ z ∈ M.map (fin s ξ₀ S').subtype,
          Op i a z ∈ M.map (fin s ξ₀ S').subtype := by
        rintro i hi a ha _ ⟨w, hw, rfl⟩
        let b : Module.End ℂ (fin s ξ₀ S') :=
          (Op i a).restrict (fin_stable h0 S' hi (Op i a) a (hOp i a ha))
        exact ⟨b w, hM b ⟨i, hi, a, ha, fun _ => rfl⟩ w hw, rfl⟩
      have hle := IH (M.map (fin s ξ₀ S').subtype) hst y y.2 ⟨y, hyM, rfl⟩ (by simpa using hy0)
      rw [eq_top_iff]
      intro w _
      obtain ⟨w', hw', he⟩ := hle w.2
      have : w' = w := Subtype.ext he
      rwa [← this]
    have hN := GlobalTheory.T.tensor_irreducible_of_countable_dimension_irreducible (N j) (fin s ξ₀ S') (Sv j) _ (hrank j) (hnt j) (hirr j) hU
      (Q.comap (phi s ξ₀ S' j f))
      (fun a ha t ht => by
        rw [Submodule.mem_comap] at ht ⊢
        rw [← LinearMap.comp_apply, hΦj a ha, LinearMap.comp_apply]
        exact hQ j (Finset.mem_insert_self j S') a ha _ ht)
      (fun b hb t ht => by
        obtain ⟨i, hi, a, ha, e⟩ := hΦi b hb
        rw [Submodule.mem_comap] at ht ⊢
        rw [← LinearMap.comp_apply, e, LinearMap.comp_apply]
        exact hQ i hi a ha _ ht)
    obtain ⟨t, rfl⟩ := hrange hx
    rcases hN with hN | hN
    · exfalso
      have ht : t ∈ Q.comap (phi s ξ₀ S' j f) := hxQ
      rw [hN, Submodule.mem_bot] at ht
      exact hx0 (by rw [ht, map_zero])
    · refine hrange.trans ?_
      rintro _ ⟨t', rfl⟩
      have ht : t' ∈ Q.comap (phi s ξ₀ S' j f) := by
        rw [hN]
        trivial
      exact ht

end GlobalTheory.RestrTensIrr

theorem GlobalTheory.rtens_irreducible : ∀ {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i),
    {i | s i = 0}.Finite → (∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (N i)) →
    ∀ Sv : ∀ i, Set (Module.End ℂ (N i)),
    (∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤) →
    ∀ Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s),
    (∀ i, ∀ a ∈ Sv i, ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      Op i a (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (Function.update ξ i (a (ξ i)))) →
    ∀ Q : Submodule ℂ (GlobalTheory.SmallThetaModules.RTens s), (∀ i, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  intro ι _ N _ _ s hs hrank hnt Sv hirr Op hOp Q hQ
  classical
  by_cases hQ0 : Q = ⊥
  · exact Or.inl hQ0
  right
  choose e he using fun i => exists_ne (0 : N i)
  let ξ₀ : ∀ i, N i := fun i => if s i = 0 then e i else s i
  have hne : ∀ i, ξ₀ i ≠ 0 := by
    intro i
    by_cases h : s i = 0
    · simp [ξ₀, h, he i]
    · simp [ξ₀, h]
  have h0 : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ₀ := hs.subset fun i hi => by
    by_contra h
    simp only [Set.mem_setOf_eq] at h hi
    exact hi (by simp [ξ₀, h])
  have hfinS : ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ → ∃ S : Finset ι, ∀ i ∉ S, ξ i = ξ₀ i := by
    intro ξ hξ
    refine ⟨(hξ.union h0).toFinset, fun i hi => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hi
    rw [hi.1, hi.2]
  have hall : ∀ x : GlobalTheory.SmallThetaModules.RTens s, ∃ S, x ∈ GlobalTheory.RestrTensIrr.fin s ξ₀ S := by
    intro x
    have hx : x ∈ Submodule.span ℂ {z | ∃ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ ∧ z = GlobalTheory.SmallThetaModules.pureT s ξ} := by
      rw [GlobalTheory.SmallThetaModules.pureT_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ξ, hξ, rfl⟩ := hz
      obtain ⟨S, hS⟩ := hfinS ξ hξ
      exact ⟨S, Submodule.subset_span ⟨ξ, hS, rfl⟩⟩
    | zero => exact ⟨∅, Submodule.zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨S, hS⟩ := ha
      obtain ⟨T, hT⟩ := hb
      exact ⟨S ∪ T, Submodule.add_mem _ (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_left hS)
        (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_right hT)⟩
    | smul c a _ ha =>
      obtain ⟨S, hS⟩ := ha
      exact ⟨S, Submodule.smul_mem _ c hS⟩
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  obtain ⟨S, hxS⟩ := hall x
  rw [eq_top_iff, ← GlobalTheory.SmallThetaModules.pureT_span s, Submodule.span_le]
  rintro _ ⟨ξ, hξ, rfl⟩
  obtain ⟨T, hT⟩ := hfinS ξ hξ
  have hle := GlobalTheory.RestrTensIrr.claim h0 hne hrank hnt Sv hirr Op hOp (S ∪ T) Q
    (fun i _ a ha y hy => hQ i a ha y hy) x
    (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_left hxS) hxQ hx0
  exact hle (GlobalTheory.RestrTensIrr.fin_mono s ξ₀ Finset.subset_union_right (Submodule.subset_span ⟨ξ, hT, rfl⟩))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedTensorProduct_irreducible_countable_dimension : ∀ {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i),
    {i | s i = 0}.Finite → (∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (N i)) →
    ∀ Sv : ∀ i, Set (Module.End ℂ (N i)),
    (∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤) →
    ∀ Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s),
    (∀ i, ∀ a ∈ Sv i, ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      Op i a (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (Function.update ξ i (a (ξ i)))) →
    ∀ Q : Submodule ℂ (GlobalTheory.SmallThetaModules.RTens s), (∀ i, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  first | exact @GlobalTheory.rtens_irreducible | exact GlobalTheory.rtens_irreducible | (intros; apply GlobalTheory.rtens_irreducible <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.TripleAssembly.Irred

section Linear

theorem exists_descend {U P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ U)
    (p : U →ₗ[ℂ] P) (hp : S.map p = ⊤) (Rel : U → U → Prop) (hex : ∀ f ∈ S, ∃ g, Rel f g)
    (hlin : ∀ f ∈ S, ∀ f' ∈ S, ∀ g g', Rel f g → Rel f' g' → ∀ a b : ℂ, Rel (a • f + b • f') (a • g + b • g'))
    (hker : ∀ f ∈ S, ∀ g, Rel f g → p f = 0 → p g = 0) :
    ∃ b : Module.End ℂ P, ∀ f ∈ S, ∀ g, Rel f g → p g = b (p f) := by
  have h1 : ∀ x : P, ∃ f ∈ S, p f = x := fun x => by
    have : x ∈ S.map p := hp ▸ Submodule.mem_top
    exact this
  choose s hs hps using h1
  choose t ht using fun x => hex (s x) (hs x)
  have key : ∀ f ∈ S, ∀ g, Rel f g → p g = p (t (p f)) := fun f hf g h => by
    have := hker _ (add_mem (S.smul_mem 1 hf) (S.smul_mem (-1) (hs (p f)))) _
      (hlin f hf _ (hs (p f)) g _ h (ht _) 1 (-1)) (by simp [hps])
    simpa [add_neg_eq_zero] using this
  have lin : ∀ (a b : ℂ) x y, p (t (a • x + b • y)) = a • p (t x) + b • p (t y) := fun a b x y => by
    have := key _ (add_mem (S.smul_mem a (hs x)) (S.smul_mem b (hs y))) _ (hlin _ (hs x) _ (hs y) _ _ (ht x) (ht y) a b)
    simp only [map_add (f := _), map_smul, hps] at this
    exact this.symm
  refine ⟨{ toFun := fun x => p (t x), map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, key⟩
  · simpa using lin 1 1 x y
  · simpa using lin a 0 x x

theorem nontrivial_tensor {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i)
    (hs : {i | s i = 0}.Finite) (hN : ∀ i, Nontrivial (N i)) (P : Type) [AddCommGroup P] [Module ℂ P] [Nontrivial P] :
    Nontrivial (TensorProduct ℂ P (GlobalTheory.SmallThetaModules.RTens s)) := by
  have h1 : ∀ i, ∃ x : N i, x ≠ 0 ∧ (s i ≠ 0 → x = s i) := fun i => by
    by_cases h : s i = 0
    · obtain ⟨x, hx⟩ := exists_ne (0 : N i)
      exact ⟨x, hx, fun k => absurd h k⟩
    · exact ⟨s i, h, fun _ => rfl⟩
  choose ξ hξ hξs using h1
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hξ i)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.SmallThetaModules.pureT_sep s l (hs.subset fun i hi => by
    by_contra h
    exact hi (by rw [← hξs i h, hl]))
  have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ := hs.subset fun i hi => by
    by_contra h
    exact hi (hξs i h)
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  obtain ⟨m, hm⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  refine ⟨x ⊗ₜ GlobalTheory.SmallThetaModules.pureT s ξ, 0, fun h => ?_⟩
  have := congrArg (LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map m Λ) h
  simp [hΛ ξ hr, hm, hl] at this

end Linear

section Darboux

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end Darboux

section MatrixPart

open scoped Matrix
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealLift.OneParam

theorem exists_lie_of_frame {k d r s : ℕ} (e : Fin k ≃ Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (hc : c ≠ 0)
    (C : Matrix (Fin k) (Ix r s) ℂ) (hC : IsFrame (c • (Hᴴ).submatrix e e) C) (Z : Mat r s) (hZ : Z ∈ upq r s) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, Yᴴ * H + H * Y = 0 ∧
      ∀ t : ℝ, ((NormedSpace.exp (t • Y)).map (starRingEnd ℂ)).submatrix e e * C = C * NormedSpace.exp (t • Z) := by
  obtain ⟨hF, C', hR⟩ := hC
  have hL : C' * C = 1 := frame_inv hF hR
  let φ : Mat r s →+* Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun Z => ((C * Z * C').map (starRingEnd ℂ)).submatrix e.symm e.symm
      map_one' := by simp [hR]
      map_mul' := fun Z Z' => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc C' C, hL, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun Z Z' => by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]
        rfl }
  have hφ : ∀ Z, φ Z = ((C * Z * C').map (starRingEnd ℂ)).submatrix e.symm e.symm := fun _ => rfl
  have hcont : Continuous φ :=
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map
      Complex.continuous_conj).matrix_submatrix _ _
  refine ⟨φ Z, ?_, fun t => ?_⟩
  · set M := c • (Hᴴ).submatrix e e with hM
    have hM' : M = C'ᵀ * Jm r s * C'.map star := by
      rw [← hF]
      calc M = (C * C')ᵀ * M * (C * C').map star := by
            rw [hR, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (by simp) (by simp), Matrix.mul_one]
        _ = _ := by rw [map_star_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    have hL1 : Cᵀ * C'ᵀ = 1 := by rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
    have hL2 : C'.map star * C.map star = 1 := by rw [← map_star_mul, hL, Matrix.map_one _ (by simp) (by simp)]
    have hZ' : Zᵀ * Jm r s + Jm r s * Z.map star = 0 := by
      have h0 : Zᴴ * Jm r s + Jm r s * Z = 0 := hZ
      have := congrArg Matrix.transpose h0
      rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, jm_transpose, Matrix.transpose_zero,
        add_comm] at this
      exact this
    have h1 : (C * Z * C')ᵀ * M + M * (C * Z * C').map star = 0 := by
      calc _ = C'ᵀ * (Zᵀ * (Cᵀ * C'ᵀ) * Jm r s + Jm r s * (C'.map star * C.map star) * Z.map star) * C'.map star := by
            rw [hM', map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
        _ = 0 := by rw [hL1, hL2, Matrix.mul_one, Matrix.mul_one, hZ', Matrix.mul_zero, Matrix.zero_mul]
    rw [hM, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_eq_zero, or_iff_right hc] at h1
    have h2 := congrArg (fun A => (Aᴴ).submatrix e.symm e.symm) h1
    rw [hφ]
    generalize C * Z * C' = Y at h2 ⊢
    have e1 : H = (H.submatrix e e).submatrix e.symm e.symm := by simp
    rw [e1, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_submatrix,
      Matrix.conjTranspose_conjTranspose] at h2
    rw [add_comm] at h2
    ext i j
    exact (congrFun (congrFun h2 i) j).trans (star_zero _)
  · have e1 : t • φ Z = φ (t • Z) := by
      rw [hφ, hφ, Matrix.mul_smul, Matrix.smul_mul]
      generalize C * Z * C' = Y
      ext i j
      simp
    have e2 : NormedSpace.exp (φ (t • Z)) = φ (NormedSpace.exp (t • Z)) := by
      letI : NormedRing (Mat r s) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Mat r s) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Mat r s) := NormedAlgebra.restrictScalars ℚ ℂ (Mat r s)
      letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
      haveI : CompleteSpace (Mat r s) := FiniteDimensional.complete ℂ _
      exact (NormedSpace.map_exp φ hcont _).symm
    rw [e1, e2, hφ]
    have e3 : ∀ A : Matrix (Fin k) (Fin k) ℂ,
        (((A.map (starRingEnd ℂ)).submatrix e.symm e.symm).map (starRingEnd ℂ)).submatrix e e = A := fun A => by
      ext i j; simp
    rw [e3, Matrix.mul_assoc, hL, Matrix.mul_one]

end MatrixPart

section Reading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {D : D7}

theorem toUX_surj (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (hξ : D.host.xi0 ≠ 0) (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    ∃ g : GA D X, GlobalTheory.TripleRead.toUX X e hJ g = h := by
  subst hJ
  have h0 : (h.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) * (h.1.1).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) := h.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h0
  have h1 := congrArg (fun A => incA D D.host.xi0⁻¹ • A) h0
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hξ, map_one, one_smul] at h1
  have h2 := congrArg (fun A => Aᵀ.submatrix e.symm e.symm) h1
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((X.gramᵀ).submatrix e e))ᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e e := rfl
  simp only [transpose_mul, transpose_transpose, e1] at h2
  refine ⟨⟨⟨h.1.1.submatrix e.symm e.symm, h.1.2.submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, h.1.val_inv]; exact Matrix.submatrix_one_equiv e.symm,
    by rw [Matrix.submatrix_mul_equiv, h.1.inv_val]; exact Matrix.submatrix_one_equiv e.symm⟩, ?_⟩, ?_⟩
  · show ((h.1.1.submatrix e.symm e.symm).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram * h.1.1.submatrix e.symm e.symm =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e e).submatrix e.symm e.symm := by simp
    have e3 : ((h.1.1.submatrix e.symm e.symm).map (cA D))ᵀ = ((h.1.1.map (cA D))ᵀ).submatrix e.symm e.symm := rfl
    rw [e2, e3, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
    exact h2
  · apply Subtype.ext
    apply Units.ext
    show (h.1.1.submatrix e.symm e.symm).submatrix e e = h.1.1
    simp

theorem mem_GfC_of_at (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (hJ : Wd.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (g : GA D X)
    (hg : GlobalTheory.TripleRead.toUX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v)) :
    g ∈ GfC X := by
  let u : AF D.host.F := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 1 0
  have h := hg u (by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v 0 = 0
    exact map_zero _)
  have key : ∀ z : AE D, infPart D (u • z) = infPart D z := by
    intro z
    rw [Algebra.smul_def, map_mul]
    exact one_mul _
  show infHom X g = 1
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (congrFun (congrFun h (e.symm i)) (e.symm j))
  rw [Matrix.smul_apply, key, Matrix.sub_apply, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h1
  have h2 : infPart D (Formalism.L2.Theta.mt X g (e (e.symm i)) (e (e.symm j))) = _ := h1
  rw [e.apply_symm_apply, e.apply_symm_apply] at h2
  refine h2.trans ?_
  by_cases c : i = j
  · subst c; simp
  · have c' : e.symm i ≠ e.symm j := fun k => c (e.symm.injective k)
    simp [c, c']

theorem kapX_eq (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (hJ' : J = D.host.xi0 • reindex e.symm e.symm X.gramᵀ) (g : GA D X) :
    GlobalTheory.SquareAgree.kapX X e.symm hJ' g = GlobalTheory.TripleRead.toUX X e hJ g := by
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.TripleRead.toUX_val]
  exact GlobalTheory.SquareAgree.mat_kapX X e.symm hJ' g

theorem toUX_map (θ : InfFam D) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau) (π : AE D →+* ℂ)
    (hπ : ∀ y, π y = conj (θ τ (infPart D y))) (g : GA D X) :
    (GlobalTheory.TripleRead.toUX X e hJ g).1.1.map π = ((infMat D.sp.cm.sig X.gram (θ τ) g).map (starRingEnd ℂ)).submatrix e e := by
  rw [GlobalTheory.TripleRead.toUX_val]
  ext i j
  exact hπ _

theorem piInf_of_conj (θ : InfFam D) (hθ : IsInfFam θ) {w : InfinitePlace D.host.F} (t : GlobalTheory.AdelicU.EmbOver D.host.E w)
    (τ : D.what₂.Tau) (hE : t.1 = (starRingEnd ℂ).comp (tauE D τ)) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf t y = conj (θ τ (infPart D y)) := by
  obtain ⟨t, ht⟩ := t
  dsimp only at hE
  subst hE
  exact GlobalTheory.ConjInfExp.piInf_eq θ hθ τ w ht y

theorem exists_line_at (θ : InfFam D) (hθ : IsInfFam θ) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Wd.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hξ : D.host.xi0 ≠ 0) (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w)
    (hemb : ∀ w, ∃ τ, ∀ x, (emb w).1 x = conj (tauE D τ x)) {r s : ℕ}
    (C : InfinitePlace D.host.F → Matrix (Fin k) (Ix r s) ℂ)
    (hC : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • Wd.J.map (emb w).1) (C w)) (w : InfinitePlace D.host.F) (Z : Mat r s)
    (hZ : Z ∈ upq r s) [DecidableEq (InfinitePlace D.host.F)] :
    ∃ γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J,
      (∃ τ, ∃ Y ∈ lieAt X τ, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t)) ∧
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd ∧ GlobalTheory.RealLift.IsGen emb C γ (Function.update (fun _ => 0) w Z) := by
  choose τ hτ using hemb
  have hE : ∀ w, (emb w).1 = (starRingEnd ℂ).comp (tauE D (τ w)) := fun w => RingHom.ext (hτ w)
  have hpi : ∀ w y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w) y = conj (θ (τ w) (infPart D y)) := fun w y =>
    piInf_of_conj θ hθ (emb w) (τ w) (hE w) y
  have hinj : ∀ w', w' ≠ w → τ w' ≠ τ w := fun w' hw k => hw (by
    have h1 := (emb w').2
    rw [hE, k, ← hE, (emb w).2] at h1
    rw [← w.mk_embedding, h1, InfinitePlace.mk_embedding])
  have hM : Complex.I • Wd.J.map (emb w).1 =
      (Complex.I * (emb w).1 D.host.xi0) • ((gramAt D X (τ w))ᴴ).submatrix e e := by
    rw [hJ]
    ext i j
    simp [gramAt, hτ, mul_assoc]
  obtain ⟨Y, hY, hexp⟩ := exists_lie_of_frame e (gramAt D X (τ w)) _
    (mul_ne_zero Complex.I_ne_zero ((map_ne_zero _).2 hξ)) (C w) (by rw [← hM]; exact hC w) Z hZ
  have hJ' : Wd.J = D.host.xi0 • reindex e.symm e.symm X.gramᵀ := hJ
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X (τ w) Y hθ hY e.symm Wd hJ'
  simp only [kapX_eq X e hJ hJ'] at hγt
  refine ⟨γ, ⟨τ w, Y, hY, hγt⟩, hγ, fun t w' => ?_⟩
  have hat := GlobalTheory.Mem.Lift.isAtTau_oneP hθ (show Y ∈ lieAt X (τ w) from hY) t
  have e1 := toUX_map θ X e hJ (τ w') _ (hpi w') (oneP θ X (τ w) Y t)
  rw [← hγt t] at e1
  refine (congrArg (· * C w') e1).trans ?_
  by_cases c : w' = w
  · subst c
    rw [hat.2.1, hexp, Function.update_self]
  · rw [hat.2.2 _ (hinj w' c), Function.update_of_ne c]
    simp

end Reading

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

theorem end_ext {U P ι : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup P] [Module ℂ P] {V N : ι → Type}
    [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)] [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (S : Submodule ℂ U) (pr : U →ₗ[ℂ] P) (hpr : S.map pr = ⊤) (SV : ∀ v, Submodule ℂ (V v)) (pv : ∀ v, V v →ₗ[ℂ] N v)
    (hpv : ∀ v, (SV v).map (pv v) = ⊤) (m : ∀ v, V v) (hm : ∀ v, m v ∈ SV v)
    (T T' : Module.End ℂ (P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens fun v => pv v (m v)))
    (h : ∀ f ∈ S, ∀ φ : ∀ v, V v, (∀ v, φ v ∈ SV v) → (∀ᶠ v in Filter.cofinite, φ v = m v) →
      T (pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT _ fun v => pv v (φ v)) =
        T' (pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT _ fun v => pv v (φ v))) : T = T' := by
  refine TensorProduct.ext' fun x y => ?_
  obtain ⟨f, hf, rfl⟩ : x ∈ S.map pr := hpr ▸ Submodule.mem_top
  refine LinearMap.congr_fun (LinearMap.ext_on (GlobalTheory.SmallThetaModules.pureT_span fun v => pv v (m v))
    (f := T ∘ₗ TensorProduct.mk ℂ _ _ (pr f)) (g := T' ∘ₗ TensorProduct.mk ℂ _ _ (pr f)) ?_) y
  rintro _ ⟨ξ, hξ, rfl⟩
  have h1 : ∀ v, ∃ φ ∈ SV v, pv v φ = ξ v ∧ (pv v (m v) = ξ v → φ = m v) := by
    intro v
    by_cases hv : pv v (m v) = ξ v
    · exact ⟨m v, hm v, hv, fun _ => rfl⟩
    · obtain ⟨φ, hφ, e⟩ : ξ v ∈ (SV v).map (pv v) := (hpv v) ▸ Submodule.mem_top
      exact ⟨φ, hφ, e, fun k => absurd k hv⟩
  choose φ hφ hφ1 hφ2 using h1
  have h2 : ∀ᶠ v in Filter.cofinite, φ v = m v := by
    have h3 : ∀ᶠ v in Filter.cofinite, ξ v = pv v (m v) := hξ
    filter_upwards [h3] with v b using hφ2 v b.symm
  have := h f hf φ hφ h2
  rw [funext hφ1] at this
  exact this


end Main

end GlobalTheory.TripleAssembly.Irred

end
