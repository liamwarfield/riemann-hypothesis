module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEquivCohomologyOfQuasiIsomorphism
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniversalCoefficientDegreeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniversalCoefficientDegreeZero
set_option autoImplicit false

open TensorProduct MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfUnit

theorem exists_unit_on_model : ∀ (R A₀ A₁ P₀ P₁ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] (d₀ : A₀ →ₗ[R] A₁) (a₀ : P₀ →ₗ[R] P₁) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (e : A₀), ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → d₀ e = 0 → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] A₀) (d₀.lTensor M) (ψ₀.lTensor M)) → (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x) → ∃ u : P₀, a₀ u = 0 ∧ ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧ ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x := by
  intro R A₀ A₁ P₀ P₁ _ _ _ _ _ _ _ _ _ d₀ a₀ ψ₀ ψ₁ e hchain hde hq he
  have lid_nat : ∀ {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
      (f : X →ₗ[R] Y) (t : R ⊗[R] X),
      f (TensorProduct.lid R X t) = TensorProduct.lid R Y (f.lTensor R t) := by
    intro X Y _ _ _ _ f t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨x, y, hx, hxy⟩ := (hq R).2 ((1 : R) ⊗ₜ[R] e) (by simp [hde])
  have hxe : ψ₀.lTensor R x = (1 : R) ⊗ₜ[R] e := by
    simpa [sub_eq_zero] using hxy
  refine ⟨TensorProduct.lid R P₀ x, ?_, ?_⟩
  · rw [lid_nat, hx, map_zero]
  have hu : ψ₀ (TensorProduct.lid R P₀ x) = e := by
    rw [lid_nat, hxe]; simp
  set u := TensorProduct.lid R P₀ x with hudef
  have hu0 : a₀ u = 0 := by rw [hudef, lid_nat, hx, map_zero]
  intro M _ _
  have hψ : ∀ m : M, ψ₀.lTensor M (m ⊗ₜ[R] u) = m ⊗ₜ[R] e := by
    intro m; simp [hu]
  refine ⟨?_, ?_⟩
  · intro m m' h
    apply (he M).1
    have h' : m ⊗ₜ[R] u = m' ⊗ₜ[R] u := h
    show m ⊗ₜ[R] e = m' ⊗ₜ[R] e
    rw [← hψ, ← hψ, h']
  · intro z hz
    have hd : d₀.lTensor M (ψ₀.lTensor M z) = 0 := by
      have h1 : (d₀.lTensor M) ∘ₗ (ψ₀.lTensor M) = (ψ₁.lTensor M) ∘ₗ (a₀.lTensor M) := by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hchain]
      have h2 := LinearMap.congr_fun h1 z
      simpa [hz] using h2
    obtain ⟨m, hm⟩ := (he M).2 _ hd
    refine ⟨m, ?_⟩
    have ha : a₀.lTensor M (z - m ⊗ₜ[R] u) = 0 := by
      simp [hz, hu0]
    have hp : ψ₀.lTensor M (z - m ⊗ₜ[R] u) = 0 := by
      rw [map_sub, hψ, hm, sub_self]
    obtain ⟨y', hy'⟩ := (hq M).1 _ ha ⟨0, by simp [hp]⟩
    have : z - m ⊗ₜ[R] u = 0 := by
      rw [← hy']; simp
    exact (sub_eq_zero.mp this).symm

end GlobalTheory.CompanionTheory.PerfUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniversalCoefficientDegreeZeroStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_coefficient_degree_zero : ∀ (R A₀ A₁ P₀ P₁ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] (d₀ : A₀ →ₗ[R] A₁) (a₀ : P₀ →ₗ[R] P₁) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (e : A₀), ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → d₀ e = 0 → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] A₀) (d₀.lTensor M) (ψ₀.lTensor M)) → (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x) → ∃ u : P₀, a₀ u = 0 ∧ ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧ ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x := by
  first | exact @GlobalTheory.CompanionTheory.PerfUnit.exists_unit_on_model | exact GlobalTheory.CompanionTheory.PerfUnit.exists_unit_on_model | (intros; apply GlobalTheory.CompanionTheory.PerfUnit.exists_unit_on_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjective
open TensorProduct

namespace GlobalTheory.CompanionTheory.FlatCoker

theorem lTensor_rTensor_comm {R P Q X Y : Type} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (i : P →ₗ[R] Q) (g : X →ₗ[R] Y) (t : P ⊗[R] X) :
    g.lTensor Q (i.rTensor X t) = i.rTensor Y (g.lTensor P t) := by
  have h1 := LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor P i g) t
  have h2 := LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor P i g) t
  exact h1.trans h2.symm

theorem flat_quotient_range_of_lTensor_injective
    (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Flat R B] (f : A →ₗ[R] B)
    (hf : ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) :
    Module.Flat R (B ⧸ LinearMap.range f) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  have hRrow := lTensor_exact R (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective (LinearMap.range f))
  have hIrow := lTensor_exact (↥I) (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective (LinearMap.range f))
  have hAcol := rTensor_exact A (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
  have hBcol := rTensor_exact B (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
  have hBinj : Function.Injective (LinearMap.rTensor B I.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype I)
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (↥I)
    (Submodule.mkQ_surjective (LinearMap.range f)) z
  rw [← lTensor_rTensor_comm I.subtype (LinearMap.range f).mkQ y] at hz
  obtain ⟨x, hx⟩ := (hRrow _).mp hz
  have hq : LinearMap.lTensor (R ⧸ I) f (LinearMap.rTensor A I.mkQ x) = 0 := by
    rw [lTensor_rTensor_comm I.mkQ f x, hx]
    exact (hBcol _).mpr ⟨y, rfl⟩
  have hq0 : LinearMap.rTensor A I.mkQ x = 0 :=
    (injective_iff_map_eq_zero (LinearMap.lTensor (R ⧸ I) f)).mp (hf (R ⧸ I)) _ hq
  obtain ⟨w, rfl⟩ := (hAcol x).mp hq0
  have hyw : LinearMap.lTensor (↥I) f w = y := by
    apply hBinj
    rw [← hx]
    exact (lTensor_rTensor_comm I.subtype f w).symm
  rw [← hyw]
  exact (hIrow _).mpr ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.FlatCoker
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjectiveStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_of_universally_injective : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [Module.Flat R B] (f : A →ₗ[R] B), (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) → Module.Flat R (B ⧸ LinearMap.range f) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | exact GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFreeKernelSplitting
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFreeKernelSplitting
open TensorProduct

namespace GlobalTheory.CompanionTheory.LocalSplit

theorem injective_of_basis_image {k V U ι : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U] (b : Module.Basis ι k V) (g : V →ₗ[k] U)
    (h : LinearIndependent k (g ∘ b)) : Function.Injective g := by
  have hg : ⇑g = (Finsupp.linearCombination k (g ∘ b)) ∘ b.repr := by
    funext x
    conv_lhs => rw [← b.linearCombination_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  rw [hg]
  exact (show Function.Injective (Finsupp.linearCombination k (g ∘ b)) from h).comp b.repr.injective

theorem ker_facts {A Q : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] (s : ℕ)
    (f : (Fin s → A) →ₗ[A] Q) (p : Q →ₗ[A] (Fin s → A)) (h : p ∘ₗ f = LinearMap.id) :
    Module.Free A (LinearMap.ker p) ∧ Module.Finite A (LinearMap.ker p) ∧
      s + Module.finrank A (LinearMap.ker p) = Module.finrank A Q := by
  have hpf : ∀ y, p (f y) = y := fun y => LinearMap.congr_fun h y
  let e : Q ≃ₗ[A] (LinearMap.ker p) × (Fin s → A) := LinearEquiv.ofLinear
    (LinearMap.prod
      (LinearMap.codRestrict (LinearMap.ker p) (LinearMap.id - f ∘ₗ p)
        (fun x => by simp [hpf]))
      p)
    (LinearMap.coprod (LinearMap.ker p).subtype f)
    (by
      ext x <;> simp [hpf])
    (by
      ext x
      simp)
  have hproj : Module.Projective A ((LinearMap.ker p) × (Fin s → A)) :=
    Module.Projective.of_equiv e
  have hker : Module.Projective A (LinearMap.ker p) :=
    Module.Projective.of_split (LinearMap.inl A (LinearMap.ker p) (Fin s → A))
      (LinearMap.fst A (LinearMap.ker p) (Fin s → A)) (by ext; simp)
  have hfin : Module.Finite A (LinearMap.ker p) :=
    Module.Finite.of_surjective (LinearMap.fst A (LinearMap.ker p) (Fin s → A) ∘ₗ e.toLinearMap)
      (fun y => ⟨e.symm (y, 0), by simp⟩)
  have hfree : Module.Free A (LinearMap.ker p) := Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, hfin, ?_⟩
  have := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_fin_fun] at this
  omega

theorem exists_section {A Q P : Type} [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup P] [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P]
    [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ (s : ℕ) (f : (Fin s → A) →ₗ[A] Q) (t : P →ₗ[A] (Fin s → A)),
      t ∘ₗ (d ∘ₗ f) = LinearMap.id ∧
      s + Module.finrank (IsLocalRing.ResidueField A)
        (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = Module.finrank A Q := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl
    (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A)))
  let v := Module.finBasis (IsLocalRing.ResidueField A) C
  have hsurj : Function.Surjective (TensorProduct.mk A (IsLocalRing.ResidueField A) Q 1) :=
    TensorProduct.mk_surjective A Q (IsLocalRing.ResidueField A) IsLocalRing.residue_surjective
  choose a ha using fun i => hsurj (v i : (IsLocalRing.ResidueField A) ⊗[A] Q)
  let f : (Fin (Module.finrank (IsLocalRing.ResidueField A) C) → A) →ₗ[A] Q :=
    Fintype.linearCombination A a
  have hf : ∀ i, f (Pi.single i 1) = a i := by
    intro i
    simp [f, Fintype.linearCombination_apply_single]
  have hgk : LinearMap.ker ((d.baseChange (IsLocalRing.ResidueField A)) ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx1 : (x : (IsLocalRing.ResidueField A) ⊗[A] Q) ∈
        LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A)) := hx
    have := hC.disjoint.le_bot ⟨hx1, x.2⟩
    simpa using this
  have hinj : Function.Injective ((d ∘ₗ f).lTensor (IsLocalRing.ResidueField A)) := by
    rw [← LinearMap.baseChange_eq_ltensor]
    apply injective_of_basis_image
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) (Pi.basisFun A _))
    have hl := v.linearIndependent.map' _ hgk
    have key : ⇑((d ∘ₗ f).baseChange (IsLocalRing.ResidueField A)) ∘
        ⇑(Algebra.TensorProduct.basis (IsLocalRing.ResidueField A)
          (Pi.basisFun A (Fin (Module.finrank (IsLocalRing.ResidueField A) C)))) =
        ⇑((d.baseChange (IsLocalRing.ResidueField A)) ∘ₗ C.subtype) ∘ ⇑v := by
      funext i
      have h2 := ha i
      simp only [TensorProduct.mk_apply] at h2
      simp [Algebra.TensorProduct.basis_apply, hf, ← h2]
    rw [key]
    exact hl
  obtain ⟨t, ht⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective (d ∘ₗ f)).2 hinj
  refine ⟨_, f, t, ht, ?_⟩
  rw [← Module.finrank_baseChange (R := IsLocalRing.ResidueField A) (S := A) (M' := Q),
    ← Submodule.finrank_add_eq_of_isCompl hC]
  omega

theorem exists_idempotent_of_residueField (A Q P : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [Module.Finite A Q]
    [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ r : P →ₗ[A] Q, (r ∘ₗ d ∘ₗ r ∘ₗ d = r ∘ₗ d) ∧ Module.Free A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.Finite A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.finrank A (LinearMap.ker (r ∘ₗ d)) =
        Module.finrank (IsLocalRing.ResidueField A)
          (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) := by
  obtain ⟨s, f, t, ht, hs⟩ := exists_section d
  have hpf : ∀ y, t (d (f y)) = y := fun y => LinearMap.congr_fun ht y
  have hfinj : Function.Injective f := fun x y hxy => by
    rw [← hpf x, ← hpf y, hxy]
  have hker : LinearMap.ker ((f ∘ₗ t) ∘ₗ d) = LinearMap.ker (t ∘ₗ d) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact ⟨fun h => hfinj (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  obtain ⟨h1, h2, h3⟩ := ker_facts s f (t ∘ₗ d) ht
  refine ⟨f ∘ₗ t, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [hpf]
  · rw [hker]; exact h1
  · rw [hker]; exact h2
  · rw [hker]; omega

end GlobalTheory.CompanionTheory.LocalSplit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFreeKernelSplittingStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_free_kernel_splitting : ∀ (A Q P : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P), ∃ r : P →ₗ[A] Q, (r ∘ₗ d ∘ₗ r ∘ₗ d = r ∘ₗ d) ∧ Module.Free A (LinearMap.ker (r ∘ₗ d)) ∧ Module.Finite A (LinearMap.ker (r ∘ₗ d)) ∧ Module.finrank A (LinearMap.ker (r ∘ₗ d)) = Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField | exact GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField | (intros; apply GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquiv
open TensorProduct

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology

theorem ker_baseChange_tower (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A]
    [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) :
    Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  let e₁ := AlgebraTensorModule.cancelBaseChange R A K K Q
  let e₂ := AlgebraTensorModule.cancelBaseChange R A K K P
  have comm : ∀ x, e₂ (((d.baseChange A).baseChange K) x) = (d.baseChange K) (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy]
      | tmul a q =>
        simp [e₁, e₂, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  refine ⟨LinearEquiv.ofSubmodules e₁ _ _ ?_⟩
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := comm x
    rw [hx, map_zero] at this
    exact this.symm
  · intro hy
    refine ⟨e₁.symm y, ?_, by simp⟩
    apply e₂.injective
    rw [comm, map_zero]
    simpa using hy

end GlobalTheory.CompanionTheory.PerfectFirstCohomology
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquivStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_base_change_tower_equiv : ∀ (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P), Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower | (intros; apply GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingKernelBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingKernelBaseChange
open TensorProduct

namespace GlobalTheory.CompanionTheory.RegularLocal

theorem regular_of_regular_at_maximal : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  intro R Q P _ _ _ _ _ _ _ _ _ d h
  have hex : Function.Exact d (LinearMap.range d).mkQ := LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ := Submodule.mkQ_surjective _

  have hloc : ∀ (p : Ideal R) [p.IsMaximal], Module.Flat (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d)) := by
    intro p _
    obtain ⟨r, hr⟩ := h p
    set A := Localization.AtPrime p
    set dA := d.baseChange A with hdA
    set πA := (LinearMap.range d).mkQ.baseChange A with hπA
    have hexA : Function.Exact dA πA := by
      have := lTensor_exact A hex hsurj
      simpa [hdA, hπA, LinearMap.baseChange_eq_ltensor] using this
    have hsA : Function.Surjective πA := by
      have := LinearMap.lTensor_surjective A hsurj
      simpa [hπA, LinearMap.baseChange_eq_ltensor] using this
    let e : A ⊗[R] P →ₗ[A] A ⊗[R] P := LinearMap.id - dA ∘ₗ r
    have he : ∀ x ∈ LinearMap.range dA, e x = 0 := by
      rintro _ ⟨y, rfl⟩
      have := LinearMap.congr_fun hr y
      simp only [LinearMap.comp_apply] at this
      simp [e, this]
    let s : A ⊗[R] (P ⧸ LinearMap.range d) →ₗ[A] A ⊗[R] P :=
      ((LinearMap.range dA).liftQ e (fun x hx => he x hx)) ∘ₗ
        (hexA.linearEquivOfSurjective hsA).symm.toLinearMap
    have hs : ∀ x, s (πA x) = e x := by
      intro x
      have : (hexA.linearEquivOfSurjective hsA).symm (πA x) = (LinearMap.range dA).mkQ x := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
      rfl
    have hsec : πA ∘ₗ s = LinearMap.id := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨x, rfl⟩ := hsA z
      rw [LinearMap.comp_apply, hs, LinearMap.id_apply]
      have h0 : πA (dA (r x)) = 0 := hexA.apply_apply_eq_zero (r x)
      simp [e, h0]
    exact Module.Flat.of_retract s πA hsec
  have hflat : Module.Flat R (P ⧸ LinearMap.range d) :=
    Module.flat_of_isLocalized_maximal R (P ⧸ LinearMap.range d)
      (fun p _ => Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d))
      (fun p _ => TensorProduct.mk R (Localization.AtPrime p) (P ⧸ LinearMap.range d) 1)
      (fun p _ => by
        have := hloc p
        exact Module.Flat.trans R (Localization.AtPrime p) _)
  have hfp : Module.FinitePresentation R (P ⧸ LinearMap.range d) := by
    have : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
    refine Module.finitePresentation_of_surjective (LinearMap.range d).mkQ hsurj ?_
    rw [Submodule.ker_mkQ]
    exact Module.Finite.iff_fg.mp inferInstance
  have hproj : Module.Projective R (P ⧸ LinearMap.range d) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id hsurj
  let f : P →ₗ[R] P := LinearMap.id - s ∘ₗ (LinearMap.range d).mkQ
  have hf : ∀ x, f x ∈ LinearMap.range d := by
    intro x
    rw [← Submodule.ker_mkQ (LinearMap.range d), LinearMap.mem_ker]
    have := LinearMap.congr_fun hs ((LinearMap.range d).mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this,
      sub_self]
  let g : P →ₗ[R] LinearMap.range d := f.codRestrict _ hf
  have hg : ∀ y : LinearMap.range d, f y = y := by
    rintro ⟨_, y, rfl⟩
    have h0 : (LinearMap.range d).mkQ (d y) = 0 := hex.apply_apply_eq_zero y
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero,
      sub_zero]
  have hrp : Module.Projective R (LinearMap.range d) :=
    Module.Projective.of_split (LinearMap.range d).subtype g (by
      ext y
      simpa [g] using hg y)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  refine ⟨t ∘ₗ g, ?_⟩
  ext y
  have h1 : g (d y) = d.rangeRestrict y := by
    apply Subtype.ext
    simpa [g] using hg (d.rangeRestrict y)
  have h2 := LinearMap.congr_fun ht (d.rangeRestrict y)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
  have h3 : d (t (d.rangeRestrict y)) = d y := by
    have := congrArg Subtype.val h2
    simpa using this
  simp [h1, h3]

end GlobalTheory.CompanionTheory.RegularLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingKernelBaseChangeStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_splitting_kernel_base_change : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  first | exact @GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal | exact GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal | (intros; apply GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RetractBaseChangeKernelCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RetractBaseChangeKernelCompatible
open TensorProduct

namespace GlobalTheory.CompanionTheory.Retract

theorem constants_of_retract :
    ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  intro R R' M A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ _ _ i j d₀ d' E₀ E₁ e hji hcomm hfree hker
  have htm : ∀ r : R', r • E₀ (1 ⊗ₜ e) = E₀ (r ⊗ₜ[R] e) := by
    intro r
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hinjR : ∀ r : R', r ⊗ₜ[R] e = 0 → r = 0 := by
    intro r hr
    apply hfree
    rw [htm, hr, map_zero]
  have hkerR : ∀ y : R' ⊗[R] A₀, d₀.baseChange R' y = 0 → ∃ r : R', r ⊗ₜ[R] e = y := by
    intro y hy
    obtain ⟨r, hr⟩ := hker (E₀ y) (by rw [← hcomm, hy, map_zero])
    exact ⟨r, E₀.injective (by rw [← htm, hr])⟩
  have hji' : ∀ m : M, j (i m) = m := fun m => by
    rw [← LinearMap.comp_apply, hji, LinearMap.id_apply]
  have hret : ∀ x : M ⊗[R] A₀, j.rTensor A₀ (i.rTensor A₀ x) = x := by
    intro x
    rw [← LinearMap.rTensor_comp_apply, hji, LinearMap.rTensor_id_apply]
  have hnat : ∀ x : M ⊗[R] A₀,
      d₀.baseChange R' (i.rTensor A₀ x) = i.rTensor A₁ (d₀.lTensor M x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m a => simp [LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine ⟨?_, ?_⟩
  · intro m m' h
    have h0 : m ⊗ₜ[R] e = m' ⊗ₜ[R] e := h
    have h1 : (i m - i m') ⊗ₜ[R] e = 0 := by
      have h2 := congrArg (i.rTensor A₀) h0
      simp only [LinearMap.rTensor_tmul] at h2
      rw [TensorProduct.sub_tmul, h2, sub_self]
    have h3 : i m = i m' := sub_eq_zero.mp (hinjR _ h1)
    rw [← hji' m, ← hji' m', h3]
  · intro x hx
    obtain ⟨r, hr⟩ := hkerR (i.rTensor A₀ x) (by rw [hnat, hx, map_zero])
    refine ⟨j r, ?_⟩
    rw [← hret x, ← hr, LinearMap.rTensor_tmul]

end GlobalTheory.CompanionTheory.Retract
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RetractBaseChangeKernelCompatibleStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.retract_base_change_kernel_compatible : ∀ (R R' M A₀ A₁ B₀ B₁ : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup B₀] [Module R' B₀] [AddCommGroup B₁] [Module R' B₁] (i : M →ₗ[R] R') (j : R' →ₗ[R] M) (d₀ : A₀ →ₗ[R] A₁) (d' : B₀ →ₗ[R'] B₁) (E₀ : R' ⊗[R] A₀ ≃ₗ[R'] B₀) (E₁ : R' ⊗[R] A₁ ≃ₗ[R'] B₁) (e : A₀), j ∘ₗ i = LinearMap.id → (∀ x, E₁ (d₀.baseChange R' x) = d' (E₀ x)) → (∀ r : R', r • E₀ (1 ⊗ₜ e) = 0 → r = 0) → (∀ z, d' z = 0 → ∃ r : R', r • E₀ (1 ⊗ₜ e) = z) → Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x := by
  first | exact @GlobalTheory.CompanionTheory.Retract.constants_of_retract | exact GlobalTheory.CompanionTheory.Retract.constants_of_retract | (intros; apply GlobalTheory.CompanionTheory.Retract.constants_of_retract <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearMapZeroOfInjectiveFullRank
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearMapZeroOfInjectiveFullRank
open TensorProduct

namespace GlobalTheory.CompanionTheory.Perf

theorem map_eq_zero_of_comp_injective_of_finrank_eq :
    ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N]
      [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ)
      (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N),
      Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by
  intro A W N _ _ _ _ _ _ _ _ _ g φ f hg hφ hf
  classical
  let e : W ≃ₗ[A] (Fin g → A) := (Module.finBasisOfFinrankEq A W hg).equivFun
  let M : Matrix (Fin g) (Fin g) A := LinearMap.toMatrix' (e.toLinearMap ∘ₗ φ)
  have hM : ∀ v, Matrix.mulVec M v = e (φ v) := fun v => by
    change Matrix.toLin' M v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  have hinj : Function.Injective M.mulVec := by
    intro v v' h
    rw [hM, hM] at h
    exact hφ (e.injective h)
  have hdet : M.det ∈ nonZeroDivisors A :=
    Matrix.nonsingular_iff_det_mem_nonZeroDivisors.mp
      (Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hinj))
  have hkill : ∀ w, M.det • f w = 0 := by
    intro w
    have h1 : φ (M.cramer (e w)) = M.det • w := by
      apply e.injective
      rw [← hM, Matrix.mulVec_cramer, map_smul]
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun hf _
  ext w
  apply (Module.Free.chooseBasis A N).repr.injective
  ext i
  have h2 := congrArg (fun n => (Module.Free.chooseBasis A N).repr n i) (hkill w)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h2
  simpa using (mul_left_mem_nonZeroDivisors_eq_zero_iff hdet).mp h2

end GlobalTheory.CompanionTheory.Perf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearMapZeroOfInjectiveFullRankStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_map_zero_of_injective_full_rank : ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N] [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ) (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N), Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq | exact GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq | (intros; apply GlobalTheory.CompanionTheory.Perf.map_eq_zero_of_comp_injective_of_finrank_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRank
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRank
open TensorProduct

namespace GlobalTheory.CompanionTheory.KerLocal

theorem ker_baseChange_localization_free :
    ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
      (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) →
      Module.Projective R (LinearMap.ker d) →
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) →
      ∀ (p : Ideal R) [p.IsPrime],
        Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.Finite (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.finrank (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  intro R Q P _ _ _ _ _ d g hfin hproj hrk p _
  have hflat : Module.Flat R (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) p.primeCompl
  let e1 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LinearMap.ker (d.baseChange (Localization.AtPrime p)) :=
    LinearMap.tensorKerEquiv (Localization.AtPrime p) (Localization.AtPrime p) d
  let e2 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LocalizedModule p.primeCompl (LinearMap.ker d) :=
    (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl (LinearMap.ker d))).equiv
  have hfree : Module.Free (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] LinearMap.ker d) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.Free.of_equiv e1, Module.Finite.equiv e1, ?_⟩
  rw [← e1.finrank_eq, e2.finrank_eq]
  exact hrk ⟨p, inferInstance⟩

end GlobalTheory.CompanionTheory.KerLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRankStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_free_at_primes_of_constant_rank : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) → Module.Projective R (LinearMap.ker d) → (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) → ∀ (p : Ideal R) [p.IsPrime], Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.Finite (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.finrank (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  first | exact @GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | exact GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | (intros; apply GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology

theorem proj_coker (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
    [Module.Finite R P₀] [Module.Finite R P₁] [Module.Projective R P₀] [Module.Projective R P₁]
    (a₀ : P₀ →ₗ[R] P₁) (u : P₀) (hu : a₀ u = 0)
    (hU : ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧
      ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x) :
    Module.Projective R (P₁ ⧸ LinearMap.range a₀) := by
  have hle : Submodule.span R {u} ≤ LinearMap.ker a₀ := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hu
  have hcomp : (Submodule.span R {u}).liftQ a₀ hle ∘ₗ (Submodule.span R {u}).mkQ = a₀ :=
    Submodule.liftQ_mkQ _ _ _
  have hflat : Module.Flat R (P₁ ⧸ LinearMap.range ((Submodule.span R {u}).liftQ a₀ hle)) := by
    apply GlobalTheory.T.flat_quotient_of_universally_injective
    intro M _ _
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective M (Submodule.mkQ_surjective (Submodule.span R {u})) z
    have hx : a₀.lTensor M x = 0 := by
      rw [← hcomp, LinearMap.lTensor_comp_apply]
      exact hz
    obtain ⟨m, rfl⟩ := (hU M).2 x hx
    rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self u), TensorProduct.tmul_zero]
  rw [Submodule.range_liftQ] at hflat
  haveI := hflat
  haveI : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  haveI : Module.FinitePresentation R (P₁ ⧸ LinearMap.range a₀) :=
    Module.finitePresentation_of_surjective (LinearMap.range a₀).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map a₀)
  exact Module.Flat.projective_of_finitePresentation

theorem local_regular (A Q P : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup P]
    [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) (g : ℕ)
    (h1 : Module.Free A (LinearMap.ker d)) (h2 : Module.Finite A (LinearMap.ker d))
    (h3 : Module.finrank A (LinearMap.ker d) = g)
    (h4 : Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = g) :
    ∃ r : P →ₗ[A] Q, d ∘ₗ r ∘ₗ d = d := by
  obtain ⟨r, hidem, hfree, hfin, hrank⟩ := GlobalTheory.T.local_free_kernel_splitting A Q P d
  refine ⟨r, ?_⟩
  have hrank' : Module.finrank A (LinearMap.ker (r ∘ₗ d)) = g := hrank.trans h4
  have hle : LinearMap.ker d ≤ LinearMap.ker (r ∘ₗ d) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]
  let b := Module.finBasisOfFinrankEq A (LinearMap.ker d) h3
  let φ : (Fin g → A) →ₗ[A] LinearMap.ker (r ∘ₗ d) :=
    Submodule.inclusion hle ∘ₗ b.equivFun.symm.toLinearMap
  have hφ : Function.Injective φ := (Submodule.inclusion_injective hle).comp b.equivFun.symm.injective
  have hzero : (d ∘ₗ (LinearMap.ker (r ∘ₗ d)).subtype) ∘ₗ φ = 0 := LinearMap.ext fun v => by
    change d ((b.equivFun.symm v : LinearMap.ker d) : Q) = 0
    exact LinearMap.mem_ker.mp (b.equivFun.symm v).2
  have key := GlobalTheory.T.linear_map_zero_of_injective_full_rank A _ P g φ
    (d ∘ₗ (LinearMap.ker (r ∘ₗ d)).subtype) hrank' hφ hzero
  ext x
  have hx : x - r (d x) ∈ LinearMap.ker (r ∘ₗ d) := by
    have h := LinearMap.congr_fun hidem x
    simp only [LinearMap.comp_apply] at h
    rw [LinearMap.mem_ker, map_sub, LinearMap.comp_apply, LinearMap.comp_apply, h, sub_self]
  have h := LinearMap.congr_fun key ⟨_, hx⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply, map_sub, sub_eq_zero] at h
  simp only [LinearMap.comp_apply]
  exact h.symm

theorem regular_of_fibres (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
    [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P) (g : ℕ)
    (hVB : VB R (LinearMap.ker d) g)
    (hfib : ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (LinearMap.ker (d.baseChange k)) = g) :
    ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  obtain ⟨hfin, hproj, hrank⟩ := hVB
  apply GlobalTheory.T.local_splitting_kernel_base_change R Q P d
  intro p hp
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.kernel_free_at_primes_of_constant_rank R Q P d g hfin hproj hrank p
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Q) :=
    Module.Flat.baseChange R _ Q
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] P) :=
    Module.Flat.baseChange R _ P
  haveI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Q) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] P) :=
    Module.free_of_flat_of_isLocalRing
  refine GlobalTheory.CompanionTheory.PerfectFirstCohomology.local_regular (Localization.AtPrime p) _ _
    (d.baseChange (Localization.AtPrime p)) g h1 h2 h3 ?_
  obtain ⟨e⟩ := GlobalTheory.T.kernel_base_change_tower_equiv R (Localization.AtPrime p)
    (IsLocalRing.ResidueField (Localization.AtPrime p)) Q P d
  rw [e.finrank_eq]
  exact hfib _

theorem stein_univ (R C : Type) [CommRing R] [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')]
    (F : C ⥤ CommAlgCat.{0} R) (hS : SteinU F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective (fun m : M ↦ m ⊗ₜ[R] (1 : C0 F)) ∧
      ∀ x : M ⊗[R] C0 F, (d0 F).lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] (1 : C0 F) = x := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun x y => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  haveI : IsScalarTower R Rᵐᵒᵖ M := ⟨fun r s m => mul_smul r (MulOpposite.unop s) m⟩
  haveI : SMulCommClass R Rᵐᵒᵖ M := ⟨fun r s m => smul_comm r (MulOpposite.unop s) m⟩
  obtain ⟨F', m, hF'⟩ := hS (TrivSqZeroExt R M)
  obtain ⟨E₀, E₁, E₂, h0, -, -, h01, -⟩ :=
    GlobalTheory.T.cochain_base_change_equivalences R (TrivSqZeroExt R M) C F F' m
  have hone : E₀ (1 ⊗ₜ[R] (1 : GlobalTheory.CatCoh.C0 F)) = 1 := by
    rw [h0]
    funext T
    first
      | exact map_one _
      | simp
  refine GlobalTheory.T.retract_base_change_kernel_compatible R (TrivSqZeroExt R M) M _ _ _ _
    (TrivSqZeroExt.inrHom R M) (TrivSqZeroExt.sndHom R M) (GlobalTheory.CatCoh.d0 F)
    (GlobalTheory.CatCoh.d0 F') E₀ E₁ 1 (LinearMap.ext fun _ => rfl) h01 ?_ ?_
  · intro r hr
    rw [hone, ← Algebra.algebraMap_eq_smul_one] at hr
    exact hF'.2 (hr.trans (map_zero _).symm)
  · intro z hz
    obtain ⟨r, hr⟩ := (hF'.1 z).mp hz
    exact ⟨r, by rw [hone, ← Algebra.algebraMap_eq_smul_one, ← Algebra.linearMap_apply]; exact hr⟩

theorem qiso_transport {R S A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing S]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module S A₀'] [Module S A₁'] [Module S A₂'] [Module S B₀'] [Module S B₁'] [Module S B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[S] A₁'} {a₁' : A₁' →ₗ[S] A₂'} {b₀' : B₀' →ₗ[S] B₁'} {b₁' : B₁' →ₗ[S] B₂'} {f' : A₁' →ₗ[S] B₁'}
    (h : QIsoAt a₀ a₁ b₀ b₁ f) (ε₀ : A₀ ≃+ A₀') (ε₁ : A₁ ≃+ A₁') (ε₂ : A₂ ≃+ A₂')
    (η₀ : B₀ ≃+ B₀') (η₁ : B₁ ≃+ B₁') (η₂ : B₂ ≃+ B₂')
    (h0 : ∀ y, a₀' (ε₀ y) = ε₁ (a₀ y)) (h1 : ∀ x, a₁' (ε₁ x) = ε₂ (a₁ x))
    (k0 : ∀ y, b₀' (η₀ y) = η₁ (b₀ y)) (k1 : ∀ x, b₁' (η₁ x) = η₂ (b₁ x))
    (hf : ∀ x, f' (ε₁ x) = η₁ (f x)) : QIsoAt a₀' a₁' b₀' b₁' f' := by
  unfold MainStatements.Hodge.QIsoAt at h ⊢
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun x' hx' ⟨y', hy'⟩ => ?_, fun z' hz' => ?_⟩
  · have ha : a₁ (ε₁.symm x') = 0 := by
      apply ε₂.injective
      rw [← h1, ε₁.apply_symm_apply, hx', map_zero]
    have hb : b₀ (η₀.symm y') = f (ε₁.symm x') := by
      apply η₁.injective
      rw [← k0, ← hf, η₀.apply_symm_apply, ε₁.apply_symm_apply, hy']
    obtain ⟨y, hy⟩ := hA _ ha ⟨_, hb⟩
    exact ⟨ε₀ y, by rw [h0, hy, ε₁.apply_symm_apply]⟩
  · have hz : b₁ (η₁.symm z') = 0 := by
      apply η₂.injective
      rw [← k1, η₁.apply_symm_apply, hz', map_zero]
    obtain ⟨x, y, hx, hxy⟩ := hB _ hz
    refine ⟨ε₁ x, η₀ y, by rw [h1, hx, map_zero], ?_⟩
    rw [hf, k0, ← hxy, map_sub, η₁.apply_symm_apply]

theorem lid_natural {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (h : X →ₗ[R] Y) (y : R ⊗[R] X) : h (TensorProduct.lid R X y) = TensorProduct.lid R Y (h.lTensor R y) := by
  induction y with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem qiso_lid {R A₀ A₁ A₂ B₀ B₁ B₂ : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    (h : QIsoAt (a₀.lTensor R) (a₁.lTensor R) (b₀.lTensor R) (b₁.lTensor R) (f.lTensor R)) :
    QIsoAt a₀ a₁ b₀ b₁ f :=
  qiso_transport h (TensorProduct.lid R A₀).toAddEquiv (TensorProduct.lid R A₁).toAddEquiv
    (TensorProduct.lid R A₂).toAddEquiv (TensorProduct.lid R B₀).toAddEquiv
    (TensorProduct.lid R B₁).toAddEquiv (TensorProduct.lid R B₂).toAddEquiv
    (lid_natural a₀) (lid_natural a₁) (lid_natural b₀) (lid_natural b₁) (lid_natural f)

section Core

variable {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)

theorem mem_Z1_iff_cocycle {S : Type} [CommRing S] (G : C ⥤ CommAlgCat.{0} S) (z : C1 G) : z ∈ Z1 G ↔ d1 G z = 0 := by
  rw [GlobalTheory.CatCoh.commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]


variable {F a₀ a₁ ψ₀ ψ₁ ψ₂} in
theorem ker_equiv_H1 (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂) (hdπ : d ∘ₗ (LinearMap.range a₀).mkQ = a₁)
    (hp : QIsoAt a₀ a₁ (d0 F) (d1 F) ψ₁) : Nonempty (LinearMap.ker d ≃ₗ[R] H1 F) := by
  refine GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism R P₀ P₁ P₂ (P₁ ⧸ LinearMap.range a₀) _ _ _ a₀ a₁
    (LinearMap.range a₀).mkQ d (GlobalTheory.CatCoh.Z1 F)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne F))
    (GlobalTheory.CatCoh.d1 F) ψ₁ ψ₀ (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range a₀) hdπ
    (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle F) ?_ (fun y => LinearMap.congr_fun c0 y) ?_
  · intro x hx
    rw [← LinearMap.comp_apply (GlobalTheory.CatCoh.d1 F) ψ₁, ← c1, LinearMap.comp_apply, hx, map_zero]
  · rwa [LinearMap.subtype_comp_codRestrict]


variable {F a₀ a₁ ψ₀ ψ₁ ψ₂} in
theorem ker_equiv_base {k : Type} [CommRing k] [Algebra R k] (G : C ⥤ CommAlgCat.{0} k)
    (E₀ : k ⊗[R] C0 F ≃ₗ[k] C0 G) (E₁ : k ⊗[R] C1 F ≃ₗ[k] C1 G) (E₂ : k ⊗[R] C2 F ≃ₗ[k] C2 G)
    (h01 : ∀ x, E₁ ((d0 F).baseChange k x) = d0 G (E₀ x)) (h12 : ∀ x, E₂ ((d1 F).baseChange k x) = d1 G (E₁ x))
    (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂) (hdπ : d ∘ₗ (LinearMap.range a₀).mkQ = a₁)
    (hq : QIsoAt (a₀.lTensor k) (a₁.lTensor k) ((d0 F).lTensor k) ((d1 F).lTensor k) (ψ₁.lTensor k)) :
    Nonempty (LinearMap.ker (d.baseChange k) ≃ₗ[k] H1 G) := by
  refine GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism k (k ⊗[R] P₀) (k ⊗[R] P₁) (k ⊗[R] P₂)
    (k ⊗[R] (P₁ ⧸ LinearMap.range a₀)) _ _ _ (a₀.baseChange k) (a₁.baseChange k)
    ((LinearMap.range a₀).mkQ.baseChange k) (d.baseChange k) (GlobalTheory.CatCoh.Z1 G)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 G) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne G))
    (GlobalTheory.CatCoh.d1 G) (E₁.toLinearMap ∘ₗ ψ₁.baseChange k) (E₀.toLinearMap ∘ₗ ψ₀.baseChange k)
    ?_ ?_ ?_ (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle G) ?_ ?_ ?_
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective k (Submodule.mkQ_surjective _)
  · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact k (LinearMap.exact_map_mkQ_range a₀) (Submodule.mkQ_surjective _)
  · rw [← LinearMap.baseChange_comp, hdπ]
  · intro x hx
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange k) c1) x
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply, hx,
      map_zero] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h12, ← h, map_zero]
  · intro y
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange k) c0) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.codRestrict_apply]
    rw [h, h01]
  · rw [LinearMap.subtype_comp_codRestrict]
    exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_transport hq (AddEquiv.refl _) (AddEquiv.refl _) (AddEquiv.refl _)
      E₀.toAddEquiv E₁.toAddEquiv E₂.toAddEquiv
      (fun y => congrFun (LinearMap.baseChange_eq_ltensor a₀) y)
      (fun x => congrFun (LinearMap.baseChange_eq_ltensor a₁) x)
      (fun y => (h01 y).symm.trans (congrArg E₁ (congrFun (LinearMap.baseChange_eq_ltensor _) y)))
      (fun x => (h12 x).symm.trans (congrArg E₂ (congrFun (LinearMap.baseChange_eq_ltensor _) x)))
      (fun x => congrArg E₁ (congrFun (LinearMap.baseChange_eq_ltensor ψ₁) x))


variable {F a₀ a₁ ψ₀ ψ₁ ψ₂} in
theorem core [Finite C] [∀ T T' : C, Finite (T ⟶ T')] [Module.Finite R P₀] [Module.Finite R P₁] [Module.Projective R P₀]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (g : ℕ)
    (h10 : a₁ ∘ₗ a₀ = 0) (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (hq0 : ∀ (M : Type) [AddCommGroup M] [Module R M],
      QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] C0 F) ((d0 F).lTensor M) (ψ₀.lTensor M))
    (hq' : ∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M)
      ((d0 F).lTensor M) ((d1 F).lTensor M) (ψ₁.lTensor M))
    (hS : SteinU F) (hVB : VB R (H1 F) g)
    (hfib : ∀ (k : Type) [Field k] [Algebra R k], ∃ (F' : C ⥤ CommAlgCat.{0} k) (_ : BC F F'),
      Module.finrank k (H1 F') = g) : H1CommutesBaseChange F := by
  have h1zero : GlobalTheory.CatCoh.d0 F 1 = 0 := by
    funext T T' φ
    rw [GlobalTheory.CatCoh.amitsur_d0_apply]
    simp
  obtain ⟨u, hu, hU⟩ := GlobalTheory.T.universal_coefficient_degree_zero R _ _ P₀ P₁
    (GlobalTheory.CatCoh.d0 F) a₀ ψ₀ ψ₁ 1 c0 h1zero hq0
    (fun M _ _ => GlobalTheory.CompanionTheory.PerfectFirstCohomology.stein_univ R C F hS M)
  haveI : Module.Projective R (P₁ ⧸ LinearMap.range a₀) :=
    GlobalTheory.CompanionTheory.PerfectFirstCohomology.proj_coker R P₀ P₁ a₀ u hu hU
  have hle : LinearMap.range a₀ ≤ LinearMap.ker a₁ := by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun h10 y
  obtain ⟨d, hdπ⟩ : ∃ d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂, d ∘ₗ (LinearMap.range a₀).mkQ = a₁ :=
    ⟨_, Submodule.liftQ_mkQ _ _ hle⟩
  obtain ⟨e⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_H1 c0 c1 d hdπ (GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_lid (hq' R))
  obtain ⟨hfin, hproj, hrank⟩ := hVB
  have hVBd : MainStatements.Hodge.VB R (LinearMap.ker d) g :=
    ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p => by
      rw [Module.rankAtStalk_eq_of_equiv e]
      exact hrank p⟩
  have hfibd : ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (LinearMap.ker (d.baseChange k)) = g := by
    intro k _ _
    obtain ⟨F', m, hg⟩ := hfib k
    obtain ⟨E₀, E₁, E₂, -, -, -, h01, h12⟩ := GlobalTheory.T.cochain_base_change_equivalences R k C F F' m
    obtain ⟨e'⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_base F' E₀ E₁ E₂ h01 h12 c0 c1 d hdπ (hq' k)
    rw [e'.finrank_eq, hg]
  obtain ⟨r', hr'⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.regular_of_fibres R _ P₂ d g hVBd hfibd
  obtain ⟨r, hr⟩ := Module.projective_lifting_property (LinearMap.range a₀).mkQ r' (Submodule.mkQ_surjective _)
  have har : a₁ ∘ₗ r ∘ₗ a₁ = a₁ := by
    rw [← hdπ]
    ext x
    have h₁ := LinearMap.congr_fun hr (d ((LinearMap.range a₀).mkQ x))
    have h₂ := LinearMap.congr_fun hr' ((LinearMap.range a₀).mkQ x)
    simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  intro R' _ _ F' m
  obtain ⟨E₀, E₁, E₂, -, hE₁, -, h01, h12⟩ := GlobalTheory.T.cochain_base_change_equivalences R R' C F F' m
  obtain ⟨H₁, H₂⟩ := GlobalTheory.T.quasi_isomorphism_degree_one_kernel R _ _ _ P₀ P₁ P₂
    (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.d1 F) a₀ a₁ ψ₀ ψ₁ ψ₂ r
    (GlobalTheory.CatCoh.Z1 F)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne F))
    (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle F) (fun _ => rfl) h10 c0 c1 har hq' R'
  exact GlobalTheory.T.first_cohomology_base_change_of_cochain_equivs R R' C F F' m E₀ E₁ E₂ hE₁ h01 h12 H₁ H₂

end Core

theorem perfect_first_cohomology_base_change : PerfectH1BaseChange := by
  intro R _ P _ _ F g hP hS hVB hfib
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ => Finite.of_subsingleton
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f0, p0⟩, ⟨f1, p1⟩, ⟨f2, p2⟩, -, h10, -, c0, c1, -, hq⟩ := hP
  exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.core g h10 c0 c1
    (fun M _ _ => (hq (ModuleCat.of R M)).1) (fun M _ _ => (hq (ModuleCat.of R M)).2.1) hS ⟨hVB.1, hVB.2.1, hVB.2.2⟩ hfib

end GlobalTheory.CompanionTheory.PerfectFirstCohomology
