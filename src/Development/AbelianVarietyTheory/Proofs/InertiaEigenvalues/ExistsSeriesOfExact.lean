module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPowKillsLatticeCokernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
noncomputable section

namespace GlobalTheory.AdmLoc

section Ss

variable {R : Type} [Ring R]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']

theorem subquot_map {f : A →ₗ[R] M} (hf : Function.Injective f) (X Y : Submodule R A) {X' Y' : Submodule R M}
    (hX : X' = X.map f) (hY : Y' = Y.map f) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  refine ⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Y) ?_⟩
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx⟩ := hy
    obtain rfl : x' = x := hf hxx
    exact ⟨⟨x', hx'⟩, hx, rfl⟩

theorem subquot_comap {g : M →ₗ[R] C} (hg : Function.Surjective g) (X Y : Submodule R C) {X' Y' : Submodule R M}
    (hX : X' = X.comap g) (hY : Y' = Y.comap g) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  let p : ↥(Y.comap g) →ₗ[R] ↥Y := g.restrict (fun _ h => h)
  let q : ↥(Y.comap g) →ₗ[R] (↥Y ⧸ X.comap Y.subtype) := (Submodule.mkQ _).comp p
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hp
  have hk : (X.comap g).comap (Y.comap g).subtype = LinearMap.ker q := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero (X.comap Y.subtype) (x := p x)).symm
  exact ⟨((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm⟩

theorem exists_series_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    (t : CompositionSeries (Submodule R A)) (ht₁ : t.head = ⊥) (ht₂ : t.last = ⊤)
    (s : CompositionSeries (Submodule R C)) (hs₁ : s.head = ⊥) (hs₂ : s.last = ⊤) :
    ∃ r : CompositionSeries (Submodule R M), r.head = ⊥ ∧ r.last = ⊤ ∧
      ∃ e : Fin t.length ⊕ Fin s.length ≃ Fin r.length,
        (∀ i, Nonempty (factor t i ≃ₗ[R] factor r (e (Sum.inl i)))) ∧
        ∀ j, Nonempty (factor s j ≃ₗ[R] factor r (e (Sum.inr j))) := by
  let s' : CompositionSeries (Submodule R M) :=
    { length := s.length
      toFun := fun i => (s i).comap g
      step := fun i => Submodule.comap_covBy_of_surjective hg (s.step i) }
  let t' : CompositionSeries (Submodule R M) :=
    { length := t.length
      toFun := fun i => (t i).map f
      step := fun i => Submodule.map_covBy_of_injective hf (t.step i) }
  have hc : t'.last = s'.head := by
    change t.last.map f = s.head.comap g
    rw [ht₂, hs₁, Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
  refine ⟨t'.smash s' hc, ?_, ?_, finSumFinEquiv, fun i => ?_, fun j => ?_⟩
  · rw [RelSeries.head_smash]
    change t.head.map f = ⊥
    rw [ht₁, Submodule.map_bot]
  · rw [RelSeries.last_smash]
    change s.last.comap g = ⊤
    rw [hs₂, Submodule.comap_top]
  · exact subquot_map hf _ _ (RelSeries.smash_castAdd hc i) (RelSeries.smash_succ_castAdd hc i)
  · exact subquot_comap hg _ _ (RelSeries.smash_natAdd hc j) (RelSeries.smash_succ_natAdd hc j)

theorem SameFactors.finiteLength_left (h : SameFactors R M M') : IsFiniteLength R M := by
  obtain ⟨s, -, h1, h2, -⟩ := h
  exact isFiniteLength_of_exists_compositionSeries ⟨s, h1, h2⟩

theorem SameFactors.finiteLength_right (h : SameFactors R M M') : IsFiniteLength R M' :=
  h.symm.finiteLength_left

theorem SameFactors.of_exact_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    {f' : A' →ₗ[R] M'} {g' : M' →ₗ[R] C'} (hf' : Function.Injective f')
    (hg' : Function.Surjective g') (H' : Function.Exact f' g')
    (hA : SameFactors R A A') (hC : SameFactors R C C') : SameFactors R M M' := by
  obtain ⟨t, t', ht1, ht2, ht3, ht4, a, ha⟩ := hA
  obtain ⟨s, s', hs1, hs2, hs3, hs4, c, hc⟩ := hC
  obtain ⟨r, hr1, hr2, e, he1, he2⟩ := exists_series_of_exact hf hg H t ht1 ht2 s hs1 hs2
  obtain ⟨r', hr3, hr4, e', he3, he4⟩ := exists_series_of_exact hf' hg' H' t' ht3 ht4 s' hs3 hs4
  refine ⟨r, r', hr1, hr2, hr3, hr4, e.symm.trans ((a.sumCongr c).trans e'), fun k => ?_⟩
  obtain ⟨k, rfl⟩ := e.surjective k
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rcases k with i | j
  · obtain ⟨u⟩ := he1 i
    obtain ⟨v⟩ := ha i
    obtain ⟨w⟩ := he3 (a i)
    exact ⟨(u.symm.trans v).trans w⟩
  · obtain ⟨u⟩ := he2 j
    obtain ⟨v⟩ := hc j
    obtain ⟨w⟩ := he4 (c j)
    exact ⟨(u.symm.trans v).trans w⟩

theorem SameFactors.of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) (h : IsFiniteLength R M) :
    SameFactors R M (A × C) :=
  SameFactors.of_exact_of_exact hf hg H LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameFactors.refl (h.of_injective hf)) (SameFactors.refl (h.of_surjective hg))

theorem SameFactors.sub_prod_quot (h : IsFiniteLength R M) (S : Submodule R M) :
    SameFactors R M (↥S × (M ⧸ S)) :=
  SameFactors.of_exact S.subtype_injective S.mkQ_surjective (LinearMap.exact_subtype_mkQ S) h

theorem SameFactors.prod (hA : SameFactors R A A') (hC : SameFactors R C C') :
    SameFactors R (A × C) (A' × C') :=
  SameFactors.of_exact_of_exact LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameFactors.congr (h : SameFactors R A A') (e : A ≃ₗ[R] C) (e' : A' ≃ₗ[R] C') : SameFactors R C C' :=
  ((SameFactors.of_equiv h.finiteLength_left e).symm.trans h).trans (SameFactors.of_equiv h.finiteLength_right e')

theorem SameFactors.of_subsingleton [Subsingleton A] [Subsingleton A'] : SameFactors R A A' :=
  SameFactors.of_equiv IsFiniteLength.of_subsingleton (LinearEquiv.ofSubsingleton _ _)

theorem SameFactors.pi_fin : ∀ {m : ℕ} {N N' : Fin m → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)], (∀ j, SameFactors R (N j) (N' j)) →
    SameFactors R (∀ j, N j) (∀ j, N' j)
  | 0, _, _, _, _, _, _, _ => SameFactors.of_subsingleton
  | _ + 1, N, N', _, _, _, _, h =>
    ((h 0).prod (SameFactors.pi_fin fun j => h (Fin.succ j))).congr
      (Fin.consLinearEquiv R N) (Fin.consLinearEquiv R N')

theorem SameFactors.pi {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)] (h : ∀ j, SameFactors R (N j) (N' j)) :
    SameFactors R (∀ j, N j) (∀ j, N' j) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact (SameFactors.pi_fin (N := fun j => N (e.symm j)) (N' := fun j => N' (e.symm j))
    fun j => h (e.symm j)).congr (LinearEquiv.piCongrLeft R N e.symm) (LinearEquiv.piCongrLeft R N' e.symm)

end Ss

section Rep

variable {O G : Type} [CommRing O] [Group G]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
  [AddCommGroup C] [Module O C] [AddCommGroup C'] [Module O C']

def asModuleMap {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M')
    (hf : ∀ g x, f (π g x) = π' g (f x)) : π.asModule →ₗ[MonoidAlgebra O G] π'.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule π π'
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }

def equivAsModule {π : Representation O G M} {π' : Representation O G M'} (e : M ≃ₗ[O] M')
    (he : ∀ g x, e (π g x) = π' g (e x)) : π.asModule ≃ₗ[MonoidAlgebra O G] π'.asModule :=
  LinearEquiv.ofBijective (asModuleMap e.toLinearMap he) e.bijective

def piAsModule {ι : Type} {N : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    (π : ∀ j, Representation O G (N j)) :
    (piRep π).asModule ≃ₗ[MonoidAlgebra O G] ∀ j, (π j).asModule :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun j => asModuleMap (π := piRep π) (π' := π j) (LinearMap.proj j) fun _ _ => rfl)
    (Function.bijective_id (α := ∀ j, N j))

theorem finiteLength_asModule (π : Representation O G M) (h : IsFiniteLength O M) :
    IsFiniteLength (MonoidAlgebra O G) π.asModule := by
  have h' : IsFiniteLength O π.asModule := h.of_injective (f := π.asModuleEquiv.toLinearMap) π.asModuleEquiv.injective
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h' ⊢
  exact ⟨isNoetherian_of_tower O h'.1, isArtinian_of_tower O h'.2⟩

variable {π : Representation O G M} {π' : Representation O G M'} {α : Representation O G A}
  {α' : Representation O G A'} {γ : Representation O G C} {γ' : Representation O G C'}

theorem SameSS.refl' (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π π := SameFactors.refl h

theorem SameSS.refl (π : Representation O G M) (h : IsFiniteLength O M) : SameSS π π :=
  SameFactors.refl (finiteLength_asModule π h)

theorem SameSS.symm (h : SameSS π π') : SameSS π' π := SameFactors.symm h

theorem SameSS.trans (h : SameSS π π') (h' : SameSS π' α) : SameSS π α := SameFactors.trans h h'

theorem SameSS.of_equiv (h : IsFiniteLength O M) (e : M ≃ₗ[O] M') (he : ∀ g x, e (π g x) = π' g (e x)) :
    SameSS π π' :=
  SameFactors.of_equiv (finiteLength_asModule π h) (equivAsModule e he)

theorem SameSS.congr (h : SameSS α α') (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x))
    (e' : A' ≃ₗ[O] C') (he' : ∀ g x, e' (α' g x) = γ' g (e' x)) : SameSS γ γ' :=
  SameFactors.congr h (equivAsModule e he) (equivAsModule e' he')

theorem SameSS.congr_left (h : SameSS α π) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS γ π :=
  h.congr e he (LinearEquiv.refl O M) fun _ _ => rfl

theorem SameSS.congr_right (h : SameSS π α) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS π γ :=
  h.congr (LinearEquiv.refl O M) (fun _ _ => rfl) e he

theorem SameSS.of_exact_of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    {f' : A' →ₗ[O] M'} {p' : M' →ₗ[O] C'}
    (ef' : ∀ g x, f' (α' g x) = π' g (f' x)) (ep' : ∀ g x, p' (π' g x) = γ' g (p' x))
    (hf' : Function.Injective f') (hp' : Function.Surjective p') (H' : Function.Exact f' p')
    (hA : SameSS α α') (hC : SameSS γ γ') : SameSS π π' :=
  SameFactors.of_exact_of_exact (R := MonoidAlgebra O G) (M := π.asModule) (M' := π'.asModule)
    (A := α.asModule) (A' := α'.asModule) (C := γ.asModule) (C' := γ'.asModule)
    (f := asModuleMap f ef) (g := asModuleMap p ep) hf hp H
    (f' := asModuleMap f' ef') (g' := asModuleMap p' ep') hf' hp' H' hA hC

theorem SameSS.of_exact' {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π (α.prod γ) :=
  SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inl O A C) (p' := LinearMap.snd O A C)
    (α' := α) (γ' := γ) (fun g x => by simp) (fun g x => by simp)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameSS.refl' (IsFiniteLength.of_injective (M := α.asModule) (N := π.asModule) (f := asModuleMap f ef) h hf))
    (SameSS.refl' (IsFiniteLength.of_surjective (M := π.asModule) (N := γ.asModule) (f := asModuleMap p ep) h hp))

theorem SameSS.of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength O M) : SameSS π (α.prod γ) :=
  SameSS.of_exact' ef ep hf hp H (finiteLength_asModule π h)

theorem SameSS.prod (hA : SameSS α α') (hC : SameSS γ γ') : SameSS (α.prod γ) (α'.prod γ') :=
  SameSS.of_exact_of_exact (f := LinearMap.inl O A C) (p := LinearMap.snd O A C)
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (f' := LinearMap.inl O A' C') (p' := LinearMap.snd O A' C')
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameSS.piRep {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module O (N' j)] {σ : ∀ j, Representation O G (N j)}
    {σ' : ∀ j, Representation O G (N' j)} (h : ∀ j, SameSS (σ j) (σ' j)) : SameSS (piRep σ) (piRep σ') :=
  (SameFactors.pi (N := fun j => (σ j).asModule) (N' := fun j => (σ' j).asModule) h).congr
    (piAsModule σ).symm (piAsModule σ').symm

end Rep

end GlobalTheory.AdmLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinApproxOfPolyApproxTrc
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem linApprox_of_polyApprox_trc : ∀ (k Γ : Type) [NormedField k] [IsUltrametricDist k] [Group Γ] (a : ℕ)
    (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)), PolyApprox (trc r) (trc '' C) → LinApprox r C := by
  intro k Γ _ _ _ a r C h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  let f : (Γ → k) → (Γ →* GL (Fin a) k) := Function.invFunOn trc C
  have hf : ∀ η ∈ s, f η ∈ C ∧ trc (f η) = η := fun η hη =>
    ⟨Function.invFunOn_mem (hs hη), Function.invFunOn_eq (hs hη)⟩
  have hinj : Set.InjOn f (s : Set (Γ → k)) := fun x hx y hy hxy => by
    rw [← (hf x hx).2, ← (hf y hy).2, hxy]
  refine ⟨s.image f, fun ρ => c (trc ρ), ?_, fun g => ?_⟩
  · intro ρ hρ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
    exact (hf η hη).1
  · have := hP (MvPolynomial.X g)
    simp only [MvPolynomial.aeval_X] at this
    rw [Finset.sum_image hinj]
    have e : ∑ x ∈ s, c (trc (f x)) * trc (f x) g = ∑ η ∈ s, c η * η g :=
      Finset.sum_congr rfl fun η hη => by rw [(hf η hη).2]
    rw [e]
    exact this

end GlobalTheory.Cong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOfPowerTraces
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CharpolyNewton

open Polynomial Finset

variable {k : Type} [Field k]

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → k) (j : ℕ) :
    (j : k) * (univ.val.map f).esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ k j)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset k) (j : ℕ) :
    (j : k) * s.esymm j = (-1) ^ (j + 1) *
      ∑ a ∈ antidiagonal j with a.1 < j, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) j
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq [CharZero k] (s t : Multiset k)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) : ∀ j, s.esymm j = t.esymm j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hj0 : (j : k) ≠ 0 := by exact_mod_cast hj.ne'
      apply mul_left_cancel₀ hj0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq [CharZero k] (s t : Multiset k) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ j, (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext j
  by_cases hj : j ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hj, Multiset.prod_X_sub_C_coeff t (hc ▸ hj), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hj
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

theorem charpoly_eq_prod_of_trace_pow : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (a : ℕ) (M : Matrix (Fin a) (Fin a) k) (B : Multiset k), Multiset.card B = a → (∀ n : ℕ, 1 ≤ n → (M ^ n).trace = (B.map (· ^ n)).sum) → M.charpoly = (B.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro k _ _ _ a M B hB h
  have hR : Multiset.card M.charpoly.roots = a := GlobalTheory.CharpolyPow.card_roots_charpoly M
  have hsplit : M.charpoly = (M.charpoly.roots.map fun b => X - C b).prod := by
    have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq M.charpoly_monic
      (by rw [hR, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
    exact this.symm
  rw [hsplit]
  refine prod_eq_of_psum_eq _ _ (by rw [hR, hB]) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hR, hB]
  · rw [← h n hn, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow]

end GlobalTheory.CharpolyNewton
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentCoeffNegEqZeroOfBounded
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory

theorem norm_eTwoPi_I_mul (y : ℝ) : ‖eTwoPi (Complex.I * y)‖ = Real.exp (-(2 * Real.pi * y)) := by
  rw [eTwoPi, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem laurent_coeff_neg_eq_zero_of_bounded : ∀ (F : ℂ⸨X⸩) (T C : ℝ),
    (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) →
    ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  intro F T C h m hm
  by_contra hne
  have hF : F ≠ 0 := by rintro rfl; exact hne (by simp)
  have hm₀le : F.order ≤ m := by
    by_contra hlt; push_neg at hlt; exact hne (HahnSeries.coeff_eq_zero_of_lt_order hlt)
  have hc : F.coeff F.order ≠ 0 := fun h0 => hF (HahnSeries.coeff_order_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (le_of_lt (lt_of_le_of_lt hm₀le hm))
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  set m₀ := F.order with hm₀
  set y₁ : ℝ := max T 0 + 1 with hy₁
  have hy₁T : T < y₁ := by have := le_max_left T 0; linarith
  have hy₁0 : 0 < y₁ := by have := le_max_right T 0; linarith
  obtain ⟨x₁, hx₁, -⟩ := h (Complex.I * y₁) (by simpa using hy₁T)
  set q₁ := eTwoPi (Complex.I * y₁) with hq₁
  set ρ₁ := ‖q₁‖ with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁, hq₁, norm_eTwoPi_I_mul]; exact Real.exp_pos _
  have hS : Summable (fun m : ℤ => ‖F.coeff m * q₁ ^ m‖) := hx₁.summable.norm
  set S := ∑' m : ℤ, ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k with hSdef
  have key : ∀ y : ℝ, y₁ ≤ y →
      ‖F.coeff m₀‖ ≤ C * Real.exp (-(2 * Real.pi * y)) ^ k + Real.exp (-(2 * Real.pi * y)) / ρ₁ * S := by
    intro y hy
    obtain ⟨x, hx, hxC⟩ := h (Complex.I * y) (by simpa using lt_of_lt_of_le hy₁T hy)
    set q := eTwoPi (Complex.I * y) with hq
    set ρ := ‖q‖ with hρ
    have hρe : ρ = Real.exp (-(2 * Real.pi * y)) := norm_eTwoPi_I_mul y
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρe, hρ₁, hq₁, norm_eTwoPi_I_mul, Real.exp_le_exp]
      nlinarith [Real.pi_pos]
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    set r : ℤ → ℂ := fun m => F.coeff m * q ^ m * q ^ k - (if m = m₀ then F.coeff m₀ else 0) with hr
    have h2 : HasSum r (x * q ^ k - F.coeff m₀) := (hx.mul_right (q ^ k)).sub (hasSum_ite_eq m₀ _)
    have hbd : ∀ m, ‖r m‖ ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by
      intro m
      have hRnn : 0 ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by positivity
      by_cases hmm : m = m₀
      · subst hmm
        have : q ^ m₀ * q ^ k = 1 := by
          rw [hk, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq0)]
        have : r m₀ = 0 := by simp only [hr, mul_assoc, this, mul_one]; simp
        rw [this, norm_zero]; exact hRnn
      rcases lt_or_gt_of_ne hmm with hlt | hgt
      · have : r m = 0 := by simp only [hr, if_neg hmm, HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul, sub_zero]
        rw [this, norm_zero]; exact hRnn
      · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ m - m₀ - 1 by omega)
        have hm : m = (n + 1 : ℕ) - (k : ℤ) := by push_cast; omega
        have e1 : ∀ t : ℝ, t ≠ 0 → t ^ m * t ^ k = t ^ (n + 1) := fun t ht => by
          rw [← zpow_natCast t k, ← zpow_add₀ ht, ← zpow_natCast]; congr 1; omega
        have hρpos : 0 < ρ := by rw [hρe]; exact Real.exp_pos _
        have hrm : ‖r m‖ = ‖F.coeff m‖ * (ρ ^ m * ρ ^ k) := by
          simp only [hr, if_neg hmm, sub_zero, norm_mul, norm_pow, norm_zpow, ← hρ, mul_assoc]
        have hq₁m : ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k = ‖F.coeff m‖ * (ρ₁ ^ m * ρ₁ ^ k) := by
          rw [norm_mul, norm_zpow, ← hρ₁, mul_assoc]
        rw [hrm, hq₁m, e1 ρ hρpos.ne', e1 ρ₁ hρ₁pos.ne']
        have hpow : ρ ^ n ≤ ρ₁ ^ n := pow_le_pow_left₀ hρ0 hρle n
        have hc0 : 0 ≤ ‖F.coeff m‖ := norm_nonneg _
        rw [pow_succ, pow_succ]
        calc ‖F.coeff m‖ * (ρ ^ n * ρ) ≤ ‖F.coeff m‖ * (ρ₁ ^ n * ρ) := by gcongr
          _ = ρ / ρ₁ * (‖F.coeff m‖ * (ρ₁ ^ n * ρ₁)) := by field_simp
    have hg : HasSum (fun m => ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k)) (ρ / ρ₁ * S) :=
      (hS.mul_right (ρ₁ ^ k)).hasSum.mul_left _
    have h3 : ‖x * q ^ k - F.coeff m₀‖ ≤ ρ / ρ₁ * S := by
      rw [← h2.tsum_eq]; exact tsum_of_norm_bounded hg hbd
    have h4 : ‖x * q ^ k‖ ≤ C * ρ ^ k := by
      rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_right hxC (by positivity)
    rw [← hρe]
    calc ‖F.coeff m₀‖ = ‖x * q ^ k - (x * q ^ k - F.coeff m₀)‖ := by ring_nf
      _ ≤ ‖x * q ^ k‖ + ‖x * q ^ k - F.coeff m₀‖ := norm_sub_le _ _
      _ ≤ C * ρ ^ k + ρ / ρ₁ * S := add_le_add h4 h3
  have hlim : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
      (Filter.tendsto_id.const_mul_atTop (by positivity)))
  have hlim2 : Filter.Tendsto (fun y : ℝ => C * Real.exp (-(2 * Real.pi * y)) ^ k +
      Real.exp (-(2 * Real.pi * y)) / ρ₁ * S) Filter.atTop (nhds 0) := by
    have := ((hlim.pow k).const_mul C).add ((hlim.div_const ρ₁).mul_const S)
    simpa [zero_pow hk0] using this
  have hle : ‖F.coeff m₀‖ ≤ 0 :=
    ge_of_tendsto hlim2 (Filter.eventually_atTop.2 ⟨y₁, key⟩)
  exact hc (norm_le_zero_iff.1 hle)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommutantMulIntegralConjugate
open Matrix Polynomial

namespace GlobalTheory.IntConj

section Krylov

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_krylov_of_semiconj {M M' x : Matrix n n A} (h : x * M' = M * x) (w : n → A) :
    x * GlobalTheory.RegSS.krylov M' w = GlobalTheory.RegSS.krylov M (x *ᵥ w) := by
  ext i j
  have hk : ∀ k : ℕ, x * M' ^ k = M ^ k * x := fun k => SemiconjBy.pow_right h k
  calc (x * GlobalTheory.RegSS.krylov M' w) i j
      = (x *ᵥ ((M' ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ w)) i := by
        simp [GlobalTheory.RegSS.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = ((M ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ (x *ᵥ w)) i := by
        rw [mulVec_mulVec, hk, ← mulVec_mulVec]
    _ = GlobalTheory.RegSS.krylov M (x *ᵥ w) i j := by simp [GlobalTheory.RegSS.krylov]

end Krylov

theorem mem_unitBall {E : Type} [NormedField E] [IsUltrametricDist E] (y : E) :
    y ∈ (NormedField.valuation (K := E)).valuationSubring ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

theorem norm_eq_one_of_isUnit {E : Type} [NormedField E] [IsUltrametricDist E]
    {a : (NormedField.valuation (K := E)).valuationSubring} (ha : IsUnit a) : ‖(a : E)‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h := congrArg (fun y : (NormedField.valuation (K := E)).valuationSubring => ‖(y : E)‖) u.mul_inv
  simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h
  have h1 : ‖((u : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 (u : (NormedField.valuation (K := E)).valuationSubring).2
  have h2 : ‖(((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 ((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring).2
  nlinarith [norm_nonneg ((u : (NormedField.valuation (K := E)).valuationSubring) : E),
    norm_nonneg (((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)]

end GlobalTheory.IntConj

namespace GlobalTheory.IntConj

theorem exists_commuting_mul_integral (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N x : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hsep : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (hx : IsUnit x) (hN' : ∀ i j, ‖(x⁻¹ * N * x) i j‖ ≤ 1) :
    ∃ c : Matrix (Fin n) (Fin n) E, IsUnit c ∧ c * N = N * c ∧ (∀ i j, ‖(c⁻¹ * x) i j‖ ≤ 1) ∧
      ‖(c⁻¹ * x).det‖ = 1 := by
  classical
  let O := (NormedField.valuation (K := E)).valuationSubring
  let φ : O →+* E := O.subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have lift : ∀ M : Matrix (Fin n) (Fin n) E, (∀ i j, ‖M i j‖ ≤ 1) →
      ∃ M₀ : Matrix (Fin n) (Fin n) O, M₀.map φ = M := fun M hM =>
    ⟨Matrix.of fun i j => ⟨M i j, (mem_unitBall _).2 (hM i j)⟩, by ext i j; rfl⟩
  have liftP : ∀ p : E[X], (∀ i, ‖p.coeff i‖ ≤ 1) → ∃ p₀ : O[X], p₀.map φ = p := by
    intro p hp
    have : p ∈ Polynomial.lifts φ :=
      (lifts_iff_coeff_lifts p).2 fun k => ⟨⟨_, (mem_unitBall _).2 (hp k)⟩, rfl⟩
    exact (mem_lifts p).1 this
  obtain ⟨u, v, hu, hv, huv⟩ := hsep
  obtain ⟨u₀, rfl⟩ := liftP u hu
  obtain ⟨v₀, rfl⟩ := liftP v hv
  have sep : ∀ M₀ : Matrix (Fin n) (Fin n) O, (M₀.map φ).charpoly = N.charpoly →
      M₀.charpoly.Separable := by
    intro M₀ hM
    refine ⟨u₀, v₀, ?_⟩
    apply Polynomial.map_injective φ hφ
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      ← Matrix.charpoly_map, hM, Polynomial.map_one]
    exact huv
  obtain ⟨X, rfl⟩ := hx
  have hXd : IsUnit (X : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 X.isUnit
  have hcp : ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)).charpoly = N.charpoly := by
    exact Matrix.charpoly_units_conj' X N
  obtain ⟨N₀, hN₀⟩ := lift N hN
  obtain ⟨N₀', hN₀'⟩ := lift _ hN'
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀ (sep N₀ (by rw [hN₀]))
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀' (sep N₀' (by rw [hN₀', hcp]))
  have hK : (GlobalTheory.RegSS.krylov N₀ v₁).map φ = GlobalTheory.RegSS.krylov N (φ ∘ v₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀]
  have hK' : (GlobalTheory.RegSS.krylov N₀' w₁).map φ =
      GlobalTheory.RegSS.krylov ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) (φ ∘ w₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀']
  have hKu := GlobalTheory.RegSS.isUnit_det_map φ hv₁
  have hKu' := GlobalTheory.RegSS.isUnit_det_map φ hw₁
  obtain ⟨-, -, hbij⟩ := GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N (φ ∘ v₁) (by rw [← hK]; exact hKu)
  obtain ⟨l, hl⟩ := hbij.2 ((X : Matrix (Fin n) (Fin n) E) *ᵥ (φ ∘ w₁))
  simp only at hl
  have hcN : N * (l : Matrix (Fin n) (Fin n) E) = l * N := GlobalTheory.RegSS.commute_of_mem_genAlg rfl l.2
  have hXN : (X : Matrix (Fin n) (Fin n) E) * ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) = N * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXd, Matrix.one_mul]
  have key : (l : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀ v₁).map φ =
      (X : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀' w₁).map φ := by
    rw [hK, hK', mul_krylov_of_semiconj hcN.symm, mul_krylov_of_semiconj hXN, hl]
  set Kv := (GlobalTheory.RegSS.krylov N₀ v₁).map φ with hKv
  set Kw := (GlobalTheory.RegSS.krylov N₀' w₁).map φ with hKw
  generalize (l : Matrix (Fin n) (Fin n) E) = c at key hcN
  have hcu : IsUnit c := by
    have : c = (X : Matrix (Fin n) (Fin n) E) * Kw * Kv⁻¹ := by
      rw [← key, Matrix.mul_nonsing_inv_cancel_right _ _ hKu]
    rw [this]
    exact (X.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hKu')).mul
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hKu))
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det _).1 hcu
  have e2 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) = Kv * Kw⁻¹ := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (c⁻¹ * (X : Matrix (Fin n) (Fin n) E)) hKu',
      Matrix.mul_assoc c⁻¹, ← key, Matrix.nonsing_inv_mul_cancel_left _ _ hcd]
  have hinv : Kw⁻¹ = ((GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hKw, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ hw₁, map_one]
  have e3 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) =
      (GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    rw [e2, hinv, hKv, Matrix.map_mul]
  refine ⟨c, hcu, hcN.symm, fun i j => ?_, ?_⟩
  · rw [e3]; exact (mem_unitBall _).1 ((GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹) i j).2
  · rw [e3, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact norm_eq_one_of_isUnit (by
      rw [Matrix.det_mul]; exact hv₁.mul (Matrix.isUnit_nonsing_inv_det _ hw₁))

end GlobalTheory.IntConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLattice
noncomputable section

namespace GlobalTheory.CokerLift

open PowerSeries GlobalTheory.BK Matrix

section Psi

variable {K : Type} [NormedField K]

def psi (l : ℕ) : K⟦X⟧ →ₗ[K] K⟦X⟧ where
  toFun f := PowerSeries.mk fun n => coeff (l * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

theorem coeff_psi (l : ℕ) (f : K⟦X⟧) (n : ℕ) : coeff n (psi l f) = coeff (l * n) f := by
  simp [psi]

theorem psi_frob_mul (l : ℕ) [Fact l.Prime] (g h : K⟦X⟧) :
    psi l (frob K l g * h) = g * psi l h := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_psi, coeff_mul, coeff_mul]
  have hinj : Function.Injective (fun p : ℕ × ℕ => (l * p.1, l * p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hl h.1) (Nat.eq_of_mul_eq_mul_left hl h.2)
  have h1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 g * coeff p.2 (psi l h) =
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).map ⟨_, hinj⟩, coeff p.1 (frob K l g) * coeff p.2 h := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coeFn_mk, coeff_frob, coeff_psi, dvd_mul_right, if_true,
      Nat.mul_div_cancel_left _ hl]
  rw [h1]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    simp only [Function.Embedding.coeFn_mk]
    rw [← mul_add, hq]
  · intro p hp hp'
    rw [coeff_frob, if_neg, zero_mul]
    rintro ⟨c, hc⟩
    apply hp'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [Finset.mem_map]
    refine ⟨(c, n - c), ?_, ?_⟩
    · have : l * c ≤ l * n := by omega
      have := Nat.le_of_mul_le_mul_left this hl
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      simp only; omega
    · refine Prod.ext hc.symm ?_
      simp only [Function.Embedding.coeFn_mk, Nat.mul_sub]
      omega

theorem psi_frob (l : ℕ) [Fact l.Prime] (g : K⟦X⟧) : psi l (frob K l g) = g := by
  ext n
  rw [coeff_psi, coeff_frob, if_pos (dvd_mul_right _ _),
    Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos]

theorem psi_mulVec {ι κ : Type} [Fintype ι] (l : ℕ) [Fact l.Prime] (Y : Matrix κ ι K⟦X⟧)
    (m : ι → K⟦X⟧) :
    (fun i => psi l ((Y.map (frob K l) *ᵥ m) i)) = Y *ᵥ fun j => psi l (m j) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, psi_frob_mul]

end Psi

end GlobalTheory.CokerLift

noncomputable section

namespace GlobalTheory.CokerLift

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]

theorem psi_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : psi l f ∈ A O K := fun n => by
  rw [coeff_psi]
  exact hf _

theorem killsCoker_M {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (n : ℕ)
    (hL : KillsCoker F.app n P.L Q.L) : KillsCoker F.app n P.M Q.M := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hL (Q.phi y) (Q.phi_mem_L hy)
  have hm (τ : ZMod a) := P.mem_extc_iff.1 (mem_tot.1 hx τ)
  refine ⟨fun σ i => psi l ((P.mxInv (σ + 1) *ᵥ x (σ + 1)) i),
    mem_tot.2 fun σ i => psi_mem_A (hm (σ + 1) i), ?_⟩
  funext σ
  have key : (F.mat σ).map (frob K l) *ᵥ (P.mxInv (σ + 1) *ᵥ x (σ + 1)) = n • frobV l (y σ) := by
    have hc := F.comm (σ + 1)
    rw [add_sub_cancel_right] at hc
    have h2 : (F.mat σ).map (frob K l) = Q.mxInv (σ + 1) * (F.mat (σ + 1) * P.mx (σ + 1)) := by
      rw [hc, ← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
    have h3 := congrFun hxy (σ + 1)
    rw [Hom.app_apply, Pi.smul_apply, Q.phi_apply, add_sub_cancel_right] at h3
    rw [h2, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Q.mxInv_mul_mx,
      Matrix.one_mulVec]
  rw [Hom.app_apply, ← psi_mulVec, key]
  funext i
  simp only [Pi.smul_apply, frobV_apply, map_nsmul, psi_frob]

theorem killsCoker_EM [NormedAlgebra ℚ_[l] K] [NeZero e] {P : PhiMod O K l e a ι}
    {Q : PhiMod O K l e a κ} (F : Hom P Q) (n η : ℕ) (hM : KillsCoker F.app n P.M Q.M) :
    KillsCoker F.app n (P.EM η) (Q.EM η) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hM _ hy
  refine ⟨Ezpow K l e (-(η : ℤ)) • x, ?_, ?_⟩
  · change E K l e ^ η • Ezpow K l e (-(η : ℤ)) • x ∈ P.M
    rw [smul_smul, E_pow_mul_Ezpow_neg, one_smul]
    exact hx
  · rw [map_smul, hxy, smul_comm, smul_smul, mul_comm, E_pow_mul_Ezpow_neg, one_smul]

theorem killsCoker_invOf [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (n : ℕ) (W₁ : Submodule (A O K) (Vec K a ι))
    (W₂ : Submodule (A O K) (Vec K a κ)) (hW : ∀ g, ∀ v ∈ W₁, Δ₁.act g v ∈ W₁)
    (h : KillsCoker F.app n W₁ W₂) : KillsCoker F.app n (Δ₁.invOf W₁) (Δ₂.invOf W₂) := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := Δ₂.mem_invOf.1 hy
  obtain ⟨x, hx, hxy⟩ := h y hy1
  refine ⟨Δ₁.avg x, Δ₁.mem_invOf.2 ⟨Δ₁.avg_mem (W₁.restrictScalars O) fun g => hW g x hx,
    fun g => Δ₁.avg_mem_inv x g⟩, ?_⟩
  have := Δ₁.map_avg (F.app.restrictScalars K) (v := x) fun g => by
    simp only [LinearMap.restrictScalars_apply]
    rw [F.app_act, hxy, map_nsmul, hy2 g]
  exact this.trans hxy

theorem killsCoker_Y' [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {Δ₁ : Descent P} {Δ₂ : Descent Q}
    (F : Descent.Hom Δ₁ Δ₂) (n η : ℕ) (hY : KillsCoker F.app n (Δ₁.Y η) (Δ₂.Y η)) :
    KillsCoker F.app n (Δ₁.Y' η) (Δ₂.Y' η) := by
  intro y hy
  obtain ⟨y₀, h₀, rfl⟩ := Δ₂.mem_Y'.1 hy
  obtain ⟨x, hx, hxy⟩ := hY y₀ h₀
  exact ⟨_, Δ₁.mem_Y'.2 ⟨x, hx, rfl⟩, by rw [map_smul, hxy, smul_comm]⟩

end Main

theorem killsAll_of_killsCoker_L (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type)
    [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H)
    (F : BKHom D₁ D₂) : ∀ r : ℕ, KillsCoker F.app (l ^ r) D₁.L D₂.L → KillsAll F (l ^ r) := by
  intro r hL
  have hM := killsCoker_M F.toHom _ hL
  have hEM := killsCoker_EM F.toHom _ η hM
  have hY := killsCoker_invOf F _ _ _ (fun g _ hv => D₁.desc.act_mem_EM g hv) hEM
  exact ⟨hL, hM, hEM, killsCoker_invOf F _ _ _ (fun g v hv => D₁.desc.act_mem_M g v hv) hM, hY,
    killsCoker_Y' F _ η hY⟩

end GlobalTheory.CokerLift
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLatticeStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ r : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ r) D₁.L D₂.L → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsAll F (l ^ r) := by
  first | exact @GlobalTheory.CokerLift.killsAll_of_killsCoker_L | exact GlobalTheory.CokerLift.killsAll_of_killsCoker_L | (intros; apply GlobalTheory.CokerLift.killsAll_of_killsCoker_L <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  intro O K _ _ _ _ _ l e a _ _ _ _ hT ι κ _ _ _ _ Sig U N η H hB D₁ D₂ hD₁ hD₂ F hF
  haveI : FiniteDimensional ℚ_[l] K := hT.finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  exact GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice O K l e a ι κ η H D₁ D₂ F _
    (GlobalTheory.T.breuilKisin_pow_kills_lattice_cokernel O K l e a ι κ η H D₁ D₂ F Sig U N hB hD₁.chars_subset hD₂ hF)

end GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePowStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  first | exact @GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | exact GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | (intros; apply GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticePowSmulNhdsZeroBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticePowSmulNhdsZeroBasis
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory

theorem _root_.GlobalTheory.lattice_multiples_nhds_basis :
    ∀ (LL O V : Type) [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V] (T : Submodule O V) (lam : O), T.FG → Submodule.span LL (T : Set V) = ⊤ → IsOpen (Set.range (algebraMap O LL)) → algebraMap O LL lam ≠ 0 → (∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (lam ^ a * x) ∈ U) → (∀ a : ℕ, {v : V | ∃ t ∈ T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ T, lam ^ a • t ∈ U := by
  intro LL O V _ _ _ _ _ _ _ _ _ _ _ T lam hT hspan hopen hlam hsmall
  obtain ⟨n, s, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hT
  set φ : (Fin n → LL) →ₗ[LL] V := Fintype.linearCombination LL s with hφ
  have key : ∀ (a : ℕ) (c : Fin n → O),
      φ (fun i => algebraMap O LL (lam ^ a * c i)) = lam ^ a • ∑ i, c i • s i := by
    intro a c
    simp only [hφ, Fintype.linearCombination_apply, Finset.smul_sum, map_mul, mul_smul,
      algebraMap_smul]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp ht
    exact ⟨_, by rw [key 0 c, pow_zero, one_smul]⟩
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hsurj
  refine ⟨fun a => ?_, fun U hU => ?_⟩
  · have hc : algebraMap O LL (lam ^ a) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hlam
    set W : Set LL := Set.range fun x : O => algebraMap O LL (lam ^ a * x) with hW
    have hWeq : W = (Homeomorph.mulLeft₀ _ hc) '' Set.range (algebraMap O LL) := by
      ext y; simp [hW, map_mul]
    have hWo : IsOpen W := hWeq ▸ (Homeomorph.mulLeft₀ _ hc).isOpenMap _ hopen
    have hPo : IsOpen (φ '' Set.univ.pi fun _ => W) :=
      hq.isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hWo)
    refine mem_of_superset (hPo.mem_nhds ⟨0, fun i _ => ⟨0, by simp⟩, map_zero φ⟩) ?_
    rintro v ⟨y, hy, rfl⟩
    choose c hc' using fun i => hy i (Set.mem_univ i)
    have : y = fun i => algebraMap O LL (lam ^ a * c i) := funext fun i => (hc' i).symm
    subst this
    exact ⟨_, (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c, rfl⟩, key a c⟩
  · have h0 : φ ⁻¹' U ∈ 𝓝 (0 : Fin n → LL) :=
      hq.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, hsub⟩ := h0
    obtain ⟨a, ha⟩ := hsmall (⋂ i, t i) (Filter.iInter_mem.mpr ht)
    refine ⟨a, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hv
    rw [← key a c]
    exact hsub fun i _ => Set.mem_iInter.mp (ha (c i)) i

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticePowSmulNhdsZeroBasisStatement
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pow_smul_nhds_zero_basis : ∀ (LL O V : Type) [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V] (T : Submodule O V) (lam : O), T.FG → Submodule.span LL (T : Set V) = ⊤ → IsOpen (Set.range (algebraMap O LL)) → algebraMap O LL lam ≠ 0 → (∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (lam ^ a * x) ∈ U) → (∀ a : ℕ, {v : V | ∃ t ∈ T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ T, lam ^ a • t ∈ U := by
  first | exact @GlobalTheory.lattice_multiples_nhds_basis | exact GlobalTheory.lattice_multiples_nhds_basis | (intros; apply GlobalTheory.lattice_multiples_nhds_basis <;> assumption)
end
end
