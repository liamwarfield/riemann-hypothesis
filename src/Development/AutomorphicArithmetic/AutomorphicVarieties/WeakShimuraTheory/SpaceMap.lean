module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section
variable {ι Γ R R' R'' : Type} [Group Γ] [CommRing R] [CommRing R'] [CommRing R'']

theorem PD.map_map (P : PD ι Γ R) (f : R →+* R') (g : R' →+* R'') : (P.map f).map g = P.map (g.comp f) := rfl

theorem adj_map (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp only [adj_apply, Matrix.map_apply]
  rw [map_zsmul]

theorem isGSp_map (f : R →+* R') {ν : R} {X : M4 R} (h : IsGSp ν X) : IsGSp (f ν) (X.map f) := by
  unfold IsGSp at h ⊢
  rw [adj_map, ← Matrix.map_mul, h]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
  split_ifs <;> simp

theorem PD.map_r (P : PD ι Γ R) (f : R →+* R') (g : Γ) : (P.map f).r g = (P.r g).map f := rfl

theorem PD.map_n (P : PD ι Γ R) (f : R →+* R') (v : ι) : (P.map f).n v = (P.n v).map f := rfl

theorem PD.map_flag (P : PD ι Γ R) (f : R →+* R') (v : ι) (s : Γ) :
    adj ((P.map f).n v) * (P.map f).r s * (P.map f).n v = (adj (P.n v) * P.r s * P.n v).map f := by
  rw [PD.map_r, PD.map_n, adj_map, ← Matrix.map_mul, ← Matrix.map_mul]

theorem PD.map_ψ (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  unfold PD.ψ
  rw [PD.map_flag]
  rfl

theorem PD.Cont.map [TopologicalSpace Γ] {P : PD ι Γ R} {I : Ideal R} (h : P.Cont I) (f : R →+* R') {J : Ideal R'}
    (hf : I ≤ J.comap f) : (P.map f).Cont J := by
  intro i j N
  have hle : I ^ N ≤ (J ^ N).comap f :=
    (Ideal.pow_right_mono hf N).trans (Ideal.le_comap_pow f N)
  have := (h i j N).comp (Ideal.quotientMap (J ^ N) f hle)
  convert this using 1
  rfl

end

theorem Fr.IsPair.map {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}
    {P : PD Φ.ι Γ R} (h : Φ.IsPair a P) (f : R →+* R') : Φ.IsPair (f.comp a) (P.map f) := by
  refine ⟨fun g => isGSp_map f (h.mult g), ?_, h.nrm.map f.map_zero, ?_, ?_, ?_⟩
  · intro g hg
    rw [PD.map_r, h.kill g hg]
    exact Matrix.map_one _ f.map_zero f.map_one
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · simpa [PD.map_n] using isGSp_map f (h.low v).1
    · intro i
      rw [PD.map_n, Matrix.map_apply, (h.low v).2.1, map_one]
    · intro i j hij
      rw [PD.map_n, Matrix.map_apply, (h.low v).2.2 i j hij, map_zero]
  · intro v s hs i j hij
    rw [PD.map_flag, Matrix.map_apply, h.flag v s hs i j hij, map_zero]
  · intro v s hs i
    rw [PD.map_ψ, h.mu v s hs i, map_one]

section
variable {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  {a : O →+* Λ} (X : Space Φ a)

theorem Space.noeth : IsNoetherianRing X.A :=
  haveI := X.ft
  Algebra.FiniteType.isNoetherianRing X.B X.A

theorem Space.pair_map {R : Type} [CommRing R] [Algebra Λ R] (f : X.A →ₐ[Λ] R) :
    Φ.IsPair ((algebraMap Λ R).comp a) (X.P.map (f : X.A →+* R)) := by
  have := X.pair.map (f : X.A →+* R)
  convert this using 1
  ext x
  simp

theorem Space.cont_map {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) :
    (X.P.map (f : X.A →+* R)).Cont (maximalIdeal R) := by
  refine X.cont.map _ (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)
  show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
  rw [← res_eq_zero_iff Λ, res_map (O := Λ) (R := X.B), res_eq_zero_iff]
  exact hb

theorem Space.hom_ext {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f f' : X.A →ₐ[Λ] R)
    (h : X.P.map (f : X.A →+* R) = X.P.map (f' : X.A →+* R)) : f = f' := by
  have hr : ∀ g i j, f (X.P.r g i j) = f' (X.P.r g i j) := by
    intro g i j
    have := congrArg (fun Q => Q.r g i j) h
    exact this
  have hn : ∀ v i j, f (X.P.n v i j) = f' (X.P.n v i j) := by
    intro v i j
    have := congrArg (fun Q => Q.n v i j) h
    exact this
  have hB : f.comp (IsScalarTower.toAlgHom Λ X.B X.A) = f'.comp (IsScalarTower.toAlgHom Λ X.B X.A) := by
    apply X.genB R
    · intro g n
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [← Polynomial.coeff_map, X.cp_map]
      have e : ∀ φ : X.A →ₐ[Λ] R, φ ((X.P.r g).charpoly.coeff n) =
          (((X.P.r g).map (φ : X.A →+* R)).charpoly).coeff n := by
        intro φ
        rw [Matrix.charpoly_map, Polynomial.coeff_map]
        rfl
      rw [e f, e f']
      exact congrArg (fun Q => (Q.r g).charpoly.coeff n) h
    · intro v i s hs
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [X.ψ_map v i s hs]
      have := congrArg (fun Q => Q.ψ v i s) h
      simp only [PD.map_ψ] at this
      exact this
  ext x
  have hx : x ∈ Algebra.adjoin X.B
      ((Set.range fun x : Γ × Fin 4 × Fin 4 => X.P.r x.1 x.2.1 x.2.2) ∪
        Set.range fun x : Φ.ι × Fin 4 × Fin 4 => X.P.n x.1 x.2.1 x.2.2) := by
    rw [X.gen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩
    · exact hr g i j
    · exact hn v i j
  | algebraMap b =>
    exact DFunLike.congr_fun hB b
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

end

end UpperTheory.V.Ws
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDim
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem redDim_set {k V X : Type} [Field k] [AddCommGroup V] [Module k V] (n : ℕ)
    (h : Module.rank k V ≤ n) (M : Set X) (ev : X → Module.Dual k V) :
    ∃ S : Finset X, (S : Set X) ⊆ M ∧ S.card ≤ n ∧ ∀ v, (∀ s ∈ S, ev s v = 0) → ∀ x ∈ M, ev x v = 0 := by
  classical
  haveI : Module.Finite k V := Module.rank_lt_aleph0_iff.1 (h.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent k (ev '' M)
  have hfin : b.Finite := hli.set_finite_of_isNoetherian
  haveI := hfin.fintype
  have hcard : Fintype.card b ≤ n := by
    refine hli.fintype_card_le_finrank.trans ?_
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_le_of_rank_le h
  choose σ hσ hσ' using fun y : b => hb y.2
  refine ⟨Finset.univ.image σ, ?_, Finset.card_image_le.trans hcard, fun v hv x hx => ?_⟩
  · intro s hs
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hs
    exact hσ y
  · have h1 : ev x ∈ Submodule.span k b := hsp ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    have h2 : Submodule.span k b ≤ LinearMap.ker (Module.Dual.eval k V v) := by
      refine Submodule.span_le.2 fun y hy => ?_
      have := hv _ (Finset.mem_image_of_mem σ (Finset.mem_univ ⟨y, hy⟩))
      rw [hσ'] at this
      exact this
    exact h2 h1

private theorem redDim_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

private theorem redDim_der {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (I : Ideal R) (hIm : I ≤ maximalIdeal R) (hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I)
    (h2 : maximalIdeal R * maximalIdeal R ≤ I) (x : R) (hx : x ∈ maximalIdeal R) (hxI : x ∉ I) :
    ∃ D ∈ PtDer (res O R) (ResidueField O), D x ≠ 0 ∧ ∀ y ∈ I, D y = 0 := by
  let N : Submodule O R := I.restrictScalars O ⊔ Submodule.span O {1}
  have hIN : ∀ y ∈ I, y ∈ N := fun y hy => Submodule.mem_sup_left hy
  have hON : ∀ a : O, algebraMap O R a ∈ N := fun a =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)
  have hxN : N.mkQ x ≠ 0 := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [← Algebra.algebraMap_eq_smul_one] at hyz
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hx (hIm hy)
      rwa [← hyz, add_sub_cancel_left] at this
    have h2 : a ∈ maximalIdeal O := fun h => h1 (h.map _)
    exact hxI (hyz ▸ I.add_mem hy (hO a h2))
  have htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    show a • N.mkQ y = 0
    rw [← map_smul]
    refine (Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (hO a ha)
  obtain ⟨φ, hφ⟩ := redDim_dual O _ htor _ hxN
  let D : R →ₗ[O] ResidueField O := φ ∘ₗ N.mkQ
  have hD : ∀ y ∈ N, D y = 0 := fun y hy => by
    show φ (N.mkQ y) = 0
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  have hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a :=
    fun y a ha => by
      have := (res_eq_zero_iff O R _).2 ha
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  refine ⟨D, fun y z => ?_, hφ, fun y hy => hD y (hIN y hy)⟩
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) z
  have h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0 :=
    hD _ (hIN _ (h2 (Ideal.mul_mem_mul ha hb)))
  have h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y
      - algebraMap O R (a * b) := by
    simp only [Algebra.smul_def, map_mul]; ring
  rw [h2, map_sub, map_add (f := _), map_add (f := _), h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]; ring

theorem UpperTheory.V.Ws.redDim :
    ∀ {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (n : ℕ),
          Module.rank (ResidueField Λ) (PtDer (res Λ R) (ResidueField Λ)) ≤ n → ringKrullDim R ≤ (n + 1 : ℕ) := by
  intro Λ _ _ _ R _ _ _ n h
  classical
  let ev : R → Module.Dual (ResidueField Λ) (PtDer (res Λ R) (ResidueField Λ)) := fun x =>
    { toFun := fun D => D.1 x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  obtain ⟨S, hS, hcard, hv⟩ := redDim_set n h (maximalIdeal R) ev
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Λ
  let T : Finset R := insert (algebraMap Λ R ϖ) S
  have hT : Ideal.span (T : Set R) ≤ maximalIdeal R := by
    refine Ideal.span_le.2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact fun hu => hϖ.not_isUnit (IsLocalHom.map_nonunit ϖ hu)
    · exact hS hy
  have hle : maximalIdeal R ≤ Ideal.span (T : Set R) ⊔ maximalIdeal R * maximalIdeal R := by
    intro x hx
    by_contra hxI
    obtain ⟨D, hD, hDx, hDI⟩ := redDim_der (O := Λ) _ (sup_le hT Ideal.mul_le_right) (fun a ha => by
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.subset_span (Finset.mem_insert_self _ _))))
      le_sup_right x hx hxI
    exact hDx (hv ⟨D, hD⟩ (fun s hs =>
      hDI s (Ideal.mem_sup_left (Ideal.subset_span (Finset.mem_insert_of_mem hs)))) x hx)
  have heq : maximalIdeal R = Ideal.span (T : Set R) :=
    le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) hle) hT
  refine (ringKrullDim_le_spanFinrank_maximalIdeal R).trans ?_
  have h3 : (maximalIdeal R).spanFinrank ≤ n + 1 := by
    rw [heq]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite T.finite_toSet).trans ?_
    rw [Set.ncard_coe_finset]
    exact (Finset.card_insert_le _ _).trans (by omega)
  exact_mod_cast h3
end
