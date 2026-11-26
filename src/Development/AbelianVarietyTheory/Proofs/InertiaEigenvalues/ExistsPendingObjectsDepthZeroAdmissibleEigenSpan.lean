module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeAction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvalues
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOneOfCharpoly
open Polynomial

namespace GlobalTheory.FinOrd

theorem eq_one_of_pow_eq_one_of_charpoly (K : Type) [Field K] [CharZero K] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) K) (h : ∃ m : ℕ, 0 < m ∧ M ^ m = 1)
    (hc : M.charpoly = (X - 1) ^ N) : M = 1 := by
  obtain ⟨m, hm, hM⟩ := h
  have hpr : Prime (X - 1 : K[X]) := by simpa using prime_X_sub_C (1 : K)

  have hsep : (X ^ m - 1 : K[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero
  have h1 : minpoly K M ∣ X ^ m - 1 := minpoly.dvd_iff.2 (by simp [hM])

  have h2 : minpoly K M ∣ (X - 1) ^ N := by
    rw [← hc]; exact minpoly.dvd_iff.2 (Matrix.aeval_self_charpoly M)
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr N).1 h2

  have hsi : ((X - 1 : K[X]) ^ i).Separable := hsep.of_dvd (hi.symm.dvd.trans h1)
  have hle : minpoly K M ∣ X - 1 := by
    rcases hsi.of_pow' with hu | ⟨-, rfl⟩ | rfl
    · exact absurd hu hpr.not_unit
    · simpa using hi.dvd
    · exact hi.dvd.trans (by simp)
  have h0 : Polynomial.aeval M (X - 1 : K[X]) = 0 := minpoly.dvd_iff.1 hle
  simpa [sub_eq_zero] using h0

end GlobalTheory.FinOrd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvalues
noncomputable section

namespace GlobalTheory.PendOf.LabIneAll

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
open Polynomial GlobalTheory.Pass GlobalTheory.PendOf GlobalTheory.WeilDeligne

section Alg

theorem charpoly_pow_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) (n : ℕ) :
    (A ^ n).charpoly = (s.map fun x => X - C (f x ^ n)).prod := by
  have h1 : A.charpoly.roots = s.map f := by
    rw [h, ← roots_multiset_prod_X_sub_C (s.map f), Multiset.map_map]
    rfl
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow K r n A
  rw [(IsAlgClosed.splits (A ^ n).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _), h2, h1,
    Multiset.map_map, Multiset.map_map]
  rfl

theorem teich_zero {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

end Alg

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω}

theorem mem_of_isOpen {H : Subgroup (Ine (F := E) A)} (hH : IsOpen (H : Set (Ine (F := E) A)))
    {γ : G E Ω} (hγ : TameGenAt A γ) (h1 : (⟨γ, hγ.1⟩ : Ine (F := E) A) ∈ H)
    (hw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A → σ ∈ H) (σ : Ine (F := E) A) : σ ∈ H := by
  have hK : IsClosed ((H.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (H.isClosed_of_isOpen hH)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ H.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, hw _ hu, rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem isOfFinOrder_of_isOpen {M : Type} [Group M] (φ : Ine (F := E) A →* M)
    (hφ : IsOpen (φ.ker : Set (Ine (F := E) A))) (σ : Ine (F := E) A) : IsOfFinOrder (φ σ) := by
  have : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have : Finite (Ine (F := E) A ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ hφ
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨φ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rw [← map_pow]
  exact φ.ker.pow_index_mem σ


open Classical in
theorem charpoly_eq_of_gen {n : ℕ} (ρ : Ine (F := E) A →* GL (Fin n) ℂ)
    (hρ : ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ U → ρ σ = 1)
    {ι : Type} (s : Multiset ι) (χ : ι → G E Ω → ℂ)
    (h1 : ∀ x ∈ s, χ x 1 = 1)
    (hmul : ∀ x ∈ s, ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, χ x (σ * σ') = χ x σ * χ x σ')
    (hwild : ∀ x ∈ s, ∀ σ ∈ Wild E A, χ x σ = 1)
    (hopen : ∀ x ∈ s, ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ ∈ U, σ ∈ Ine (F := E) A → χ x σ = 1)
    {γ : G E Ω} (hγ : TameGenAt A γ)
    (hρw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A →
      ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (X - 1) ^ n)
    (hργ : ((ρ ⟨γ, hγ.1⟩ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly =
      (s.map fun x => X - C (χ x γ)).prod)
    (σ : Ine (F := E) A) :
    ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun x => X - C (χ x σ)).prod := by
  let T := s.toFinset
  let c : T → (Ine (F := E) A →* ℂˣ) := fun x => MonoidHom.toHomUnits
    { toFun := fun σ => χ x (σ : G E Ω)
      map_one' := h1 x (Multiset.mem_toFinset.1 x.2)
      map_mul' := fun σ σ' => hmul x (Multiset.mem_toFinset.1 x.2) σ σ.2 σ' σ'.2 }
  have hc : ∀ x σ, ((c x σ : ℂˣ) : ℂ) = χ x (σ : G E Ω) := fun _ _ => rfl
  let Φ : Ine (F := E) A →* GL (Fin n) ℂ × (T → ℂˣ) := ρ.prod (Pi.monoidHom c)
  obtain ⟨U, hU, hUρ⟩ := hρ
  choose V hV hVχ using fun x : T => hopen x (Multiset.mem_toFinset.1 x.2)
  let W : Set (Ine (F := E) A) := Subtype.val ⁻¹' ((U : Set (G E Ω)) ∩ ⋂ x, (V x : Set (G E Ω)))
  have hWo : IsOpen W := continuous_subtype_val.isOpen_preimage _ (hU.inter (isOpen_iInter_of_finite hV))
  have hWk : ∀ σ ∈ W, Φ σ = 1 := by
    intro σ hσ
    refine Prod.ext (hUρ σ hσ.1) (funext fun x => Units.ext ?_)
    show χ x (σ : G E Ω) = 1
    exact hVχ x σ (Set.mem_iInter.1 hσ.2 x) σ.2
  have h1W : (1 : Ine (F := E) A) ∈ W := ⟨U.one_mem, Set.mem_iInter.2 fun x => (V x).one_mem⟩
  have hker : IsOpen (Φ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (hWo.mem_nhds h1W) fun σ hσ => MonoidHom.mem_ker.2 (hWk σ hσ))
  have hkerρ : IsOpen (ρ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => MonoidHom.mem_ker.2 (congrArg Prod.fst (MonoidHom.mem_ker.1 hσ)))
      hker
  let γ' : Ine (F := E) A := ⟨γ, hγ.1⟩
  let H := (Subgroup.zpowers (Φ γ')).comap Φ
  have hH : IsOpen (H : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => Subgroup.mem_comap.2 (by
      rw [MonoidHom.mem_ker.1 hσ]; exact one_mem _)) hker
  have hσH : σ ∈ H := by
    refine mem_of_isOpen hH hγ (Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)) (fun τ hτ => ?_) σ
    refine Subgroup.mem_comap.2 ?_
    have hρ1 : ρ τ = 1 := by
      obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_isOpen ρ hkerρ τ)
      exact Units.ext (GlobalTheory.FinOrd.eq_one_of_pow_eq_one_of_charpoly ℂ n _
        ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]⟩ (hρw τ hτ))
    have hΦ1 : Φ τ = 1 := by
      refine Prod.ext hρ1 (funext fun x => Units.ext ?_)
      show χ x (τ : G E Ω) = 1
      exact hwild x (Multiset.mem_toFinset.1 x.2) τ hτ
    rw [hΦ1]
    exact one_mem _
  obtain ⟨m, hm⟩ := ((isOfFinOrder_of_isOpen Φ hker γ').mem_powers_iff_mem_zpowers).2 (Subgroup.mem_comap.1 hσH)
  have hρm : ρ σ = ρ γ' ^ m := by
    have := congrArg Prod.fst hm
    simpa [Φ] using this.symm
  have hχm : ∀ x ∈ s, χ x γ ^ m = χ x σ := by
    intro x hx
    have := congrArg (fun p : GL (Fin n) ℂ × (T → ℂˣ) => ((p.2 ⟨x, Multiset.mem_toFinset.2 hx⟩ : ℂˣ) : ℂ)) hm
    simp only [Φ, MonoidHom.prod_apply, Prod.pow_snd, Pi.pow_apply, Units.val_pow_eq_pow_val,
      Pi.monoidHom_apply] at this
    exact this
  rw [hρm, Units.val_pow_eq_pow_val, charpoly_pow_of_prod _ s (fun x => χ x γ) hργ m]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => by rw [hχm x hx])

end Local

theorem main : ∀ D : D7, IneRep D → LabDepth D → LabGen D → ∃ Ω : TameOm D, LabIne Ω := by
  intro D hR hD hG
  obtain ⟨γ, hγ, hlab⟩ := hG
  obtain ⟨Ω, hΩ⟩ := GlobalTheory.PendOf.Model.exists_tameOm D γ hγ
  refine ⟨Ω, fun k w hw L hL => ?_⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro σ hσ
  obtain ⟨ρ, hρ, hρP⟩ := hR k w hw L
  have hT : TameLP D L := ((hD k w hw L).2).1 hL
  have hγw := hγ.2 k w hw
  have hlabγ := hlab k w hw L hL
  have hs0 : ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L), x ≠ 0 := by
    intro x hx h0
    subst h0
    have hdvd : X ∣ ((ρ ⟨γ k w, hγw.1⟩ : GL (Fin (D.naut.lpDim L)) ℂ) :
        Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly := by
      rw [← hρP ⟨γ k w, hγw.1⟩]
      rw [show ((⟨γ k w, hγw.1⟩ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = γ k w from rfl, hlabγ]
      have := Multiset.dvd_prod (Multiset.mem_map_of_mem (fun x => X - C (D.ntypes.teichC k x)) hx)
      simpa [teich_zero (D.ntypes.teichC k) (D.ntypes.teichC_inj k)] using this
    rw [X_dvd_iff] at hdvd
    have hdet := Matrix.isUnits_det_units (ρ ⟨γ k w, hγw.1⟩)
    rw [Matrix.det_eq_sign_charpoly_coeff, hdvd, mul_zero] at hdet
    exact not_isUnit_zero hdet
  refine (hρP ⟨σ, hσ⟩).trans (charpoly_eq_of_gen ρ hρ _ (fun x τ => Ω.om k w x τ)
    (fun x hx => Ω.om_one k w x (hs0 x hx))
    (fun x hx => Ω.om_mul k w x (hs0 x hx))
    (fun x hx τ hτ => Ω.om_wild k w hw x (hs0 x hx) τ hτ)
    (fun x hx => Ω.om_open k w x (hs0 x hx)) hγw
    (fun τ hτ => (hρP τ).symm.trans (hT τ τ.2 hτ)) ?_ ⟨σ, hσ⟩)
  rw [← hρP ⟨γ k w, hγw.1⟩]
  refine hlabγ.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => ?_))
  rw [hΩ k w hw x (hs0 x hx)]

end GlobalTheory.PendOf.LabIneAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvaluesStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_label_inertia_eigenvalues : ∀ D : D7, IneRep D → LabDepth D → LabGen D → ∃ Ω : TameOm D, LabIne Ω := by
  first | exact @GlobalTheory.PendOf.LabIneAll.main | exact GlobalTheory.PendOf.LabIneAll.main | (intros; apply GlobalTheory.PendOf.LabIneAll.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingData
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotent
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PrimCentIdem

open CategoryTheory

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem eq_sum_single (e : MonoidAlgebra ℂ Γ) : e = ∑ q : Γ, MonoidAlgebra.single q (e.coeff q) := by
  classical
  ext x
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul_fin (a b : MonoidAlgebra ℂ Γ) (x : Γ) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

theorem exists_scalar (e : MonoidAlgebra ℂ Γ) (he : ∀ w, e * w = w * e) (ρ : FDRep ℂ Γ) [Simple ρ] :
    ∃ c : ℂ, ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v := by
  let T : ρ →ₗ[ℂ] ρ := ∑ q : Γ, e.coeff q • ρ.ρ q
  have hTA : T = Representation.asAlgebraHom ρ.ρ e := by
    conv_rhs => rw [eq_sum_single e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, map_sum, Representation.asAlgebraHom_single]
  have hcomm : ∀ h : Γ, ∀ v : ρ, T (ρ.ρ h v) = ρ.ρ h (T v) := by
    intro h v
    have h1 : Representation.asAlgebraHom ρ.ρ (e * MonoidAlgebra.single h 1) = Representation.asAlgebraHom ρ.ρ (MonoidAlgebra.single h 1 * e) := by
      rw [he]
    rw [map_mul, map_mul, Representation.asAlgebraHom_single, one_smul] at h1
    rw [hTA]
    exact LinearMap.congr_fun h1 v
  let f' : ρ ⟶ ρ := ⟨FGModuleCat.ofHom T, fun g => by
    ext v
    exact hcomm g v⟩
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f'
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun φ : ρ ⟶ ρ => φ.hom.hom v) hc
  exact this.symm

theorem mul_zIdem_eq_smul (e : MonoidAlgebra ℂ Γ) (ρ : FDRep ℂ Γ) (c : ℂ)
    (hc : ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v) :
    e * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ = c • Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  ext x
  rw [coeff_mul_fin, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  have hT : (∑ q : Γ, e.coeff q • ρ.ρ q) = c • (1 : Module.End ℂ ρ) := LinearMap.ext fun v => by simp [hc v]
  have h1 : ∀ q : Γ, ρ.ρ (q⁻¹ * x)⁻¹ = ρ.ρ x⁻¹ * ρ.ρ q := fun q => by rw [mul_inv_rev, inv_inv, map_mul]
  have h2 : ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) =
      LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ∑ q : Γ, e.coeff q • ρ.ρ q) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  have h3 : ∑ q : Γ, e.coeff q * ((Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ ρ (ρ.ρ (q⁻¹ * x)⁻¹)) =
      (Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h1]; ring
  rw [h3, h2, hT, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
  ring

end GlobalTheory.PrimCentIdem

open GlobalTheory.PrimCentIdem in
theorem GlobalTheory.PrimCentIdem.main : ∀ (g a : ℕ) [Fact g.Prime] (L : PairedCharacterCondition.LzData g) (τ : L.Irr a),
    ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧ L.idem τ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  intro g a _ L τ
  classical
  obtain ⟨hfin, hsum⟩ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one (GL (Fin a) (ZMod g))
  have hex : ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧
      L.idem τ * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply L.idem_ne τ
    rw [← mul_one (L.idem τ), ← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨ρ, hρ, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hz
    exact hno ρ hρ
  obtain ⟨ρ, hρ, hne⟩ := hex
  haveI := hρ
  refine ⟨ρ, hρ, ?_⟩
  set e := L.idem τ with he_def
  set z := Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ with hz_def
  have hzz : z * z = z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).1
  have hee : e * e = e := L.idem_idem τ
  have hec : ∀ w, e * w = w * e := L.idem_central τ
  have hzc : ∀ w, z * w = w * z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  obtain ⟨c, hc⟩ := exists_scalar e hec ρ
  have hmul : e * z = c • z := mul_zIdem_eq_smul e ρ c hc
  have hze : z * e = e * z := hzc e
  have hprim := L.idem_prim τ (e * z)
    (calc e * z * (e * z) = e * (z * e) * z := by simp only [mul_assoc]
      _ = e * (e * z) * z := by rw [hze]
      _ = (e * e) * (z * z) := by simp only [mul_assoc]
      _ = e * z := by rw [hee, hzz])
    (fun w => calc e * z * w = e * (z * w) := mul_assoc _ _ _
      _ = e * (w * z) := by rw [hzc w]
      _ = (e * w) * z := (mul_assoc _ _ _).symm
      _ = (w * e) * z := by rw [hec w]
      _ = w * (e * z) := mul_assoc _ _ _)
    (show e * z * e = e * z from calc e * z * e = e * (z * e) := mul_assoc _ _ _
      _ = e * (e * z) := by rw [hze]
      _ = (e * e) * z := (mul_assoc _ _ _).symm
      _ = e * z := by rw [hee])
  have hez : e * z = e := hprim.resolve_left hne
  have hcz : c • z ≠ 0 := hmul ▸ hne
  have hc0 : c ≠ 0 := fun h => hcz (by rw [h, zero_smul])
  have hz0 : z ≠ 0 := fun h => hcz (by rw [h, smul_zero])
  have hidem : (c * c - c) • z = 0 := by
    have h1 : (c • z) * (c • z) = c • z := by rw [← hmul, hez, hee]
    rw [smul_mul_smul_comm, hzz] at h1
    rw [sub_smul, h1, sub_self]
  have hcc : c * c - c = 0 := (smul_eq_zero.1 hidem).resolve_right hz0
  have hc1 : c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact hcc
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc0
    · exact sub_eq_zero.1 h
  rw [← hez, hmul, hc1, one_smul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotentStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent : ∀ (g a : ℕ) [Fact g.Prime] (L : PairedCharacterCondition.LzData g) (τ : L.Irr a), ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧ L.idem τ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  first | exact @GlobalTheory.PrimCentIdem.main | exact GlobalTheory.PrimCentIdem.main | (intros; apply GlobalTheory.PrimCentIdem.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingData
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.AdmDepthZero

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  intro D P h i k v PI τ hτ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro hsq hu
  obtain ⟨ρ, hρ, he⟩ := GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent (D.host.g k) D.R.r (P.lz k) τ
  have hO := PairedCharacterCondition.RT.ktyTie_of_spec P i PI k v τ hτ
  rw [he] at hO
  have hs : Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k ((P.lz k).lab τ) =
      Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
    rw [← he]
    exact PairedCharacterCondition.RT.idem_mul_eSer P k τ
  exact h i k v PI ρ _ hρ hs hO hsq hu

end GlobalTheory.AdmDepthZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingDataStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZeroAdmissible_all_pending_data : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  first | exact @GlobalTheory.AdmDepthZero.main | exact GlobalTheory.AdmDepthZero.main | (intros; apply GlobalTheory.AdmDepthZero.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTame
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTame
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.ParOfPoint

theorem inePol_foldr (D : D7) {w : PlE D.host} (x : D.naut.LP w) {α : Type} (c : α → ℝ) (l : List α)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw x (c k)) acc) (D.naut.lpZero w)) σ =
      D.naut.inePol x σ ^ l.length := by
  induction l with
  | nil =>
    have h := ((D.naut.unr_iff_ine (D.naut.lpZero w)).1 (D.naut.lpZero_unr w)).2 σ hσ
    rw [D.naut.lpDim_zero, pow_zero] at h
    simpa using h
  | cons k l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.inePol_sum, D.naut.inePol_tw _ _ σ hσ, ih, pow_succ, mul_comm]

theorem inePol_twistIso (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut) (L : List (Part D.naut.CG)) (w : PlE D.host)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w) σ =
      D.naut.inePol (isoLoc D.nd D.naut L w) σ := by
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hu : D.naut.inePol (D.naut.locG D.naut.etaTinv w) σ = X - C 1 := by
    have h := ((D.naut.unr_iff_ine _).1 (D.naut.etaTinv_def w).1).2 σ hσ
    rw [hd, pow_one] at h
    rw [h, map_one]
  have hpart : ∀ {a : ℕ} (π : D.naut.CG a),
      D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) σ = D.naut.inePol (D.naut.locG π w) σ := by
    intro a π
    rw [D.naut.locG_tw, ((hT w (D.naut.locG π w) (D.naut.locG π w) _ _ 0 hd hd).2.2.2.2.2 σ hσ).2 1 hu,
      Polynomial.scaleRoots_one]
  induction L with
  | nil => rfl
  | cons p L ih =>
    show D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ w)
      (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w)) σ =
      D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut p w) (isoLoc D.nd D.naut L w)) σ
    rw [D.naut.inePol_sum, D.naut.inePol_sum, ih]
    unfold spehLoc
    rw [inePol_foldr D _ _ _ σ hσ, inePol_foldr D _ _ _ σ hσ, hpart]

theorem eq_pow_of_mul_eq (A B : ℂ[X]) (n : ℕ) (hA : A.Monic) (hB : B.Monic) (h : A * B = (X - 1) ^ n) :
    A = (X - 1) ^ A.natDegree := by
  have hdvd : A ∣ (X - C 1) ^ n := by rw [map_one, ← h]; exact dvd_mul_right A B
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) n).1 hdvd
  have e := Polynomial.eq_of_monic_of_associated hA ((monic_X_sub_C (1 : ℂ)).pow j) hj
  rw [e, (monic_X_sub_C (1 : ℂ)).natDegree_pow, natDegree_X_sub_C, mul_one, map_one]

theorem tw_back (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).2)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem main : ∀ D : D7, (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → LabDepth D → DepthZ D → ParSurj D := by
  intro D hPar h0 h5 hsplit hLab hDZ i x Sig hX
  obtain ⟨P, -, hB⟩ := hX
  have hT : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hAN := h5.1
  set χ := D.naut.etaTinv with hχ
  have htw : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ =
      twistIso D.nd D.naut Sig χ ++ twistIso D.nd D.naut [muPart D.nd D.naut i] χ := List.map_append

  have hparts : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π := by
    intro p hp
    have hm : (⟨p.a, D.naut.tw p.π χ, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ := by
      rw [htw]
      exact List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨ha, hd, hc⟩ := hB.1 _ hm
    refine ⟨ha, hd, ?_⟩
    have e := tw_back D hT hAN ha p.π
    rw [← e]
    exact D.naut.csd_tw _ _ h0.2.1.1.1 hc

  have hnodup : (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup := by
    have h2 := hB.2.1
    rw [htw, List.map_append] at h2
    have h3 := (List.nodup_append.1 h2).1
    have e : (twistIso D.nd D.naut Sig χ).map (fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) =
        (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).map
          (fun q => ((⟨q.1.1, D.naut.tw q.1.2 χ⟩ : Σ a, D.naut.CG a), q.2)) := by
      unfold twistIso
      rw [List.map_map, List.map_map]
      rfl
    rw [e] at h3
    exact h3.of_map _

  have hrank : rankIso D.nd D.naut Sig = D.R.r := by
    have hr := hB.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ) =
        rankIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1] at hr
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

  have hlab : ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
    intro k v
    set w := D.naut.plGw k v with hw
    have hover := D.naut.plGw_over k v
    obtain ⟨hmon, hiff⟩ := hLab k w hover (isoLoc D.nd D.naut Sig w)
    refine ⟨hmon, ?_⟩
    rw [← hrank, ← lpDim_isoLoc]
    apply hiff.2
    intro σ hσ hwild
    have hloc := hB.2.2.2.1 w (hsplit k v)
    have htame := hDZ i P k w hover σ hσ hwild
    rw [← hloc, inePol_twistIso D hT _ w σ hσ, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.inePol_sum] at htame
    have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ w
    have hm1 := ((hT w (isoLoc D.nd D.naut Sig w) (isoLoc D.nd D.naut Sig w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have hm2 := ((hT w (isoLoc D.nd D.naut [muPart D.nd D.naut i] w)
      (isoLoc D.nd D.naut [muPart D.nd D.naut i] w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have e := eq_pow_of_mul_eq _ _ _ hm1.1 hm2.1 htame
    rw [e, hm1.2]
  exact hPar ⟨Sig, hparts, hnodup, hrank, hlab⟩

end GlobalTheory.ParOfPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTameStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointParameterIsTypeParameter_of_tame : ∀ D : D7, (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → LabDepth D → DepthZ D → ParSurj D := by
  first | exact @GlobalTheory.ParOfPoint.main | exact GlobalTheory.ParOfPoint.main | (intros; apply GlobalTheory.ParOfPoint.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSums
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSums
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.LzExist

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

def IsDecomp (S : Finset A) : Prop :=
  (∀ e ∈ S, e * e = e) ∧ (∀ e ∈ S, ∀ z : A, e * z = z * e) ∧ (∀ e ∈ S, e ≠ 0) ∧
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → e * f = 0) ∧ ∑ e ∈ S, e = 1

def IsPrim (S : Finset A) : Prop :=
  ∀ t ∈ S, ∀ x : A, x * x = x → (∀ z, x * z = z * x) → x * t = x → x = 0 ∨ x = t

theorem linInd {S : Finset A} (h : IsDecomp S) : LinearIndependent ℂ (fun x : S => (x : A)) := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h1 : (∑ j ∈ s, c j • (j : A)) * (i : A) = c i • (i : A) := by
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    · rw [smul_mul_assoc, h.1 _ i.2]
    · intro j _ hji
      rw [smul_mul_assoc, h.2.2.2.1 _ j.2 _ i.2 (fun e => hji (Subtype.ext e)), smul_zero]
    · intro h'; exact absurd hi h'
  rw [hs, zero_mul] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right (h.2.2.1 _ i.2)

theorem card_le [Module.Finite ℂ A] {S : Finset A} (h : IsDecomp S) : S.card ≤ Module.finrank ℂ A := by
  have := (linInd h).fintype_card_le_finrank
  simpa using this

theorem refine_decomp [DecidableEq A] {S : Finset A} (h : IsDecomp S) {t : A} (ht : t ∈ S) {x : A}
    (hx : x * x = x) (hc : ∀ z, x * z = z * x) (hxt : x * t = x) (h0 : x ≠ 0) (ht' : x ≠ t) :
    IsDecomp (insert x (insert (t - x) (S.erase t))) ∧
      (insert x (insert (t - x) (S.erase t))).card = S.card + 1 := by
  obtain ⟨hI, hC, hN, hO, hS⟩ := h
  have htx : t * x = x := by rw [← hc t, hxt]
  have hxs : ∀ s ∈ S.erase t, x * s = 0 := by
    intro s hs
    obtain ⟨hst, hs⟩ := Finset.mem_erase.1 hs
    rw [← hxt, mul_assoc, hO t ht s hs (Ne.symm hst), mul_zero]
  have hsx : ∀ s ∈ S.erase t, s * x = 0 := fun s hs => by rw [← hc s]; exact hxs s hs
  have hts : ∀ s ∈ S.erase t, (t - x) * s = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [sub_mul, hO t ht s hs' (Ne.symm hst), hxs s hs, sub_zero]
  have hst' : ∀ s ∈ S.erase t, s * (t - x) = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [mul_sub, hO s hs' t ht hst, hsx s hs, sub_zero]
  have hxtx : x * (t - x) = 0 := by rw [mul_sub, hxt, hx, sub_self]
  have htxx : (t - x) * x = 0 := by rw [sub_mul, htx, hx, sub_self]
  have htt : (t - x) * (t - x) = t - x := by
    rw [mul_sub, htxx, sub_zero, sub_mul, hI t ht, hxt]
  have htx0 : t - x ≠ 0 := fun h => ht' (sub_eq_zero.1 h).symm
  have hnot : ∀ y, y * y = y → y ≠ 0 → (∀ s ∈ S.erase t, y * s = 0) → y ∉ S.erase t := by
    intro y hy hy0 hys hmem
    exact hy0 (by rw [← hy]; exact hys y hmem)
  have hm1 : t - x ∉ S.erase t := hnot _ htt htx0 hts
  have hm2 : x ∉ insert (t - x) (S.erase t) := by
    rw [Finset.mem_insert, not_or]
    refine ⟨fun e => h0 ?_, hnot _ hx h0 hxs⟩
    rw [← hx]; nth_rewrite 2 [e]; exact hxtx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hx
    · exact htt
    · exact hI e (Finset.mem_of_mem_erase he)
  · intro e he z
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hc z
    · rw [sub_mul, mul_sub, hC t ht z, hc z]
    · exact hC e (Finset.mem_of_mem_erase he) z
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact h0
    · exact htx0
    · exact hN e (Finset.mem_of_mem_erase he)
  · intro e he f hf hef
    rw [Finset.mem_insert, Finset.mem_insert] at he hf
    rcases he with rfl | rfl | he <;> rcases hf with rfl | rfl | hf
    · exact absurd rfl hef
    · exact hxtx
    · exact hxs f hf
    · exact htxx
    · exact absurd rfl hef
    · exact hts f hf
    · exact hsx e he
    · exact hst' e he
    · exact hO e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef
  · rw [Finset.sum_insert hm2, Finset.sum_insert hm1, ← add_assoc, add_sub_cancel,
      Finset.add_sum_erase S (fun e => e) ht, hS]
  · rw [Finset.card_insert_of_notMem hm2, Finset.card_insert_of_notMem hm1,
      Finset.card_erase_of_mem ht]
    have := Finset.card_pos.2 ⟨t, ht⟩
    omega

theorem exists_prim [Module.Finite ℂ A] [Nontrivial A] : ∃ S : Finset A, IsDecomp S ∧ IsPrim S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset A, IsDecomp S ∧ S.card = n
  have h1 : P 1 := ⟨{1}, ⟨by simp, by simp, by simp, by simp, by simp⟩, by simp⟩
  have hb : ∀ n, P n → n ≤ Module.finrank ℂ A := by
    rintro n ⟨S, hS, rfl⟩; exact card_le hS
  obtain ⟨S, hS, hc⟩ := Nat.findGreatest_spec (P := P) (m := 1) (n := Module.finrank ℂ A) (hb 1 h1) h1
  refine ⟨S, hS, ?_⟩
  intro t ht x hx hc' hxt
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h2, h3⟩ := refine_decomp hS ht hx hc' hxt hne.1 hne.2
  have := Nat.le_findGreatest (P := P) (hb _ ⟨_, h2, rfl⟩) ⟨_, h2, rfl⟩
  omega

theorem lab_unique {ι : Type} {S : Finset A} (hS : IsDecomp S) (hP : IsPrim S) (e : ι → A)
    (he_idem : ∀ i, e i * e i = e i) (he_c : ∀ i z, e i * z = z * e i)
    (he_o : ∀ i j, i ≠ j → e i * e j = 0) (T : Finset ι) (hT : ∑ i ∈ T, e i = 1) {t : A} (ht : t ∈ S) :
    ∃ i ∈ T, e i * t = t ∧ ∀ j, j ≠ i → e j * t = 0 := by
  have key : ∀ j, e j * t = 0 ∨ e j * t = t := by
    intro j
    refine hP t ht _ ?_ ?_ ?_
    · rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e j), mul_assoc, hS.1 t ht, ← mul_assoc, he_idem]
    · intro z
      rw [mul_assoc, hS.2.1 t ht z, ← mul_assoc, he_c j z, mul_assoc]
    · rw [mul_assoc, hS.1 t ht]
  have hsum : ∑ j ∈ T, e j * t = t := by rw [← Finset.sum_mul, hT, one_mul]
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hS.2.2.1 t ht)
  have hit : e i * t = t := (key i).resolve_left hne
  refine ⟨i, hi, hit, fun j hji => (key j).resolve_right fun hjt => hS.2.2.1 t ht ?_⟩
  have h0 : (e j * t) * (e i * t) = 0 := by
    rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e i), mul_assoc, ← mul_assoc (e j), he_o j i hji,
      zero_mul]
  rw [hjt, hit, hS.1 t ht] at h0
  exact h0

end Alg

section Lz

variable (g r : ℕ) [Fact g.Prime] (e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)))

abbrev GA (a : ℕ) : Type := MonoidAlgebra ℂ (GL (Fin a) (ZMod g))

def decS (a : ℕ) : Finset (GA g a) := (exists_prim (A := GA g a)).choose

theorem decS_spec (a : ℕ) : IsDecomp (decS g a) ∧ IsPrim (decS g a) :=
  (exists_prim (A := GA g a)).choose_spec

def LabQ (a : ℕ) (x : GA g a) (f : (ZMod g)[X]) : Prop :=
  (f.Monic ∧ f.natDegree = a ∧ f.coeff 0 ≠ 0) ∧
    ∀ h : a = r, e f * cast (congrArg (GA g) h) x = cast (congrArg (GA g) h) x


open Classical in
def labF (a : ℕ) (x : GA g a) : (ZMod g)[X] :=
  if h : ∃ f, LabQ g r e a x f then h.choose else (X - C 1) ^ a

theorem labF_spec (a : ℕ) (x : GA g a) :
    (labF g r e a x).Monic ∧ (labF g r e a x).natDegree = a ∧ (labF g r e a x).coeff 0 ≠ 0 := by
  unfold labF
  split_ifs with h
  · exact h.choose_spec.1
  · refine ⟨(monic_X_sub_C 1).pow a, ?_, ?_⟩
    · rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    · rw [coeff_zero_eq_eval_zero]; simp

def lzE : PairedCharacterCondition.LzData g where
  Irr a := ↥(decS g a)
  finIrr a := inferInstance
  idem τ := τ.1
  idem_idem τ := (decS_spec g _).1.1 _ τ.2
  idem_central τ z := (decS_spec g _).1.2.1 _ τ.2 z
  idem_ne τ := (decS_spec g _).1.2.2.1 _ τ.2
  idem_orth τ σ h := (decS_spec g _).1.2.2.2.1 _ τ.2 _ σ.2 (fun e => h (Subtype.ext e))
  idem_sum a := by
    rw [Finset.sum_coe_sort (decS g a) (fun x => x)]; exact (decS_spec g a).1.2.2.2.2
  idem_prim τ x hx hc hxt := (decS_spec g _).2 _ τ.2 x hx hc hxt
  lab τ := labF g r e _ τ.1
  lab_spec τ := labF_spec g r e _ τ.1
  Rep a := Set ↥(decS g a)
  ofIrr τ := {τ}
  cons R τ := τ ∈ R
  cons_ofIrr _ _ := Set.mem_singleton_iff
  hc _ _ := ∅

open Classical in
theorem lzE_ser (hidem : ∀ f, e f * e f = e f) (hcen : ∀ f a, e f * a = a * e f)
    (horth : ∀ f f', f ≠ f' → e f * e f' = 0)
    (hsum : ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧
      ∑ f ∈ S, e f = 1) (f : (ZMod g)[X]) :
    e f = ∑ τ : (lzE g r e).Irr r, if (lzE g r e).lab τ = f then (lzE g r e).idem τ else 0 := by
  obtain ⟨T, hTm, hT⟩ := hsum
  have hmain : ∀ t ∈ decS g r, ∀ f, e f * t = if labF g r e r t = f then t else 0 := by
    intro t ht f
    obtain ⟨i, hi, hit, hj⟩ :=
      lab_unique (decS_spec g r).1 (decS_spec g r).2 e hidem hcen horth T hT ht
    have hlab : labF g r e r t = i := by
      have hex : ∃ f, LabQ g r e r t f := ⟨i, (hTm i).1 hi, fun h => by simp only [cast_eq]; exact hit⟩
      have hs := hex.choose_spec.2 rfl
      simp only [cast_eq] at hs
      unfold labF
      rw [dite_eq_left hex]
      by_contra hne
      exact (decS_spec g r).1.2.2.1 t ht (hs.symm.trans (hj _ hne))
    rw [hlab]
    split_ifs with hif
    · subst hif; exact hit
    · exact hj f (Ne.symm hif)
  show e f = ∑ τ : ↥(decS g r), if labF g r e r τ.1 = f then τ.1 else 0
  calc e f = e f * ∑ τ : ↥(decS g r), τ.1 := by
        rw [Finset.sum_coe_sort (decS g r) (fun x => x), (decS_spec g r).1.2.2.2.2, mul_one]
    _ = ∑ τ : ↥(decS g r), e f * τ.1 := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun τ _ => hmain τ.1 τ.2 f

end Lz

theorem exists_lz_serEq : ∀ D : D7, ∃ lz : ∀ k : Fin 2, PairedCharacterCondition.LzData (D.host.g k), SerEq D lz := by
  intro D
  refine ⟨fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩;
    lzE (D.host.g k) D.R.r (D.ntypes.eSer k), ?_⟩
  intro k f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  exact lzE_ser _ _ _ (D.ntypes.eSer_idem k) (D.ntypes.eSer_central k) (D.ntypes.eSer_orth k)
    (D.ntypes.eSer_sum k) f

end GlobalTheory.LzExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSumsStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteGroupData_seriesIdempotentsLabelSums : ∀ D : D7, ∃ lz : ∀ k : Fin 2, PairedCharacterCondition.LzData (D.host.g k), SerEq D lz := by
  first | exact @GlobalTheory.LzExist.exists_lz_serEq | exact GlobalTheory.LzExist.exists_lz_serEq | (intros; apply GlobalTheory.LzExist.exists_lz_serEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabels
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabels
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.TwistLabel

theorem teich_zero' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

theorem teich_injective' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : Function.Injective t := by
  have h0 := teich_zero' t ht
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  intro x y h
  by_cases hx : x = 0
  · by_contra hxy
    exact hne y (fun hy => hxy (hx.trans hy.symm)) (by rw [← h, hx, h0])
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem prod_scaleRoots {α : Type*} (s : Multiset α) (f : α → ℂ) (c : ℂ) :
    ((s.map fun x => X - C (f x)).prod).scaleRoots c = (s.map fun x => X - C (f x * c)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s IH =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots', X_sub_C_scaleRoots, IH,
      Multiset.map_cons, Multiset.prod_cons]
    rw [leadingCoeff_X_sub_C, one_mul, ne_eq, leadingCoeff_eq_zero]
    exact (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C _).ne_zero

theorem roots_prod_map {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ((s.map fun x => X - C (f x)).prod).roots = s.map f := by
  rw [show (s.map fun x => X - C (f x)) = (s.map f).map (fun a => X - C a) by rw [Multiset.map_map]; rfl]
  exact roots_multiset_prod_X_sub_C _

end GlobalTheory.TwistLabel

open GlobalTheory.TwistLabel in
theorem main : ∀ D : D7, SumRepresentations.tie0 D → IneRep D → LabDepth D → LabGen D → LabChar D := by
  intro D hT _ hDep hGen k w hw L χ u hL hχ hχl
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ, hG⟩ := hGen
  have hLP := hT.1
  have hγI : γ k w ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := (hγ.2 k w hw).1
  have hdim : D.naut.lpDim (D.naut.lpChar L χ) = D.naut.lpDim L := D.naut.lpDim_char L χ hχ
  have hχdeg : (D.naut.items₂ k w χ).natDegree = D.naut.lpDim χ := by rw [hχl, natDegree_X_sub_C, hχ]
  have hχtame : TameLP D χ := ((hDep k w hw χ).2).1 hχdeg
  have hLtame : TameLP D L := ((hDep k w hw L).2).1 hL
  have hLχtame : TameLP D (D.naut.lpChar L χ) := by
    intro σ hσ hwσ
    have h1 := hχtame σ hσ hwσ
    rw [hχ, pow_one] at h1
    have h2 := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 σ hσ).2 1 (by rw [h1, map_one])
    rw [h2, hLtame σ hσ hwσ, scaleRoots_one, hdim]
  have hfull : (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L := by
    rw [← hdim]; exact ((hDep k w hw _).2).2 hLχtame
  refine ⟨hfull, ?_⟩
  set u' := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) with hu'
  have hrχ : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w χ) = {u'} := by
    rw [hχl, Formalism.CyclotomicNorms.rootsBar, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]
  have hχγ : D.naut.inePol χ (γ k w) = X - C (D.ntypes.teichC k u') := by
    rw [hG k w hw χ hχdeg, hrχ]; simp
  have hsc := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 (γ k w) hγI).2 _ hχγ
  rw [hG k w hw L hL, prod_scaleRoots, hG k w hw _ (hfull.trans hdim.symm)] at hsc
  have hr := congrArg Polynomial.roots hsc
  rw [roots_prod_map, roots_prod_map] at hr
  have hinj := teich_injective' (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  apply Multiset.map_injective hinj
  rw [hr, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp, map_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabelsStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelTwistMultipliesRoots_of_tame_labels : ∀ D : D7, SumRepresentations.tie0 D → IneRep D → LabDepth D → LabGen D → LabChar D := by
  first | exact @main | exact main | (intros; apply main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpan
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.PendClose

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) →
    SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D →
    SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  intro D M hT hR hA hPar h0 h5 hIne hDep hGen hZL hCI hCT hSer hZeta hDZ hAdm
  have hSU : GlobalTheory.EtaJoin.SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hSec : ∀ i, Nonempty (Sec D i) := fun i =>
    GlobalTheory.T.nonempty_localised_forms_type_section_hecke D M i hT hR hA hSU (GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M hT hA i)
  obtain ⟨lz, hlz⟩ := GlobalTheory.T.exists_finiteGroupData_seriesIdempotentsLabelSums D
  obtain ⟨Ω, hΩ⟩ := GlobalTheory.T.exists_label_inertia_eigenvalues D hIne hDep hGen
  have hChar : LabChar D := GlobalTheory.T.labelTwistMultipliesRoots_of_tame_labels D h0 hIne hDep hGen
  obtain ⟨Z⟩ := GlobalTheory.T.nonempty_groupAlgebraCentreLatticeAction D hSec hZL hCI hCT
  have hPr : PrType D := GlobalTheory.T.typeSpaceProjectionEigen_of_localisedFormsSection D hSec
  have hSplit : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v) := fun k v =>
    GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  have hPS : ParSurj D := GlobalTheory.T.pointParameterIsTypeParameter_of_tame D hPar h0 h5 hSplit hDep hDZ
  let P : PairedCharacterCondition.Pend D := mk lz hlz hSer hZeta Ω hΩ hChar Z hZL hPr hPS
  exact ⟨P, GlobalTheory.T.depthZeroAdmissible_all_pending_data D P hAdm, GlobalTheory.T.centralActsOnHeckeEigenspace_of_typeSections D P hSec hCT⟩

end GlobalTheory.PendClose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpanStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M → (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D → SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  first | exact @GlobalTheory.PendClose.main | exact GlobalTheory.PendClose.main | (intros; apply GlobalTheory.PendClose.main <;> assumption)
end
