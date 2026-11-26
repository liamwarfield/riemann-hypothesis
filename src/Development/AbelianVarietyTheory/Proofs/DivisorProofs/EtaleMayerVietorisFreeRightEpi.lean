module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpi
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEpi

theorem exists_prime_over (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)
    (hs : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (hi : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})
    (p : PrimeSpectrum A) (hp : f ∈ p.asIdeal) :
    ∃ q : PrimeSpectrum A', PrimeSpectrum.comap (algebraMap A A') q = p := by
  set I : Ideal A := Ideal.span {f} with hI
  set J : Ideal A' := Ideal.span {algebraMap A A' f} with hJ
  have hIJ : I ≤ J.comap (algebraMap A A') := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span rfl
  let φ : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J (algebraMap A A') hIJ
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hi a ha)
    · intro b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨a, ha⟩ := hs b
      refine ⟨Ideal.Quotient.mk I a, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
      have := J.neg_mem ha
      simpa using this
  let e : A ⧸ I ≃+* A' ⧸ J := RingEquiv.ofBijective φ hφ
  have hIp : I ≤ p.asIdeal := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hp
  let p0 : Ideal (A ⧸ I) := p.asIdeal.map (Ideal.Quotient.mk I)
  have hp0 : p0.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  let q : Ideal A' := (p0.comap (e.symm : A' ⧸ J →+* A ⧸ I)).comap (Ideal.Quotient.mk J)
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨⟨q, hq⟩, ?_⟩
  ext a
  have he : e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) = Ideal.Quotient.mk I a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  change Ideal.Quotient.mk J (algebraMap A A' a) ∈ p0.comap (e.symm : A' ⧸ J →+* A ⧸ I) ↔ a ∈ p.asIdeal
  rw [Ideal.mem_comap]
  change e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) ∈ p0 ↔ _
  rw [he]
  exact Ideal.mem_quotient_iff_mem hIp

theorem loc_point {X B : Scheme.{0}} (e : B ⟶ X) [Etale e] {T : Scheme.{0}} (x : T ⟶ X) (t : T)
    (ht : x t ∈ Set.range e) :
    ∃ (V : Scheme.{0}) (g : V ⟶ T), IsAffine V ∧ Etale g ∧ t ∈ Set.range g ∧ ∃ y : V ⟶ B, y ≫ e = g ≫ x := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := e) t b hb.symm
  obtain ⟨W0, hW, hzW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (pullback x e).isBasis_affineOpens)
    (show z ∈ (⊤ : (pullback x e).Opens) from trivial)
  let W : (pullback x e).Opens := W0
  haveI : IsAffine W := hW
  refine ⟨W, W.ι ≫ pullback.fst x e, inferInstance, inferInstance, ⟨⟨z, hzW⟩, ?_⟩, W.ι ≫ pullback.snd x e, ?_⟩
  · exact hz1
  · simp [pullback.condition]

theorem epi_of_loc (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E)
    (h : ∀ (T : Scheme.{0}) (x : E.obj (op T)),
      Loc T fun (V : Scheme.{0}) (k : V ⟶ T) => (∃ y, f.app (op V) y = E.map k.op x) ∨ (∃ y, g.app (op V) y = E.map k.op x)) :
    Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  refine ⟨fun {F} φ ψ hφψ => ?_⟩
  have ef : (free R).map f ≫ φ = (free R).map f ≫ ψ := by
    simpa using congrArg (biprod.inl ≫ ·) hφψ
  have eg : (free R).map g ≫ φ = (free R).map g ≫ ψ := by
    simpa using congrArg (biprod.inr ≫ ·) hφψ
  have res_map : ∀ {G H : Shv R} (χ : G ⟶ H) {V U : Scheme.{0}} (k : V ⟶ U) (s : Sec G U),
      Sec.res k (Sec.map χ s) = Sec.map χ (Sec.res k s) := by
    intro G H χ V U k s
    exact (NatTrans.naturality_apply χ.hom k.op s).symm
  have map_comp : ∀ {G H K : Shv R} (χ : G ⟶ H) (ω : H ⟶ K) {U : Scheme.{0}} (s : Sec G U),
      Sec.map (χ ≫ ω) s = Sec.map ω (Sec.map χ s) := by
    intros; rfl
  obtain ⟨-, hext, hres, -⟩ := GlobalTheory.T.free_sections_ext_res_map R E F
  obtain ⟨-, -, -, hmapP⟩ := GlobalTheory.T.free_sections_ext_res_map R P F
  obtain ⟨-, -, -, hmapQ⟩ := GlobalTheory.T.free_sections_ext_res_map R Q F
  apply hext
  intro T x
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1
  obtain ⟨S, hS, hP⟩ := h T x
  refine ⟨S, hS, fun V k hk => ?_⟩
  rcases hP V k hk with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [res_map, res_map, hres, ← hy, ← hmapP, ← map_comp, ← map_comp, ef]
  · rw [res_map, res_map, hres, ← hy, ← hmapQ, ← map_comp, ← map_comp, eg]

end GlobalTheory.EtC.MVEpi

namespace GlobalTheory.EtC.MVEpi

theorem mv_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) →
    (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) →
    Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  intro R _ A A' _ _ _ _ f hs hi
  haveI hd : Etale (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  apply epi_of_loc
  intro T (x : T ⟶ Spec (CommRingCat.of A))
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    by_cases hf : f ∈ (x t).asIdeal
    · obtain ⟨q, hq⟩ := exists_prime_over A A' f hs hi (x t) hf
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A A'))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inr ⟨y, hy⟩⟩
    · have hr : x t ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
        exact hf
      obtain ⟨q, hq⟩ := hr
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inl ⟨y, hy⟩⟩
  · rintro V W g k (⟨y, hy⟩ | ⟨y, hy⟩)
    · refine Or.inl ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]
    · refine Or.inr ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]

end GlobalTheory.EtC.MVEpi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleMayerVietoris_free_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  first | (exact @GlobalTheory.EtC.MVEpi.mv_right_epi) | (exact GlobalTheory.EtC.MVEpi.mv_right_epi) | (intros; apply GlobalTheory.EtC.MVEpi.mv_right_epi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebra
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD


set_option maxHeartbeats 1000000 in
open TensorProduct in
theorem exists_notMem_smul_D_mem_span (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B), f ∉ P ∧
      ∀ v : B, f • D k B v ∈ Submodule.span B (Set.range fun j => D k B (u j)) := by
  haveI : Algebra.FormallyEtale B K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  haveI : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2 hinj
  have hrk : Module.finrank B Ω[B⁄k] = d := by
    rw [← hd, (KaehlerDifferential.isBaseChange_of_formallyEtale k B K).finrank_eq]
  have hfib : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) = d := by
    rw [← hrk]; exact Ideal.finrank_fiber_eq_finrank P

  let g : B → P.ResidueField ⊗[B] Ω[B⁄k] := fun v => (1 : P.ResidueField) ⊗ₜ D k B v
  have hg : Submodule.span P.ResidueField (Set.range g) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a m =>
      have h1 : (1 : P.ResidueField) ⊗ₜ[B] m ∈ Submodule.span P.ResidueField (Set.range g) := by
        have hm : m ∈ Submodule.span B (Set.range (D k B)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hm using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          exact Submodule.subset_span ⟨v, rfl⟩
        | zero => rw [tmul_zero]; exact zero_mem _
        | add y z _ _ hy hz => rw [tmul_add]; exact add_mem hy hz
        | smul r y _ hy =>
          rw [tmul_smul, ← algebraMap_smul P.ResidueField r]
          exact Submodule.smul_mem _ _ hy
      have : a ⊗ₜ[B] m = a • ((1 : P.ResidueField) ⊗ₜ[B] m) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ _ h1
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent P.ResidueField (Set.range g)
  let bs : Module.Basis s P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hg])
  haveI : Finite s := Module.Finite.finite_basis bs
  letI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = d := by rw [← Module.finrank_eq_card_basis bs, hfib]
  let bF := bs.reindex (Fintype.equivFinOfCardEq hcard)
  have hu : ∀ j, ∃ v, g v = bF j := by
    intro j
    have : bF j ∈ s := by
      rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]; exact Subtype.prop _
    exact hs this
  choose u hu using hu

  let N : Submodule B Ω[B⁄k] := Submodule.span B (Set.range fun j => D k B (u j))
  let φ := (N.mkQ).baseChange P.ResidueField
  have hφ : φ = 0 := by
    refine bF.ext fun j => ?_
    rw [← hu j]
    simp only [φ, g, LinearMap.baseChange_tmul, LinearMap.zero_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨j, rfl⟩)]
    exact TensorProduct.tmul_zero _ _
  have hsub : Subsingleton (P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N)) := by
    have h0 : ∀ x : P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N), x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | add x y hx hy => rw [hx, hy, add_zero]
      | tmul a q =>
        obtain ⟨m, rfl⟩ := N.mkQ_surjective q
        have := LinearMap.congr_fun hφ (a ⊗ₜ m)
        simpa only [φ, LinearMap.baseChange_tmul, LinearMap.zero_apply] using this
    exact ⟨fun x y => by rw [h0 x, h0 y]⟩
  have hnot : (⟨P, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B (Ω[B⁄k] ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfP⟩ := Set.not_subset.1 hnot
  have hfN : ∀ v : B, f • D k B v ∈ N := fun v => by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hf _
  exact ⟨f, u, hfP, hfN⟩

end GlobalTheory.PD

namespace GlobalTheory.PD

theorem exists_local_dbasis (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]), f ∉ P ∧ (∀ j, b j = D k K (u j : K)) ∧
      ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c := by
  obtain ⟨f, u, hfP, hfN⟩ := exists_notMem_smul_D_mem_span k K B d hd P
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hf0 : (f : K) ≠ 0 := by
    intro h
    apply hfP
    have : f = 0 := hinj (by rw [map_zero]; exact h)
    rw [this]; exact P.zero_mem
  have hcoef : ∀ v : B, ∃ c : Fin d → B,
      (f : K) • D k K (v : K) = ∑ j, (c j : K) • D k K (u j : K) := by
    intro v
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 (hfN v)
    refine ⟨c, ?_⟩
    have := congrArg (KaehlerDifferential.map k k B K) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smul, KaehlerDifferential.map_D, Subalgebra.smul_def] at this
    exact this.symm
  let W : Submodule K Ω[K⁄k] := Submodule.span K (Set.range fun j => D k K (u j : K))
  have hB : ∀ v : B, D k K (v : K) ∈ W := by
    intro v
    obtain ⟨c, hc⟩ := hcoef v
    have h1 : (f : K) • D k K (v : K) ∈ W := by
      rw [hc]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := Submodule.smul_mem W (f : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hf0, one_smul] at this
  have hK : ∀ w : K, D k K w ∈ W := by
    intro w
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) w
    have hy0 : algebraMap B K y ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hy)
    have hx : D k K (algebraMap B K x) = (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y)
        + algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) := by
      conv_lhs => rw [show algebraMap B K x = algebraMap B K x / algebraMap B K y * algebraMap B K y by
        rw [div_mul_cancel₀ _ hy0]]
      rw [Derivation.leibniz, add_comm]
    have h2 : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) ∈ W := by
      have e : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) =
          D k K (algebraMap B K x) - (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y) := by
        rw [hx]; abel
      rw [e]
      exact sub_mem (hB x) (Submodule.smul_mem _ _ (hB y))
    have := Submodule.smul_mem W (algebraMap B K y)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hy0, one_smul] at this
  have htop : ⊤ ≤ W := by
    rw [← KaehlerDifferential.span_range_derivation k K]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 hK)
  let b := basisOfTopLeSpanOfCardEqFinrank (fun j => D k K (u j : K)) htop (by rw [Fintype.card_fin, hd])
  have hb : ∀ j, b j = D k K (u j : K) := fun j => by
    simp only [b, coe_basisOfTopLeSpanOfCardEqFinrank]
  refine ⟨f, u, b, hfP, hb, fun v j => ?_⟩
  obtain ⟨c, hc⟩ := hcoef v
  refine ⟨c j, ?_⟩
  have h3 : b.repr ((f : K) • D k K (v : K)) j = (c j : K) := by
    rw [hc]
    simp_rw [← hb]
    rw [b.repr_sum_self (fun j => (c j : K))]
  rw [← h3, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.PD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebraStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ), Module.finrank K Ω[K⁄k] = d → ∀ (P : Ideal B) [P.IsPrime], ∃ (f : B) (u : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]), f ∉ P ∧ (∀ j, b j = D k K (u j : K)) ∧ ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c := by
  first | (exact @GlobalTheory.PD.exists_local_dbasis) | (exact GlobalTheory.PD.exists_local_dbasis) | (intros; apply GlobalTheory.PD.exists_local_dbasis  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairing
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.CupAdj

variable {k : Type} [Field k] {E : Type} [AddCommGroup E] [Module k E] {ι : Type} [LinearOrder ι]

theorem cech_apply_mem {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    (s : Finset ι) : a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥) :=
  (Submodule.mem_pi.1 ha) s (Set.mem_univ _)

theorem cech_apply_eq_zero {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    {s : Finset ι} (h : ¬ (s.Nonempty ∧ (s.card : ℤ) = n + 1)) : a s = 0 := by
  have := cech_apply_mem ha s
  rw [if_neg h] at this
  exact (Submodule.mem_bot k).1 this

theorem cech_apply_mem_of_subset {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t)
    {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n) {s t : Finset ι} (hst : s ⊆ t) : a s ∈ F t := by
  by_cases h : s.Nonempty ∧ (s.card : ℤ) = n + 1
  · have := cech_apply_mem ha s
    rw [if_pos h] at this
    exact hF s t h.1 hst this
  · rw [cech_apply_eq_zero ha h]; exact zero_mem _

end GlobalTheory.PD.CupAdj

namespace GlobalTheory.PD.CupAdj

theorem cupPair_apply {k : Type} [Field k] {d : ℕ} {E : Type} [AddCommGroup E] [Module k E] {E' : Type}
    [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) (a : Finset (Fin (d+1)) → E)
    (b : Finset (Fin (d+1)) → E') :
    cupPair β a b = ∑ j, β (a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
  simp [cupPair]

theorem deltaL_apply {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]
    (a : Finset ι → E) (t : Finset ι) :
    deltaL k ι E a t = ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) := rfl

theorem card_le (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (· ≤ j)).card = j.val + 1 := by
  rw [show Finset.univ.filter (· ≤ j) = Finset.Iic j by ext; simp, Fin.card_Iic]

theorem card_ge (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (j ≤ ·)).card = d + 1 - j.val := by
  rw [show Finset.univ.filter (j ≤ ·) = Finset.Ici j by ext; simp, Fin.card_Ici]

theorem cech_adj (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type)
    [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E)
    (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t)
    (hβ : ∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i),
      β a b = 0) :
    Adj (cech A) (cech B) (cupPair β) d := by
  intro n
  have van : ∀ {m m' : ℤ} {a : Finset (Fin (d+1)) → E} {b : Finset (Fin (d+1)) → E'},
      a ∈ cechC A m → b ∈ cechC B m' → ∀ i s t, s ⊆ Finset.univ.erase i → t ⊆ Finset.univ.erase i →
      β (a s) (b t) = 0 := by
    intro m m' a b ha hb i s t hs ht
    by_cases hne : s.Nonempty
    · exact hβ i (hne.mono hs) _ (cech_apply_mem_of_subset hA ha hs) _ (cech_apply_mem_of_subset hB hb ht)
    · rw [cech_apply_eq_zero ha (fun h => hne h.1), map_zero, LinearMap.zero_apply]
  by_cases hn : 0 ≤ n ∧ n + 1 ≤ d
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.1).symm⟩
    have hmd : m + 1 ≤ d := by exact_mod_cast hn.2
    set j : Fin (d+1) := ⟨m + 1, by omega⟩ with hj
    set j' : Fin (d+1) := ⟨m, by omega⟩ with hj'
    refine ⟨(-1 : ℤˣ) ^ ((Finset.univ.filter (· ≤ j)).filter (· < j)).card, ?_⟩
    intro a ha b hb
    change cupPair β (deltaL k _ E a) b = _ • cupPair β a (deltaL k _ E' b)
    have L1 : cupPair β (deltaL k _ E a) b =
        β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero hb (s := Finset.univ.filter (j0 ≤ ·)), map_zero]
      rintro ⟨-, h⟩
      have := j0.isLt
      rw [card_ge, Nat.cast_sub (by omega)] at h
      push_cast at h
      apply hj0; ext; simp only [hj]; omega
    have L2 : cupPair β a (deltaL k _ E' b) =
        β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j' (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero ha (s := Finset.univ.filter (· ≤ j0)), map_zero, LinearMap.zero_apply]
      rintro ⟨-, h⟩
      rw [card_le] at h
      push_cast at h
      apply hj0; ext; simp only [hj']; omega
    have L3 : β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) =
        GlobalTheory.cubeSign (Finset.univ.filter (· ≤ j)) j •
          β (a ((Finset.univ.filter (· ≤ j)).erase j)) (b (Finset.univ.filter (j ≤ ·))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [deltaL_apply, map_sum, LinearMap.sum_apply]
      refine (Finset.sum_eq_single j (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul, LinearMap.smul_apply]
        have hi' : i < j := lt_of_le_of_ne (by simpa using hi) hij
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
      · rw [map_zsmul, LinearMap.smul_apply]
    have L4 : β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) =
        β (a (Finset.univ.filter (· ≤ j'))) (b ((Finset.univ.filter (j' ≤ ·)).erase j')) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [deltaL_apply, map_sum]
      refine (Finset.sum_eq_single j' (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul]
        have hi' : j' < i := lt_of_le_of_ne (by simpa using hi) (Ne.symm hij)
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
      · have : GlobalTheory.cubeSign (Finset.univ.filter (j' ≤ ·)) j' = 1 := by
          rw [GlobalTheory.cubeSign]
          have : ((Finset.univ.filter (j' ≤ ·)).filter (· < j')) = ∅ := by
            ext x; simp
          rw [this]; simp
        rw [this, one_smul]
    have e1 : (Finset.univ.filter (· ≤ j)).erase j = Finset.univ.filter (· ≤ j') := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    have e2 : Finset.univ.filter (j ≤ ·) = (Finset.univ.filter (j' ≤ ·)).erase j' := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    rw [L1, L2, L3, L4, e1, e2, GlobalTheory.cubeSign, Units.smul_def]
    push_cast
    rfl
  · refine ⟨1, ?_⟩
    intro a ha b hb
    rw [one_smul]
    rcases not_and_or.1 hn with h | h
    · have : a = 0 := by
        funext s
        refine cech_apply_eq_zero ha ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]
    · have : b = 0 := by
        funext s
        refine cech_apply_eq_zero hb ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]

end GlobalTheory.PD.CupAdj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairingStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDifferential_adjoint_cupProductPairing : ∀ (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type) [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E) (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) → (∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i), β a b = 0) → Adj (cech A) (cech B) (cupPair β) d := by
  first | (exact @GlobalTheory.PD.CupAdj.cech_adj) | (exact GlobalTheory.PD.CupAdj.cech_adj) | (intros; apply GlobalTheory.PD.CupAdj.cech_adj  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHense
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHense
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

namespace AICStalk

theorem isIntegrallyClosed_of_aic {A : Type} [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  rintro x ⟨p, hpm, hp⟩
  suffices H : ∀ n : ℕ, ∀ p : A[X], p.Monic → p.natDegree = n → aeval x p = 0 →
      ∃ y, algebraMap A (FractionRing A) y = x by
    exact H _ p hpm rfl (by rwa [aeval_def])
  intro n
  induction n with
  | zero =>
    intro p hpm hdeg hp
    rw [Polynomial.eq_one_of_monic_natDegree_zero hpm hdeg] at hp
    simp at hp
  | succ n ih =>
    intro p hpm hdeg hp
    obtain ⟨a, ha⟩ := h p hpm (by omega)
    have hq : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hq]; exact hpm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]; rfl
    rw [← hq, map_mul] at hp
    simp only [map_sub, aeval_X, aeval_C] at hp
    rcases mul_eq_zero.mp hp with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqm hqd h1

theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : GlobalTheory.EtC.AIC R) :
    GlobalTheory.EtC.AIC S := by
  intro p hpm hdeg
  have hm : (p.map (e.symm : S →+* R)).Monic := hpm.map _
  have hd : (p.map (e.symm : S →+* R)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective e.symm.injective p
  obtain ⟨a, ha⟩ := h _ hm (hd ▸ hdeg)
  refine ⟨e a, ?_⟩
  have hp : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]; ext n; simp
  rw [hp, Polynomial.eval_map, show e a = (e : R →+* S) a from rfl, Polynomial.eval₂_at_apply, ha, map_zero]

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := by
  intro p _ hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hdeg)]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem algebraMap_injective_of_indEt {A O : Type} [CommRing A] [IsDomain A] [CommRing O]
    [Nontrivial O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : Function.Injective (algebraMap A O) := by
  haveI : Module.Flat A O := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hmem : (1 : O) ∈ Submodule.torsion A O := by
    rw [Submodule.mem_torsion_iff]
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, by simp [Algebra.smul_def, ha]⟩
  rw [Module.Flat.torsion_eq_bot] at hmem
  exact one_ne_zero ((Submodule.mem_bot A).mp hmem)

theorem isDomain_of_indEt {A O : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing O] [IsLocalRing O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : IsDomain O := by
  refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
  let I : Ideal (MvPolynomial (Fin 2) A) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
  haveI : Algebra.FinitePresentation A (MvPolynomial (Fin 2) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  let g : (MvPolynomial (Fin 2) A ⧸ I) →ₐ[A] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hxy])
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X _ i)
  have h0 : w 0 * w 1 = 0 := by
    have : Ideal.Quotient.mkₐ A I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ A I (MvPolynomial.X 1) = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [w, ← map_mul, this, map_zero]
  let q : Ideal W := (IsLocalRing.maximalIdeal O).comap v
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hdom, -⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A W q
  have hq : ∀ t ∈ q.primeCompl, IsUnit (v t) := fun t ht => by
    by_contra hc
    exact ht (IsLocalRing.mem_maximalIdeal _ |>.mpr hc)
  have hm : algebraMap W (Localization.AtPrime q) (w 0) * algebraMap W (Localization.AtPrime q) (w 1) = 0 := by
    rw [← map_mul, h0, map_zero]
  rcases mul_eq_zero.mp hm with h1 | h1
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inl (((hq t ht).mul_right_eq_zero).mp this)
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inr (((hq t ht).mul_right_eq_zero).mp this)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isIntegral_tmul_one {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [Algebra A O]
    (h : GlobalTheory.EtC.IndEt A O) (o : O) :
    IsIntegral (FractionRing A) (o ⊗ₜ[A] (1 : FractionRing A)) := by
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h (Polynomial.aeval (R := A) o)
  haveI : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.Etale.baseChange A W _
  haveI : Module.Finite (FractionRing A) (FractionRing A ⊗[A] W) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.IsIntegral.of_finite _ _
  let χ : W →ₐ[A] O ⊗[A] FractionRing A := (Algebra.TensorProduct.includeLeft (S := A)).comp v
  let Χ : FractionRing A ⊗[A] W →ₐ[FractionRing A] O ⊗[A] FractionRing A :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) χ (fun _ _ => Commute.all _ _)
  have hX : Χ (1 ⊗ₜ (u Polynomial.X)) = o ⊗ₜ 1 := by
    have := DFunLike.congr_fun huv Polynomial.X
    simp only [AlgHom.comp_apply, Polynomial.aeval_X] at this
    simp [Χ, χ, this]
  rw [← hX]
  exact (Algebra.IsIntegral.isIntegral _).map Χ

end AICStalk


open AICStalk in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isField_aic_tensor_fractionRing_of_strictlyHenselian :
    ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], GlobalTheory.EtC.AIC A →
      GlobalTheory.EtC.SH O → GlobalTheory.EtC.IndEt A O →
      IsField (O ⊗[A] FractionRing A) ∧ GlobalTheory.EtC.AIC (O ⊗[A] FractionRing A) := by
  intro A O _ _ _ _ hA hO h
  haveI := isIntegrallyClosed_of_aic hA
  obtain ⟨hH, -⟩ := hO
  haveI := hH
  haveI := isDomain_of_indEt h
  haveI : IsAlgClosed (FractionRing A) := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors A))
      (O ⊗[A] FractionRing A) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) (FractionRing A)]
    infer_instance
  have hinj := algebraMap_injective_of_indEt h
  haveI : IsDomain (O ⊗[A] FractionRing A) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors A)) (O ⊗[A] FractionRing A) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))
  have hall : ∀ x : O ⊗[A] FractionRing A, IsIntegral (FractionRing A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul o k =>
      have : o ⊗ₜ[A] k = (o ⊗ₜ[A] (1 : FractionRing A)) * algebraMap (FractionRing A) _ k := by
        rw [show algebraMap (FractionRing A) (O ⊗[A] FractionRing A) k = 1 ⊗ₜ k from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact (isIntegral_tmul_one h o).mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  haveI : Algebra.IsIntegral (FractionRing A) (O ⊗[A] FractionRing A) := ⟨hall⟩
  let e := RingEquiv.ofBijective _
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := FractionRing A) (K := O ⊗[A] FractionRing A))
  exact ⟨MulEquiv.isField (Field.toIsField (FractionRing A)) e.symm.toMulEquiv,
    aic_of_ringEquiv e (aic_of_isAlgClosed _)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHenseStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian : ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], AIC A → SH O → IndEt A O → IsField (O ⊗[A] FractionRing A) ∧ AIC (O ⊗[A] FractionRing A) := by
  first | (exact @GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (exact GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (intros; apply GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open scoped TensorProduct

namespace GlobalTheory.EtC.TensLocBij

theorem locAll {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) :
    Loc U P := GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

theorem locMono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

theorem locAnd {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.1 U P Q hP hQ

theorem locTrans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem locFin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

section Alg

variable {S : Type*} [CommRing S] {A B D : Type*} [AddCommGroup A] [Module S A]
  [AddCommGroup B] [Module S B] [AddCommGroup D] [Module S D]

theorem exists_fg_lTensor (x : A ⊗[S] B) :
    ∃ (J : Submodule S B) (_ : J.FG) (y : A ⊗[S] J), x = LinearMap.lTensor A J.subtype y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, 0, by simp⟩
  | tmul a b => exact ⟨S ∙ b, Submodule.fg_span_singleton b,
      a ⊗ₜ[S] ⟨b, Submodule.mem_span_singleton_self _⟩, rfl⟩
  | add x₁ x₂ ih₁ ih₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ih₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ih₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂, LinearMap.lTensor A (Submodule.inclusion le_sup_left) y₁ +
      LinearMap.lTensor A (Submodule.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add (f := _), ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl

theorem rTensor_comm_eq {Y : Type*} [AddCommGroup Y] [Module S Y] (g : B →ₗ[S] Y) (x : A ⊗[S] B) :
    LinearMap.rTensor A g (TensorProduct.comm S A B x) =
      TensorProduct.comm S A Y (LinearMap.lTensor A g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fg_lTensor_eq_zero {J : Submodule S D} (hJ : J.FG) {t : A ⊗[S] J}
    (h : LinearMap.lTensor A J.subtype t = 0) :
    ∃ (K : Submodule S D) (hJK : J ≤ K), K.FG ∧
      LinearMap.lTensor A (Submodule.inclusion hJK) t = 0 := by
  have h' : LinearMap.rTensor A J.subtype (TensorProduct.comm S A J t) = 0 := by
    rw [rTensor_comm_eq, h, map_zero]
  obtain ⟨K, hJK, hK, h0⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hJ h'
  refine ⟨K, hJK, hK, ?_⟩
  rw [rTensor_comm_eq] at h0
  exact (LinearEquiv.map_eq_zero_iff _).mp h0

end Alg

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem surj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (U : Scheme.{0}) (y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U))) :
    Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x =
      TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y := by
  induction y using TensorProduct.induction_on with
  | zero => exact locAll fun V g => ⟨0, by simp⟩
  | tmul c q =>
    exact locMono (hs U q) fun V g ⟨x, hx⟩ => ⟨(C.map g.op).hom c ⊗ₜ x, by simp [hx]⟩
  | add a b ha hb =>
    exact locMono (locAnd ha hb) fun V g ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ => ⟨x + x', by simp [map_add (f := _), hx, hx']⟩

theorem kerPart
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (V : Scheme.{0}) (K : Submodule (ULift.{1} R) (P.obj (op V)))
    (hK : ∀ k ∈ K, (φ.app (op V)).hom k = 0) (z : C.obj (op V) ⊗[ULift.{1} R] K) :
    Loc V fun _ h => TensorProduct.map (C.map h.op).hom (P.map h.op).hom
      (LinearMap.lTensor _ K.subtype z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact locAll fun _ _ => by simp
  | tmul c k => exact locMono (hi V k.1 (hK k.1 k.2)) fun W h hk => by simp [hk]
  | add a b ha hb => exact locMono (locAnd ha hb) fun W h ⟨h1, h2⟩ => by simp [map_add (f := _), h1, h2]

theorem map_restr_comp {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) :
    TensorProduct.map (C.map (k ≫ g).op).hom (P.map (k ≫ g).op).hom =
      TensorProduct.map (C.map k.op).hom (P.map k.op).hom ∘ₗ
        TensorProduct.map (C.map g.op).hom (P.map g.op).hom := by
  rw [op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
    TensorProduct.map_comp]

theorem nat_apply {U V : Scheme.{0}} (g : V ⟶ U) (p : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom p) = (Q.map g.op).hom ((φ.app (op U)).hom p) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h p) (φ.naturality g.op)
  simpa using this

end GlobalTheory.EtC.TensLocBij

namespace GlobalTheory.EtC.TensLocBij

variable {R : Type} [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q)

theorem inj
    (hs : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (hi : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)))
    (hx : LinearMap.lTensor _ (φ.app (op U)).hom x = 0) :
    Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  obtain ⟨B₀, hB₀, x₀, rfl⟩ := exists_fg_lTensor x
  have hcomp : (B₀.map (φ.app (op U)).hom).subtype ∘ₗ (φ.app (op U)).hom.submoduleMap B₀ =
      (φ.app (op U)).hom ∘ₗ B₀.subtype := rfl
  have ht : LinearMap.lTensor _ (B₀.map (φ.app (op U)).hom).subtype
      (LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) x₀) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨K, hJK, ⟨s, hs'⟩, hK0⟩ := fg_lTensor_eq_zero (hB₀.map _) ht
  have hloc := locFin (ι := Fin s.card)
    (fun i V g => ∃ p, (φ.app (op V)).hom p = (Q.map g.op).hom (s.equivFin.symm i).1)
    (fun i => hs U (s.equivFin.symm i).1)
  apply locTrans
  refine locMono hloc fun V g hV => ?_
  have hle : K ≤ (LinearMap.range (φ.app (op V)).hom).comap (Q.map g.op).hom := by
    rw [← hs', Submodule.span_le]
    intro q hq
    obtain ⟨p, hp⟩ := hV (s.equivFin ⟨q, hq⟩)
    rw [Equiv.symm_apply_apply] at hp
    exact ⟨p, hp⟩
  let ρ := ((Q.map g.op).hom ∘ₗ K.subtype).codRestrict (LinearMap.range (φ.app (op V)).hom)
    (fun k => hle k.2)
  have key : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict ∘ₗ
      TensorProduct.map (C.map g.op).hom (P.map g.op).hom ∘ₗ LinearMap.lTensor _ B₀.subtype =
      TensorProduct.map (C.map g.op).hom ρ ∘ₗ LinearMap.lTensor _ (Submodule.inclusion hJK) ∘ₗ
        LinearMap.lTensor _ ((φ.app (op U)).hom.submoduleMap B₀) := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
    congr 1
    apply Subtype.ext
    simp [ρ, nat_apply]
  have hy : LinearMap.lTensor _ (φ.app (op V)).hom.rangeRestrict
      (TensorProduct.map (C.map g.op).hom (P.map g.op).hom (LinearMap.lTensor _ B₀.subtype x₀)) = 0 := by
    have := congrArg (fun L => L x₀) key
    simp only [LinearMap.comp_apply] at this
    rw [this, hK0, map_zero]
  have hex := lTensor_exact (C.obj (op V))
    (LinearMap.exact_subtype_ker_map (φ.app (op V)).hom.rangeRestrict)
    (LinearMap.surjective_rangeRestrict _)
  obtain ⟨z, hz⟩ := (hex _).mp hy
  have hK : ∀ k ∈ LinearMap.ker (φ.app (op V)).hom.rangeRestrict, (φ.app (op V)).hom k = 0 := by
    intro k hk
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hk)
    simpa using this
  refine locMono (kerPart C P Q φ hi V _ hK z) fun W k hk => ?_
  rw [map_restr_comp, LinearMap.comp_apply, ← hz]
  exact hk

theorem main : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  fun _ _ C P Q φ hs hi U => ⟨surj C P Q φ hs U, inj C P Q φ hs hi U⟩

end GlobalTheory.EtC.TensLocBij

theorem GlobalTheory.EtC.tensor_loc_bij : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 :=
  GlobalTheory.EtC.TensLocBij.main
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective : ∀ (R : Type) [CommRing R] (C P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ U : Scheme.{0}, (∀ y : TensorProduct (ULift.{1} R) (C.obj (op U)) (Q.obj (op U)), Loc U fun V g => ∃ x, LinearMap.lTensor _ (φ.app (op V)).hom x = TensorProduct.map (C.map g.op).hom (Q.map g.op).hom y) ∧ ∀ x : TensorProduct (ULift.{1} R) (C.obj (op U)) (P.obj (op U)), LinearMap.lTensor _ (φ.app (op U)).hom x = 0 → Loc U fun _ g => TensorProduct.map (C.map g.op).hom (P.map g.op).hom x = 0 := by
  first | (exact @GlobalTheory.EtC.tensor_loc_bij) | (exact GlobalTheory.EtC.tensor_loc_bij) | (intros; apply GlobalTheory.EtC.tensor_loc_bij  <;> assumption)
end
end
