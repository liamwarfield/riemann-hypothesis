module

public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntegralNormalization
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf

def OpenNbhdIC : Prop := ∀ {Z : Scheme.{0}} (U : Z.Opens), AICSch Z → (U : Set Z).Nonempty → AICSch U.toScheme

def FFAlg : Prop := ∀ {Z : Scheme.{0}} [IsIntegral Z], AICSch Z → IsAlgClosed Z.functionField

def NormAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g], AICSch g.normalization

theorem spec_field_qc (K : Type) [Field K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W) : QuasiCompact g := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U _
  exact (Set.toFinite _).isCompact

theorem Norm_of (h0 : OpenNbhdIC) (h1 : FFAlg) (h2 : NormAIC) : LateralTheory.E.ChowCut.Norm := by
  intro Z W f _ hZ ⟨U, s, hU, hs⟩
  have : IsIntegral Z := hZ.1
  have hUa := h0 U hZ hU
  have := hUa.1
  have := h1 hUa
  let g0 : Spec (CommRingCat.of U.toScheme.functionField) ⟶ U.toScheme := U.toScheme.fromSpecStalk _
  let g := g0 ≫ s
  have := spec_field_qc _ g
  refine ⟨g.normalization, g.fromNormalization, inferInstance, h2 _ g, ?_⟩
  have hg0 : IsDominant g0 := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.range_fromSpecStalk]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec U.toScheme).def ▸ closure_mono (Set.singleton_subset_iff.mpr (specializes_refl _)))
  have hU' : IsDominant U.ι := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.Opens.range_ι]
    exact (U.isOpen.dense hU).closure_eq
  have e : g.toNormalization ≫ g.fromNormalization ≫ f = g0 ≫ U.ι := by
    rw [reassoc_of% g.toNormalization_fromNormalization, Category.assoc, hs]
  have : IsDominant (g.toNormalization ≫ g.fromNormalization ≫ f) := by rw [e]; infer_instance
  exact IsDominant.of_comp g.toNormalization _

end LateralTheory.E.NormPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.OpenPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf.OpenPf

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : GlobalTheory.EtC.AIC R) : GlobalTheory.EtC.AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hq : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    rw [Polynomial.map_map]; ext n; simp
  rw [← hq, Polynomial.eval_map]
  have h2 := Polynomial.eval₂_at_apply (p := p.map e.symm.toRingHom) e.toRingHom a
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h2 ha ⊢
  rw [h2, ha, map_zero]

theorem openNbhdIC : OpenNbhdIC := by
  intro Z U hZ hU
  have : IsIntegral Z := hZ.1
  have : Nonempty U := hU.to_subtype
  refine ⟨inferInstance, fun V hV hVne => ?_⟩
  have hV' : IsAffineOpen (U.ι ''ᵁ V) := hV.image_of_isOpenImmersion U.ι
  have hne : ((U.ι ''ᵁ V : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hx⟩ := hVne
    exact ⟨U.ι x, x, hx, rfl⟩
  exact aic_of_equiv (U.ι.appIso V).commRingCatIsoToRingEquiv (hZ.2 _ hV' hne)

end LateralTheory.E.NormPf.OpenPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.AlgClosedOfAic
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.NormPf.FFPf

theorem algClosed_of_aic (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (h : GlobalTheory.EtC.AIC R) : IsAlgClosed K := by
  classical
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hd : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    ((Finset.range (p.natDegree + 1)).image p.coeff)
  set d : K := algebraMap R K b with hdd
  have hd0 : d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hint : ∀ i, ∃ r : R, algebraMap R K r = p.coeff i * d := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · obtain ⟨r, hr⟩ := hb (p.coeff i) (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
      refine ⟨r, ?_⟩
      rw [hr, Algebra.smul_def, mul_comm]
    · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩
  have hl : scaleRoots p d ∈ lifts (algebraMap R K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    by_cases hi : i < p.natDegree
    · obtain ⟨r, hr⟩ := hint i
      refine ⟨r * b ^ (p.natDegree - i - 1), ?_⟩
      rw [map_mul, map_pow, hr, ← hdd, mul_assoc, ← pow_succ']
      congr 2
      omega
    · by_cases he : i = p.natDegree
      · subst he; exact ⟨1, by rw [hp.coeff_natDegree]; simp⟩
      · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_degree_eq_and_monic hl ((monic_scaleRoots_iff d).mpr hp)
  have hqn : 0 < q.natDegree := by
    rw [natDegree_eq_of_degree_eq hqd, natDegree_scaleRoots]; exact hd
  obtain ⟨r, hr⟩ := h q hqm hqn
  refine ⟨algebraMap R K r / d, ?_⟩
  have e1 := scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap R K r / d) d
  simp only [RingHom.id_apply, eval₂_id] at e1
  rw [mul_div_cancel₀ _ hd0, ← hq, Polynomial.eval_map, eval₂_at_apply, hr, map_zero] at e1
  exact (mul_eq_zero.mp e1.symm).resolve_left (pow_ne_zero _ hd0)

theorem ffAlg : FFAlg := by
  intro Z _ hZ
  obtain ⟨x⟩ := (inferInstance : Nonempty Z)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen Z V hV
  exact algClosed_of_aic Γ(Z, V) Z.functionField (hZ.2 V hV ⟨x, hxV⟩)

end LateralTheory.E.NormPf.FFPf

end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf.AICPf

def AffAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g] (U : W.Opens), IsAffineOpen U →
  GlobalTheory.EtC.AIC Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U)

def LocAIC : Prop := ∀ (X : Scheme.{0}) [IsIntegral X],
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ GlobalTheory.EtC.AIC Γ(X, U)) → AICSch X

theorem normAIC_of (ha : AffAIC) (hl : LocAIC) : NormAIC := by
  intro K _ _ W g _ _
  refine ⟨inferInstance, ?_⟩
  have := hl g.normalization ?_
  · exact this.2
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.fromNormalization x)) isOpen_univ
  exact ⟨g.fromNormalization ⁻¹ᵁ U, hxU, hU.preimage _, ha K g U hU⟩

theorem norm_full (ha : AffAIC) (hl : LocAIC) : LateralTheory.E.ChowCut.Norm :=
  Norm_of OpenPf.openNbhdIC FFPf.ffAlg (normAIC_of ha hl)

end LateralTheory.E.NormPf.AICPf

end
