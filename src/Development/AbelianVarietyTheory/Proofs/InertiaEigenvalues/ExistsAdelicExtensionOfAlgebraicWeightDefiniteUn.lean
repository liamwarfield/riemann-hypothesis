module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise

namespace GlobalTheory.WeightRealExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem dense_rat_fin : Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
  intro g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU E n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA E n → UA E n) := continuous_mul_const k
  refine closure_mono ?_
    (image_closure_subset_closure_image hc ⟨x, GlobalTheory.DefiniteDense.mem_closure_rat_fin x hx, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
  exact ⟨γ, hγ, k' * k, (finU (E := E) (n := n)).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (γ : UA E n) (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) : γ₀ ∈ GQ0 E n := by
  have h0 : Formalism.UG.cT (conjAd E) (γ.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * γ.1 = 1 := γ.2
  rw [mul_one, h] at h0
  have e : Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
      (conjT (IsCMField.complexConj E : E →+* E) (γ₀ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
    ext i j
    simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
  change Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) *
      (γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1 at h0
  rw [e, ← Matrix.map_mul, ← Matrix.map_one (algebraMap E (Ad E)) (map_zero _) (map_one _)] at h0
  have h1 := Matrix.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 E) E) h0
  exact mul_eq_one_comm.1 h1

def ratPt : GQ0 E n →* GQ E n where
  toFun γ := ⟨⟨GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) γ.1, by
      have h0 : (γ.1 : Matrix (Fin n) (Fin n) E) * conjT (IsCMField.complexConj E : E →+* E) γ.1 = 1 := γ.2
      have e : conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) =
          (conjT (IsCMField.complexConj E : E →+* E) (γ.1 : Matrix (Fin n) (Fin n) E)).map
            (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) := by
        ext i j
        simp [conjT, conjAL]
      change (γ.1 : Matrix (Fin n) (Fin n) E).map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) *
        conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) = 1
      rw [e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]⟩,
    Subgroup.mem_subgroupOf.2 ⟨γ.1, γ.2, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul _ _ _))

def polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (g : UA E n) : Matrix ι ι ℂ :=
  fun i j => MvPolynomial.eval (fun p => coord p.1 ((cInf g : Matrix (Fin n) (Fin n) (Cinf E)) p.2.1 p.2.2)) (P i j)

theorem polyMat_congr {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) {g h : UA E n}
    (e : cInf g = cInf h) : polyMat P g = polyMat P h := by
  unfold polyMat
  rw [e]

theorem polyMat_rat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (γ : UA E n)
    (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) :
    polyMat P γ = fun i j =>
      MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) E) p.2.1 p.2.2)) (P i j) := by
  funext i j
  unfold polyMat
  congr 2
  funext p
  rw [← coord_algebraMap p.1]
  congr 1
  change pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) = _
  rw [h]
  rfl


omit [NumberField E] [IsCMField E] in
theorem continuous_coord' (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) :
    Continuous (polyMat P) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (MvPolynomial.continuous_eval (P i j)).comp (continuous_pi fun p => ?_)
  refine (continuous_coord' p.1).comp (continuous_pInf'.comp
    (f := fun g : UA E n => (g.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) ?_)
  exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _

theorem exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational {γ : UA E n} (hγ : γ ∈ ratU E n) : ∃ γ₀ : GQ0 E n, γ.1 = ratGL E n γ₀.1 := by
  obtain ⟨γ₀, hγ₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  exact ⟨⟨γ₀, mem_rationalGL_of_unitaryGroupGram_unitGram γ γ₀ hγ₀.symm⟩, hγ₀.symm⟩

theorem mul_of_dense {G M : Type} [Mul G] [TopologicalSpace G] [ContinuousMul G] [Mul M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {D : Set G} (hD : Dense D) (f : G → M) (hf : Continuous f)
    (h : ∀ x ∈ D, ∀ y ∈ D, f (x * y) = f x * f y) (x y : G) : f (x * y) = f x * f y := by
  have hcl : IsClosed {z : G × G | f (z.1 * z.2) = f z.1 * f z.2} :=
    isClosed_eq (hf.comp (continuous_fst.mul continuous_snd))
      ((hf.comp continuous_fst).mul (hf.comp continuous_snd))
  exact hcl.closure_subset_iff.2 (fun z (hz : z ∈ D ×ˢ D) => h z.1 hz.1 z.2 hz.2) ((hD.prod hD) (x, y))

theorem mul_of_rat {M : Type} [Mul M] [TopologicalSpace M] [ContinuousMul M] [T2Space M] (f : UA E n → M)
    (hf : Continuous f) (hi : ∀ g h, cInf g = cInf h → f g = f h)
    (h : ∀ x ∈ ratU E n, ∀ y ∈ ratU E n, f (x * y) = f x * f y) : ∀ x y, f (x * y) = f x * f y := by
  refine mul_of_dense dense_rat_fin f hf fun x hx y hy => ?_
  obtain ⟨γ, hγ, k, hk, hx⟩ := Set.mem_mul.1 hx
  obtain ⟨δ, hδ, l, hl, hy⟩ := Set.mem_mul.1 hy
  have hk' : cInf k = 1 := hk
  have hl' : cInf l = 1 := hl
  have e1 : cInf x = cInf γ := by rw [← hx, map_mul, hk', mul_one]
  have e2 : cInf y = cInf δ := by rw [← hy, map_mul, hl', mul_one]
  rw [hi x γ e1, hi y δ e2, hi (x * y) (γ * δ) (by rw [map_mul, map_mul, e1, e2]), h γ hγ δ hδ]

theorem exists_extension : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ R : UA L n →* Module.End ℂ a.W, (∀ k ∈ finU (E := L) (n := n), R k = 1) ∧ (∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = a.ρ γQ) ∧ ∀ (v : a.W) (μ : Module.Dual ℂ a.W), Continuous fun g : UA L n => μ (R g v) := by
  intro L _ _ _ n a
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  have hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ γQ) := fun γ γQ γ₀ h1 h2 =>
    (polyMat_rat P γ γ₀ h1).trans (hP γQ γ₀ h2).symm
  have hrat' : ∀ (γ : UA L n) (γ₀ : GQ0 L n), γ.1 = ratGL L n γ₀.1 →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ (ratPt (E := L) (n := n) γ₀)) := fun γ γ₀ h => hrat γ _ γ₀.1 h rfl
  have hone : polyMat P 1 = 1 := by
    rw [hrat' 1 1 (map_one (ratGL L n)).symm, map_one, map_one, LinearMap.toMatrix_one]
  have hmul : ∀ g h : UA L n, polyMat P (g * h) = polyMat P g * polyMat P h := by
    refine mul_of_rat (polyMat P) (continuous_polyMat P) (fun _ _ => polyMat_congr P) fun γ hγ δ hδ => ?_
    obtain ⟨γ₀, hγ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ
    obtain ⟨δ₀, hδ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hδ
    have e : (γ * δ).1 = ratGL L n (γ₀ * δ₀).1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, hγ₀, hδ₀]
    rw [hrat' γ γ₀ hγ₀, hrat' δ δ₀ hδ₀, hrat' (γ * δ) (γ₀ * δ₀) e, map_mul, map_mul, LinearMap.toMatrix_mul]
  refine ⟨⟨⟨fun g => Matrix.toLin b b (polyMat P g), ?_⟩, fun g h => ?_⟩, fun k hk => ?_, fun γ γQ γ₀ h1 h2 => ?_,
    fun v μ => ?_⟩
  · rw [hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P (g * h)) = _
    rw [hmul, Matrix.toLin_mul b b b]
    rfl
  · change Matrix.toLin b b (polyMat P k) = 1
    rw [polyMat_congr P (g := k) (h := 1) ((show cInf k = 1 from hk).trans (map_one _).symm), hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P γ) = _
    rw [hrat γ γQ γ₀ h1 h2, Matrix.toLin_toMatrix]
  · change Continuous fun g : UA L n => μ (Matrix.toLin b b (polyMat P g) v)
    have hc := continuous_polyMat P
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.toLin_apply, map_sum, map_smul, smul_eq_mul]
    refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const
    exact (continuous_apply j).comp (hc.matrix_mulVec continuous_const)

end GlobalTheory.WeightRealExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUnStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_extension_of_algebraicWeight_definiteUnitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ R : UA L n →* Module.End ℂ a.W, (∀ k ∈ finU (E := L) (n := n), R k = 1) ∧ (∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = a.ρ γQ) ∧ ∀ (v : a.W) (μ : Module.Dual ℂ a.W), Continuous fun g : UA L n => μ (R g v) := by
  first | exact @GlobalTheory.WeightRealExt.exists_extension | exact GlobalTheory.WeightRealExt.exists_extension | (intros; apply GlobalTheory.WeightRealExt.exists_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocationsDistinguishedByGenerics
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocationsDistinguishedByGenerics
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty

set_option synthInstance.maxHeartbeats 400000 in
theorem sameLoc_iff_heckeCong : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  intro D cf jE A M C tup big L hB j w i i' hi hi' x x'
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB

  have hiC : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (z : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a z = Sp.iotaC j w (Sp.phO j w a ha z) := by
    intro a ha z
    rw [← Sp.iotaC_coh j w a ha z]
    show ((L.Y.naut.iotaQC a).toRingHom.comp (L.Y.naut.iotaQ a)) (algebraMap _ _ z) = _
    rw [RingHom.comp_apply, Au.iotaQ, Au.iotaQC]
    rfl

  have key : ∀ (a : L.X.nd.Loc) (ha : a ∈ L.X.nd.locs j w) (y : L.X.nd.O a),
      iotaO L.X.nd L.Y.naut a y ∈ (A.pl.plB w).nonunits ↔ y ∈ IsLocalRing.maximalIdeal (L.X.nd.O a) := by
    intro a ha y
    have hw : L.X.nd.w a = w := ((L.X.nd.locs_mem j w a).1 ha).2
    subst hw
    obtain ⟨h, e⟩ := Au.kFbar a y
    rw [ValuationSubring.mem_nonunits_iff]
    have e1 : (A.pl.plB (L.X.nd.w a)).valuation (iotaO L.X.nd L.Y.naut a y) =
        (A.pl.plB (L.X.nd.w a)).valuation ((⟨_, h⟩ : A.pl.plB (L.X.nd.w a)) : ℂ) := rfl
    rw [e1, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff,
      ← IsLocalRing.residue_eq_zero_iff, ← map_eq_zero (L.Y.naut.kFbar a), ← e]
    simp only [EmbeddingLike.map_eq_zero_iff]

  have gen : ∀ v k, GenAt D (D.what₂.places.resChar w) (C.Q w) v k ↔
      GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
    intro v k; rw [Sp.Qc_eq]
  constructor
  · rintro rfl v k hvk
    have hvk' := (gen v k).1 hvk
    have e1 := Sp.ptX_hT j w i hi x v k hvk'
    have e2 := Sp.ptX_hT j w i hi' x' v k hvk'
    have hc : Formalism.L2.NCov.cls (Sp.ptX j w i hi x).1 = Formalism.L2.NCov.cls (Sp.ptX j w i hi' x').1 :=
      (Sp.ptX j w i hi x).2.1.trans (Sp.ptX j w i hi' x').2.1.symm
    generalize (Sp.ptX j w i hi x).1 = ψ at e1 hc
    generalize (Sp.ptX j w i hi' x').1 = ψ' at e2 hc
    generalize (⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk', rfl⟩⟩ : heckeAlg Sp.B j w) = t at e1 e2
    have hmem : t - algebraMap _ _ (ψ t) ∈ Formalism.L2.NCov.cls ψ' := by
      rw [← hc, Formalism.L2.NCov.cls, RingHom.mem_ker]
      change IsLocalRing.residue _ (ψ (t - algebraMap _ _ (ψ t))) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
    rw [Formalism.L2.NCov.cls, RingHom.mem_ker] at hmem
    change IsLocalRing.residue _ (ψ' (t - algebraMap _ _ (ψ t))) = 0 at hmem
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_sub, sub_eq_zero, ← e1, ← e2] at hmem
    have r := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi).symm hmem
    simp only [RingEquiv.symm_apply_apply] at r
    rw [← map_sub]
    refine (key i hi _).2 ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, r, sub_self]
  · intro H
    apply Sp.mx_inj j w hi hi'
    rw [← (Sp.ptX j w i hi x).2.1, ← (Sp.ptX j w i' hi' x').2.1]
    refine GlobalTheory.PtLocalEig.cls_eq_of_residue _ _ _ ?_
    rintro _ ⟨v, k, hvk, rfl⟩
    rw [← Sp.ptX_hT j w i hi x v k hvk, ← Sp.ptX_hT j w i' hi' x' v k hvk]
    have h1 := H v k ((gen v k).2 hvk)
    have hz : iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') =
        iotaO L.X.nd L.Y.naut i ((Sp.phO j w i hi).symm
          (Sp.phO j w i' hi' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x'))) := by
      rw [hiC i hi, hiC i' hi', RingEquiv.apply_symm_apply]
    rw [hz, ← map_sub, key i hi, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at h1
    have h2 := GlobalTheory.PtLocalEig.residue_map_equiv (Sp.phO j w i hi) h1
    rwa [RingEquiv.apply_symm_apply] at h2

end GlobalTheory.CoefDuty

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocationsDistinguishedByGenericsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locations_distinguished_by_generics : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  first | exact @GlobalTheory.CoefDuty.sameLoc_iff_heckeCong | exact GlobalTheory.CoefDuty.sameLoc_iff_heckeCong | (intros; apply GlobalTheory.CoefDuty.sameLoc_iff_heckeCong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOutIffGenAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.PtExt

variable {D : D7}


open Classical in
def sys (L : LocAll (lay0 D)) (i : L.X.nd.Loc) (x : L.X.nd.X i) : PlE D.host → ℕ → ℂ := fun v k =>
  if SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV then
    iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x)
  else 0

theorem splitOut_iff_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (C.Q w) v k := by
  obtain ⟨Sp, -, -⟩ := hB
  have hw : L.X.nd.w i = w := ((L.X.nd.locs_mem j w i).1 hi).2
  have hl : L.X.nd.l i = D.what₂.places.resChar w := by rw [← hw]; exact (L.X.nd.w_l i).symm
  have hQ : L.X.nd.Q i = C.Q w := (Sp.Q_eq j w i hi).trans (Sp.Qc_eq j w)
  have hS : v ∈ L.X.nd.S i ↔ v ∈ placesS D (L.X.nd.l i) := L.X.nd.S_def i v
  unfold SplitOut GenAt
  rw [hS, ← hl, ← hQ]
  tauto

theorem sys_of_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) :
    sys L i x v k = iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) := by
  unfold sys
  rw [if_pos ((splitOut_iff_genAt hB hi v k).2 h)]

theorem sys_of_not_genAt {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) {v : PlE D.host} {k : ℕ}
    (h : ¬ GenAt D (D.what₂.places.resChar w) (C.Q w) v k) : sys L i x v k = 0 := by
  unfold sys
  rw [if_neg (fun h' => h ((splitOut_iff_genAt hB hi v k).1 h'))]

theorem sys_mem {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hB : Built A M C tup big L) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {i : L.X.nd.Loc}
    (hi : i ∈ L.X.nd.locs j w) (x : L.X.nd.X i) :
    sys L i x ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w) := by
  refine ⟨fun v k h => sys_of_not_genAt hB hi x h, ?_⟩
  have hB' := hB
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB'
  obtain ⟨hj, hw⟩ := (L.X.nd.locs_mem j w i).1 hi
  subst hj hw
  obtain ⟨P, hP⟩ := L.Y.naut.pt_surj i x
  have key : ∃ y : D.what₂.Mt (L.X.nd.mu i) (L.X.nd.j i), y ≠ 0 ∧
      ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        GenAt D (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) v k → IsConjPl D.host v s.w →
        IsUnif D.host.E s.v ϖ →
        NG.tN (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).J s ϖ k ((M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y) =
          sys L i x v k • (M (L.X.nd.mu i) (L.X.nd.j i) h1 h2).real y := by
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (L.Y.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hso, k1, k2⟩ := (splitOut_iff_genAt hB hi v k).2 hg
    rw [sys_of_genAt hB hi x hg]
    exact (Au.ptV i P x).1 hP v k s ϖ hso hc hu k1 k2 y hy
  rw [L.X.nd.mu_w i] at key
  exact key

theorem iotaO_injective (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : Function.Injective (iotaO L.X.nd L.Y.naut i) := by
  intro a b h
  unfold iotaO at h
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  exact IsFractionRing.injective (L.X.nd.O i) (FractionRing (L.X.nd.O i))
    ((L.Y.naut.iotaQ i).injective ((L.Y.naut.iotaQC i).injective h))

theorem sys_inj (L : LocAll (lay0 D)) (i : L.X.nd.Loc) {x x' : L.X.nd.X i} (h : sys L i x = sys L i x') : x = x' := by
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := L.X.nd.T_sep i x x' hne
  apply hfx
  let E : Subalgebra (L.X.nd.O i) (L.X.nd.X i → L.X.nd.O i) :=
    AlgHom.equalizer (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x)
      (Pi.evalAlgHom (L.X.nd.O i) (fun _ => L.X.nd.O i) x')
  have hle : L.X.nd.T i ≤ E := by
    rw [← L.X.nd.T_gen i, Algebra.adjoin_le_iff]
    rintro g ⟨v, k, hs, hl, hS, hQ, k1, k2, rfl⟩
    have hv : SplitOut L.X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV := ⟨⟨hs, hl, hS, hQ⟩, k1, k2⟩
    have := congrFun (congrFun h v) k
    unfold sys at this
    rw [if_pos hv, if_pos hv] at this
    exact iotaO_injective L i this
  exact hle hf

end GlobalTheory.PtExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtTensorTwistApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IndChain.SuppStep

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL
open scoped TensorProduct

variable {g : ℕ} [Fact g.Prime]

theorem isUnram_of_supp {ν : ℚ_[g]ˣ →* ℂˣ} (h : Supp.IsUnram ν) : GlobalTheory.SplitWeil.IsUnram ν := by
  intro x hx
  have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g (x : ℚ_[g]) 1
  have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 (x : ℚ_[g])
  rw [hx, map_one] at a1 a2
  have h1 : ‖(x : ℚ_[g])‖ = 1 := by
    simp only [lt_self_iff_false, norm_one, false_iff, not_lt] at a1 a2
    exact le_antisymm a2 a1
  have := h (PadicInt.mkUnits h1)
  convert this using 2
  exact Units.ext rfl

theorem extTensor_twist_apply {a b : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (χ₁ : GL (Fin a) ℚ_[g] →* ℂˣ) (χ₂ : GL (Fin b) ℚ_[g] →* ℂˣ) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g])
    (w : W ⊗[ℂ] W') :
    extTensor (GlobalTheory.SmGL.twist σ χ₁) (GlobalTheory.SmGL.twist ρ χ₂) (x, y) w = ((χ₁ x * χ₂ y : ℂˣ) : ℂ) • TensorProduct.map (σ x) (ρ y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), hu, hv, map_add (f := _), smul_add]
  | tmul u v =>
    rw [extTensor_tmul, TensorProduct.map_tmul, twist_apply, twist_apply, TensorProduct.smul_tmul_smul,
      Units.val_mul]

theorem scal_eq (ν₁ ν₂ A B : ℚ_[g]ˣ →* ℂˣ) (u v : ℚ_[g]ˣ) :
    (A u * B v) * ((ν₁ * A⁻¹) u * (ν₂ * B⁻¹) v) = ν₁ u * ν₂ v := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem law {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W')
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (q : parab ℚ_[g] (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    Λ (π q w) = (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) (leviProj ℚ_[g] _ q) : ℂ) •
      extTensor (GlobalTheory.SmGL.twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
        (GlobalTheory.SmGL.twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))
        ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)) (Λ w) := by
  set X := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).1 with hX
  set Y := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).2 with hY
  have hL : leviProj ℚ_[g] _ q = leviTwo ℚ_[g] _ _ (X, Y) := (MulEquiv.apply_symm_apply _ _).symm
  have hpar := (mem_parab_two ℚ_[g]).1 q.2
  have h0 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) →
      ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0 := by
    intro i j hj hi
    have e1 : stdSum (rfl : a + b = a + b) (.inr ⟨i - a, by omega⟩) = i := Fin.ext (by rw [stdSum_inr]; simp; omega)
    have e2 : stdSum (rfl : a + b = a + b) (.inl ⟨j, hj⟩) = j := Fin.ext (by rw [stdSum_inl])
    have := hpar ⟨i - a, by omega⟩ ⟨j, hj⟩
    rwa [e1, e2] at this
  have hx : ∀ i j : Fin a, (X : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dite_eq_left ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inl i)) (stdSum (rfl : a + b = a + b) (.inl j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inl _ _)
  have hy : ∀ i j : Fin b, (Y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j) := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dite_eq_left ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inr i)) (stdSum (rfl : a + b = a + b) (.inr j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inr _ _)
  rw [hΛ q X Y h0 hx hy w, hL, MulEquiv.symm_apply_apply, deltaHalf_two, extTensor_twist_apply, smul_smul,
    ← Units.val_mul, detChar_apply, detChar_apply]
  simp only [Fintype.card_fin]
  rw [scal_eq]

theorem supp_of_mapsToProd : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (g : ℕ) [Fact g.Prime] (n a b : ℕ) (V W W' : Type)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → Supp.MapsToProd π σ ρ →
    ∀ (ys yr : Multiset (GlobalTheory.LocGL.IrrGL (k := ℚ_[g]))), GlobalTheory.LocGL.HasSupport σ ys → GlobalTheory.LocGL.HasSupport ρ yr →
    ∃ (μ₁ μ₂ : ℚ_[g]ˣ →* ℂˣ) (h₁ : GlobalTheory.SplitWeil.IsUnram μ₁) (h₂ : GlobalTheory.SplitWeil.IsUnram μ₂),
      GlobalTheory.LocGL.HasSupport π (ys.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)) +
        yr.map (fun x => x.tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂))) := by
  intro hZ g _ n a b V W W' _ _ _ _ _ _ π σ ρ hs hπ hM ys yr hys hyr
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ ℚ_[g]
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, hΛ0, hΛ⟩ := hM
  subst hn
  have hμ₁ : GlobalTheory.SplitWeil.IsUnram (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₁) (isUnram_inv (isUnram_absPow _ _))
  have hμ₂ : GlobalTheory.SplitWeil.IsUnram (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₂) (isUnram_inv (isUnram_absPow _ _))
  refine ⟨_, _, hμ₁, hμ₂, ?_⟩
  let T : π.IntertwiningMap (prod₂ (GlobalTheory.SmGL.twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
      (GlobalTheory.SmGL.twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))) :=
    { toFun := fun v => ⟨⟨fun x => Λ (π x v), fun q x => by
          show Λ (π (q * x) v) = _
          rw [map_mul, Module.End.mul_apply]
          exact law π σ ρ ν₁ ν₂ Λ hΛ q (π x v)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
          have hh' : π h v = v := hh
          refine Subtype.ext (funext fun x => ?_)
          show Λ (π (x * h) v) = Λ (π x v)
          rw [map_mul, Module.End.mul_apply, hh'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (v + w)) = Λ (π x v) + Λ (π x w)
        rw [map_add (f := _), map_add (f := _)]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (c • v)) = c • Λ (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (π h v)) = Λ (π (x * h) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hT : Function.Injective T := by
    haveI := hπ
    refine (Representation.IsIrreducible.injective_or_eq_zero T).resolve_right fun h0 => hΛ0 (LinearMap.ext fun v => ?_)
    have h1 : (T v).1.1 1 = 0 := by rw [h0]; rfl
    change Λ (π 1 v) = 0 at h1
    simpa using h1
  have hσ' := hys.tw _ (isSmoothChar_of_isUnram hμ₁)
  have hρ' := hyr.tw _ (isSmoothChar_of_isUnram hμ₂)
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr _ hσ'.isSmooth hσ'.isIrreducible _ hρ'.isSmooth hρ'.isIrreducible
    (Fin.sum_univ_two _)
  have hsub := (IsSubquotient.of_injective T hT).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have key := SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ
    (t := ![_, _]) (Fin.forall_fin_two.2 ⟨hσ'.of_equiv (IrrGL.equivOf _ _ _), hρ'.of_equiv (IrrGL.equivOf _ _ _)⟩)
    hπ hsub
  rw [Fin.sum_univ_two] at key
  exact key

end GlobalTheory.IndChain.SuppStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem representation_inv_mul_apply_cancel_left {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H)
    (v : W) : ρ (γ * h)⁻¹ (ρ γ v) = ρ h⁻¹ v := by
  rw [← Module.End.mul_apply, ← map_mul]; congr 2; group

theorem representation_inv_mul_smul_one_of_trivial_right {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (h κ : H)
    (hκ : ρ κ⁻¹ = 1) (c : ℂ) (v : W) : ρ (h * κ)⁻¹ (c • ρ 1 v) = c • ρ h⁻¹ v := by
  rw [map_one, Module.End.one_apply, map_smul, _root_.mul_inv_rev, map_mul, hκ, one_mul]

theorem extV_law (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    (R.HV i t).e y (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
      ((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ) • (R.cV i).ρ γ ((R.HV i t).e y x) := by
  have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ _
  exact (SetLike.ext_iff.mp (hM.HV i t).2.1 ((R.HV i t).e y)).mp h1 γ x k

theorem extV_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (γ * h) = R.extV i t y h := by
  have hx : (finHom (Vc D i)).rangeRestrict (γ * h) = Formalism.IndefR.Bridge.ratF (Vc D i) ⟨γ, hγ⟩ *
      (finHom (Vc D i)).rangeRestrict h * ((1 : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [Formalism.IndefR.Bridge.ratF]
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h)) = (R.cV i).ρ γ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y ⟨γ, hγ⟩ ((finHom (Vc D i)).rangeRestrict h) 1
      _ = _ := by simp only [map_one, Units.val_one, one_smul]
  show (R.cV i).ρ (γ * h)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h))) =
    (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_apply_cancel_left _ γ h _

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (κ : GA D (Vc D i)) (hκ : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • R.extV i t y h := by
  let k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J := ⟨(finHom (Vc D i)).rangeRestrict κ, hκ.2⟩
  have hx : (finHom (Vc D i)).rangeRestrict (h * κ) = Formalism.IndefR.Bridge.ratF (Vc D i) 1 *
      (finHom (Vc D i)).rangeRestrict h * (k : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [k]
  have hχ : (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ := rfl
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • (R.cV i).ρ 1 ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y 1 ((finHom (Vc D i)).rangeRestrict h) k
      _ = _ := congrArg (· • _) hχ
  show (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ))) =
    _ • (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_smul_one_of_trivial_right _ h κ ((hM.cV i).1 _ ((GfC (Vc D i)).inv_mem hκ.1)) _ _

def compF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ) :
    GA D (Vc D i) → ℂ :=
  fun h => l (R.extV i t y h)

theorem compF_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (compF R i t y l) := by
  intro k hk h
  exact (congrArg l (extV_type R hM i t y k hk h)).trans (by rw [map_smul, smul_eq_mul]; rfl)

theorem compF_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    compF R i t y l (γ * h) = compF R i t y l h :=
  congrArg l (extV_left R hM i t y γ hγ h)

theorem theta_left (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hP : R.FullP)
    (φ : WO (Vc D i) (Wc D i) → ℂ) (hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ) (g : GA D (Wc D i))
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) (γ * h) g φ = thetaKO (R.ωP i t) h g φ := by
  have hm : ((γ * h, g) : GA D (Vc D i) × GA D (Wc D i)) = (γ, 1) * (h, g) := by rw [Prod.mk_mul_mk, one_mul]
  show R.ωP i t (γ * h, g) φ 0 = R.ωP i t (h, g) φ 0
  rw [hm, map_mul, Module.End.mul_apply]
  exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ φ hφ)

theorem theta_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (φ : WO (Vc D i) (Wc D i) → ℂ)
    (g : GA D (Wc D i)) (κ h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) φ) = thetaKO (R.ωP i t) (h * κ) g φ := by
  show R.ωP i t (h, g) (R.ωP i t (κ, 1) φ) 0 = R.ωP i t (h * κ, g) φ 0
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem theta_avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        thetaKO (R.ωP i t) (h * (κ j)⁻¹) g f := by
  rw [← Finset.sum_congr rfl fun j _ => congrArg (_ * ·) (theta_transl R i t f g (κ j)⁻¹ h)]
  show R.ωP i t (h, g) (avgW R i t PP a tr ε κ f) 0 = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [avgW, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem sum_compF_eq_zero (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (hNC : NoChi R i t y) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (ha : a ≠ 0) (tr : Bool) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (κ : G → GA D (Vc D i)) (hκ : IsLifts R i t κ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (h : GA D (Vc D i)) :
    ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      compF R i t y l (h * κ j) = 0 := by
  have h0 := congrFun (hNC PP a ha tr ε hε l) h
  refine Eq.trans ?_ h0
  simp only [gaL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = mirC R i PP a tr ε j * actG0 (Vc D i) (R.βV i) (R.datVt i t) (R.eG j) (compF R i t y l) h
  rw [level_action_spec (compF_type R hM i t y l) ⟨κ j, hκ j⟩ (κ j) (hκ j) h]
  ring

def termF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) : GA D (Vc D i) → ℂ :=
  fun h => thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h

theorem termF_eq (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) :
    (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ⁻¹, 1) f) * l (R.extV i t y h)) = termF R i t y l f g κ := by
  funext h
  exact congrArg (· * l (R.extV i t y h)) (theta_transl R i t f g κ⁻¹ h)

theorem termF_left (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.FullP) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f)
    (g : GA D (Wc D i)) (κ : GA D (Vc D i)) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    termF R i t y l f g κ (γ * h) = termF R i t y l f g κ h := by
  show thetaKO (R.ωP i t) (γ * h * κ⁻¹) g f * compF R i t y l (γ * h) =
    thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h
  rw [mul_assoc, theta_left R i t hP f hf g γ hγ, compF_left R hM i t y l γ hγ h]

theorem avgLaw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC PP a ha tr ε hε κ hκ f hf l g
  have hM := hG.core.models
  obtain ⟨hmeas, hfd⟩ := hM.νV i t
  haveI : (R.νV i t).IsHaarMeasure := hmeas.1
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hmeas.1
  have hu_int : ∀ j, IntegrableOn (termF R i t y l f g (κ j)) (R.fdV i t) (R.νV i t) := by
    intro j
    have h1 := GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y (R.ωP i t ((κ j)⁻¹, 1) f) l g
      ((hP i t).datum.om_pres _ f hf)
    exact (congrArg (fun φ => IntegrableOn φ (R.fdV i t) (R.νV i t)) (termF_eq R i t y l f g (κ j))).mp h1
  have hv_int : ∀ j, IntegrableOn (fun h => termF R i t y l f g (κ j) (h * κ j)) (R.fdV i t) (R.νV i t) :=
    fun j => GlobalTheory.integrableOn_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h) (hu_int j)
  have hsub : ∀ j, ∫ h in R.fdV i t, termF R i t y l f g (κ j) h ∂(R.νV i t) =
      ∫ h in R.fdV i t, termF R i t y l f g (κ j) (h * κ j) ∂(R.νV i t) :=
    fun j => (GlobalTheory.setIntegral_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h)).symm
  have hpt1 : ∀ h, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        termF R i t y l f g (κ j) h := by
    intro h
    rw [theta_avgW, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  have hpt2 : ∀ h, ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      termF R i t y l f g (κ j) (h * κ j) = 0 := by
    intro h
    have e : ∀ j, termF R i t y l f g (κ j) (h * κ j) = thetaKO (R.ωP i t) h g f * compF R i t y l (h * κ j) := by
      intro j
      show thetaKO (R.ωP i t) (h * κ j * (κ j)⁻¹) g f * _ = _
      rw [mul_inv_cancel_right]
    simp only [e]
    rw [← mul_zero (thetaKO (R.ωP i t) h g f), ← sum_compF_eq_zero R hM i t y hNC PP a ha tr ε hε κ hκ l h,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h ∂(R.νV i t) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1),
    integral_finsetSum _ fun j _ => (hu_int j).const_mul _]
  simp only [integral_const_mul]
  simp only [hsub]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun j _ => (hv_int j).const_mul _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt2)]
  exact integral_zero _ _

end GlobalTheory.DownLift.GenFinite

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_averages_theta_pair_zero_without_character : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  first | exact @GlobalTheory.DownLift.GenFinite.avgLaw | exact GlobalTheory.DownLift.GenFinite.avgLaw | (intros; apply GlobalTheory.DownLift.GenFinite.avgLaw <;> assumption)
end
end
