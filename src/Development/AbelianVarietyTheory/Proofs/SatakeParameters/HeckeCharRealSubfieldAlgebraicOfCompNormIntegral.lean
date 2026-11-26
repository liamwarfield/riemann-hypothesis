module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldProdEmbeddingsRegroupMaximalRealStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_prod_embeddings_regroup_maximalReal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : (E →+* ℂ) → ℤ), (∀ τ, k (ComplexEmbedding.conjugate τ) = k τ) → ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ, ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ = ∏ φ, g φ ^ (2 * n φ) := by
  first | exact @GlobalTheory.cm_prod_regroup_maximalReal | exact GlobalTheory.cm_prod_regroup_maximalReal | (intros; apply GlobalTheory.cm_prod_regroup_maximalReal <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapNormToMaxRealInfiniteIdele
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapNormToMaxRealInfiniteIdele
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.GalReal

theorem ideleMap_ideleNorm_infId (E : Type) [Field E] [NumberField E] [IsCMField E] (u : (Cinf E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (ideleNorm E (infId E u)) =
      infId E (u * Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  have h1 : ∀ t : (Cinf E)ˣ, pInf E (infId E t).val = t.val := fun t => by
    change (infEq E).symm (1 - infEq E 1 + infEq E t.val) = _
    simp
  have h2 : ∀ t : (Cinf E)ˣ, pFin E (infId E t).val = 1 := fun t => by
    change (1 : Af E) - 0 + 0 = 1
    simp
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, GlobalTheory.PolChar.ideleConj_eq, map_mul]
  congr 1
  refine Units.ext (ad_ext ?_ ?_)
  · change pInf E (GlobalTheory.UnitaryBC.conjAd E (infId E u).val) = _
    rw [GlobalTheory.ThetaPull.pInf_conjAd, h1, h1]
    rfl
  · change pFin E (GlobalTheory.UnitaryBC.conjAd E (infId E u).val) = _
    rw [GlobalTheory.ThetaPull.pFin_conjAd, h2, h2, map_one]

end GlobalTheory.GalReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapNormToMaxRealInfiniteIdeleStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleMap_normToMaxReal_infiniteIdele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : (Cinf E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (ideleNorm E (infId E u)) = infId E (u * Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  first | exact @GlobalTheory.GalReal.ideleMap_ideleNorm_infId | exact GlobalTheory.GalReal.ideleMap_ideleNorm_infId | (intros; apply GlobalTheory.GalReal.ideleMap_ideleNorm_infId <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapInfDiagMaxRealSubfieldCm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapInfDiagMaxRealSubfieldCm
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

noncomputable section

namespace GlobalTheory.InfDiagExt

theorem val_infDiag (L : Type) [Field L] [NumberField L] (k : Lˣ) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem ideleMap_infDiag_gen (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : Kˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (infDiag x) = infDiag (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L ((infDiag x : Ideles K) : AdeleRing (𝓞 K) K) = _
  rw [val_infDiag, val_infDiag]
  refine Prod.ext ?_ ?_
  · have h := congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L (x : K))
    exact h
  · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)

theorem ideleMap_infDiag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (maximalRealSubfield E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infDiag x) = infDiag (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) :=
  fun E _ _ _ x => ideleMap_infDiag_gen (maximalRealSubfield E) E x

end GlobalTheory.InfDiagExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapInfDiagMaxRealSubfieldCmStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (maximalRealSubfield E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infDiag x) = infDiag (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
  first | exact @GlobalTheory.InfDiagExt.ideleMap_infDiag | exact GlobalTheory.InfDiagExt.ideleMap_infDiag | (intros; apply GlobalTheory.InfDiagExt.ideleMap_infDiag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapOfAlgebraMaximalRealSubfieldInjectiveStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapOfAlgebraMaximalRealSubfieldInjective
open NumberField HeckeCharacterZeroLocus.ThmBIn GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.UnitaryHeckeBaseChange

namespace GlobalTheory.IdeleMapInjective

theorem adeleMap_injective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Function.Injective (adeleMap F E) := by
  intro a b hab
  rw [← toAdele_algebraMap, ← toAdele_algebraMap] at hab
  exact Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
    (algebraMap F E).injective ((bijective_toAdele h).1 hab)

theorem ideleMap_injective (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E) := by
  have h : IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  intro a b hab
  exact Units.ext (adeleMap_injective h (congrArg Units.val hab))

end GlobalTheory.IdeleMapInjective
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleMapOfAlgebra_maximalRealSubfield_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E) := by
  first | exact @GlobalTheory.IdeleMapInjective.ideleMap_injective | exact GlobalTheory.IdeleMapInjective.ideleMap_injective | (intros; apply GlobalTheory.IdeleMapInjective.ideleMap_injective <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRealSubfieldAlgebraicOfCompNormIntegral
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.CMRealAlg

theorem isAlgPos_of_compNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)),
    (∀ τ : E →+* ℂ, ∃ k : ℤ, expo (compNorm E χ) τ = k) → ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  intro E _ _ _ χ h
  choose k hk using h
  have hkc : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ := fun τ => by
    have := (hk _).symm.trans ((GlobalTheory.T.exponent_heckeChar_compNorm_conjEmbedding E χ τ).trans (hk τ))
    exact_mod_cast this
  obtain ⟨n, hn⟩ := GlobalTheory.T.cmField_prod_embeddings_regroup_maximalReal E k hkc
  refine ⟨n, fun x hx => ?_⟩
  have hpos : ∀ φ : maximalRealSubfield E →+* ℂ,
      ((‖φ (x : maximalRealSubfield E)‖ : ℝ) : ℂ) = φ x ∧ 0 < ‖φ (x : maximalRealSubfield E)‖ := by
    intro φ
    have hr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
    have h0 := hx hr.embedding
    rw [← hr.coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    exact ⟨rfl, h0⟩
  let z : Cinf E := fun w => ((Real.log (w ((x : maximalRealSubfield E) : E)) / 2 : ℝ) : ℂ)
  let u : (Cinf E)ˣ := expU z
  have hu : u * Units.map (starRingEnd (Cinf E)).toMonoidHom u =
      Units.map (diagInf E).toMonoidHom (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
    apply Units.ext
    funext w
    have e1 := hpos (w.embedding.comp (algebraMap _ E))
    have e2 : ‖w.embedding ((x : maximalRealSubfield E) : E)‖ = w ((x : maximalRealSubfield E) : E) :=
      InfinitePlace.norm_embedding_eq w _
    change Complex.exp (z w) * starRingEnd ℂ (Complex.exp (z w)) = pInf E (algebraMap E (Ad E) ((x : maximalRealSubfield E) : E)) w
    rw [pInf_algebraMap, ← Complex.exp_conj, Complex.conj_ofReal, ← Complex.exp_add, ← Complex.ofReal_add,
      ← Complex.ofReal_exp, show Real.log (w ((x : maximalRealSubfield E) : E)) / 2 + Real.log (w ((x : maximalRealSubfield E) : E)) / 2 =
        Real.log (w ((x : maximalRealSubfield E) : E)) by ring, Real.exp_log (e2 ▸ e1.2), ← e2]
    exact e1.1
  have hN : ideleNorm E (infId E u) = infDiag x := GlobalTheory.T.ideleMapOfAlgebra_maximalRealSubfield_injective E (by rw [GlobalTheory.T.ideleMap_normToMaxReal_infiniteIdele, hu, ← InfType.infDiag_eq, GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm])
  have e1 : ((χ.inf x : ℂˣ) : ℂ) = ((chiInf (compNorm E χ) u : ℂˣ) : ℂ) := by
    rw [HChar.inf, MonoidHom.comp_apply, ← hN]; rfl
  rw [e1, chiInf_eq_prod _ k hk]
  let g : (maximalRealSubfield E →+* ℂ) → ℂ := fun φ =>
    Complex.exp ((Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ)
  have hc : ∀ τ : E →+* ℂ, coord τ (u : Cinf E) = g (τ.comp (algebraMap _ E)) := by
    intro τ
    rw [coord_expU]
    congr 1
    have e3 : z (InfinitePlace.mk τ) = ((Real.log ‖(τ.comp (algebraMap (maximalRealSubfield E) E)) (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ) := by
      simp only [z, InfinitePlace.apply]; rfl
    unfold coord
    split_ifs
    · exact e3
    · change starRingEnd ℂ (z (InfinitePlace.mk τ)) = _
      rw [e3, Complex.conj_ofReal]
  simp only [hc]
  rw [hn g]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [zpow_mul, zpow_two, ← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_exp,
    show Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 + Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 =
      Real.log ‖φ (x : maximalRealSubfield E)‖ by ring, Real.exp_log (hpos φ).2, (hpos φ).1]

end GlobalTheory.CMRealAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRealSubfieldAlgebraicOfCompNormIntegralStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_realSubfield_algebraic_of_comp_norm_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)), (∀ τ : E →+* ℂ, ∃ k : ℤ, expo (compNorm E χ) τ = k) → ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  first | exact @GlobalTheory.CMRealAlg.isAlgPos_of_compNorm | exact GlobalTheory.CMRealAlg.isAlgPos_of_compNorm | (intros; apply GlobalTheory.CMRealAlg.isAlgPos_of_compNorm <;> assumption)
end
