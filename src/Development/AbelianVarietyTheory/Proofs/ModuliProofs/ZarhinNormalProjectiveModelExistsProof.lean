module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelOfGeometricHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelOfGeometricHalf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_model_semiAbelian_of_geo :
    GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ZHGeoSt → ZHSt := by
  intro hN hU hL hL2 hTors hGeo o Ω _ _ _ hb S ρ hBig J₀ _ t₀ ht hfin
  have hT : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hN hU hL hL2 hTors o Ω S ρ).1
  obtain ⟨M, U₀, hA, -, hD⟩ := @GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω _ _ _ _ S J₀ _ t₀ ht hfin
  obtain ⟨EE, hEE, hE⟩ := @GlobalTheory.ZH.exists_isEE_of_adm o Ω _ _ _ _ S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have hsec := @GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω _ _ _ _ S M U₀ EE hA hll hte h0a h0b hwt h11 h12 hne hE
  obtain ⟨n, a, GG, hGG⟩ := @GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω _ _ _ _ S M U₀ EE hA hll.2 h0b hne hE hsec
  exact ⟨M, U₀, EE, hO, hD, hEE, hGeo o Ω S ρ hBig M U₀ EE hO hEE ⟨n, a, fun k j => (GG k j : Ω), hGG⟩⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelOfGeometricHalfStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianModel_of_geometricHalf : GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ZHGeoSt → ZHSt := by
  first | exact @GlobalTheory.ZH.exists_model_semiAbelian_of_geo | exact GlobalTheory.ZH.exists_model_semiAbelian_of_geo | (intros; apply GlobalTheory.ZH.exists_model_semiAbelian_of_geo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinProjectiveModelOfSemistableReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinProjectiveModelOfSemistableReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem zh_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHSt :=
  fun S => GlobalTheory.T.exists_semiAbelianModel_of_geometricHalf S GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2 (GlobalTheory.T.zarhinGeometric_of_semistableReduction S)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinProjectiveModelOfSemistableReductionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProjectiveModel_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHSt := by
  first | exact @GlobalTheory.zh_of_semistableReduction | exact GlobalTheory.zh_of_semistableReduction | (intros; apply GlobalTheory.zh_of_semistableReduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProof
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem zhSt_holds : GlobalTheory.ZH.ZHSt :=
  GlobalTheory.T.zarhinProjectiveModel_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProofStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinNormalProjectiveModelExists_proof : GlobalTheory.ZH.ZHSt := by
  first | exact @GlobalTheory.zhSt_holds | exact GlobalTheory.zhSt_holds | (intros; apply GlobalTheory.zhSt_holds <;> assumption)
end
