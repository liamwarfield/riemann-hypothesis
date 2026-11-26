module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointDarbouxTrivialArchimedean
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointDarbouxTrivialArchimedean
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.GfCArch

def infIncl (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun a := ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((a + b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((c • a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_fst (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u) : u • x = 0 := by
  let e : AF F := ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  let f : AF F := ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have hf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F f = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h0 : f • u = 0 := hu f hf
  have hef : e + f = 1 := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) + 0 = 1
      rw [add_zero]
    · show (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + 1 = 1
      rw [zero_add]
  have hu' : u = e * u := by
    calc u = (e + f) * u := by rw [hef, one_mul]
      _ = e * u + f • u := add_mul _ _ _
      _ = e * u := by rw [h0, add_zero]
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (infIncl F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        (((show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact one_mul _
      · exact zero_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_comm, mul_smul, key, hx, map_zero, smul_zero]

theorem gfc_arch : ∀ (D : D7) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X), g ∈ GfC X →
    ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1) = 0 := by
  intro D X k e J hJ g hg u hu
  have hM : ∀ a b, Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 :=
    (GlobalTheory.FinPl.KOpen.mem_GfC_iff X g).1 hg
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1 = (Formalism.L2.Theta.mt X g - 1).submatrix e e := by
    show (Formalism.L2.Theta.mt X g).submatrix e e - 1 = _
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_fst _ _ _ (hM _ _) u hu

end GlobalTheory.GfCArch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointDarbouxTrivialArchimedeanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteUnitaryPoint_darboux_trivial_archimedean : ∀ (D : D7) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X), g ∈ GfC X →
    ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.GfCArch.gfc_arch | exact GlobalTheory.GfCArch.gfc_arch | (intros; apply GlobalTheory.GfCArch.gfc_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepListProdDistinctPlacesPureTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepListProdDistinctPlacesPureTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.PureListAct

theorem om_list_prod_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (φ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) →
    (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv v)) (φ v) (φ₁ v)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), l.Nodup → ∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, (l.map hv).prod) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => if v ∈ l then φ₁ v else φ v) := by
  intro F E _ _ _ _ _ σ n d Y Wd om hv φ φ₁ hφ hφ₁ hact hstd l
  induction l with
  | nil =>
    intro _ f
    have h1 : om (1, (([] : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))).map hv).prod) = 1 := by
      rw [List.map_nil, List.prod_nil, Prod.mk_one_one, map_one]
    rw [h1, Module.End.one_apply]
    congr 1
  | cons a t ih =>
    intro hl f
    rw [List.nodup_cons] at hl
    have hsplit : om (1, ((a :: t).map hv).prod) = om (1, hv a) * om (1, (t.map hv).prod) := by
      rw [List.map_cons, List.prod_cons, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [hsplit, Module.End.mul_apply, ih hl.2 f]
    set φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ :=
      fun v => if v ∈ t then φ₁ v else φ v with hφ'

    have hstd' : ∀ᶠ v in Filter.cofinite,
        φ' v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hstd, (List.finite_toSet t).compl_mem_cofinite] with v hv1 hv2
      have hvt : v ∉ t := hv2
      simp only [hφ', if_neg hvt]
      exact hv1
    have hSB' : ∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) := by
      intro v
      by_cases h : v ∈ t
      · simp only [hφ', if_pos h]; exact hφ₁ v
      · simp only [hφ', if_neg h]; exact hφ v
    have hat : φ' a = φ a := by simp only [hφ', if_neg hl.1]

    obtain ⟨r, hr, htens⟩ := GlobalTheory.PureFactor.exists_rest_factor a f φ' hstd'
    have hfac : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F a) (φ a) r := by
      rw [htens, ← hat, Function.update_eq_self]
    have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.AdelicU.evFin F a) (φ a) r :=
      ⟨hr, hfac ▸ GlobalTheory.TensUniq.pure_mem_schA f φ' hSB' hstd'⟩
    rw [hfac, hact a r hrest, htens]
    congr 1
    funext v
    by_cases h : v = a
    · subst h
      simp
    · rw [Function.update_of_ne h]
      simp [hφ', h]

end GlobalTheory.PureListAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepListProdDistinctPlacesPureTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_list_prod_distinctPlaces_pureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (φ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) →
    (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv v)) (φ v) (φ₁ v)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), l.Nodup → ∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, (l.map hv).prod) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => if v ∈ l then φ₁ v else φ v) := by
  first | exact @GlobalTheory.PureListAct.om_list_prod_pure | exact GlobalTheory.PureListAct.om_list_prod_pure | (intros; apply GlobalTheory.PureListAct.om_list_prod_pure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedOfFixesPureTensorsVacuaOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedOfFixesPureTensorsVacuaOutside
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

theorem GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))), M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) →
    (∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) ψ → ψ = M.vac v := by
  intro F E _ _ _ _ _ σ n d Y Wd M om v k S hvac hstd hfix ψ hψ
  let ind : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

  let φ := Function.update ind v (M.vac v)
  have hφv : φ v = M.vac v := by simp [φ]
  have hφw : ∀ w, w ≠ v → φ w = ind w := fun w h => by simp [φ, h]
  have hφev : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton v).subset fun w hw => ?_
    by_contra hne
    exact hw (hφw w hne)
  have hSB : ∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; rw [hφv]; exact hvac
    · rw [hφw w h]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
  obtain ⟨r, hrinv, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφev
  have hupd : ∀ ψ₀, Function.update φ v ψ₀ = Function.update ind v ψ₀ :=
    fun ψ₀ => Function.update_idem _ _ _

  have hfixφ : om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    refine hfix f φ hSB fun w hw => ?_
    by_cases h : w = v
    · subst h; exact hφv
    · rw [hφw w h, hstd w hw]
  have hpv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    rw [hrt, hupd]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest
    refine ⟨hrinv, ?_⟩
    rw [hpv]
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hφev
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) ψ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    rw [← hψ r hRest, hpv, hfixφ]

  have hr0 : r 0 ≠ 0 := by
    have h1 := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at h1
    rw [h1, hupd]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have e1 : (fun i : Fin n × Fin d => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : Fin n × Fin d → AF F) i)) = 0 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : Fin n × Fin d → AF F) i).1 = 0
      exact map_zero _
    have e2 : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), Function.update ind v (fun _ => 1) w
        (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1 := by
      intro w
      by_cases h : w = v
      · subst h; simp
      · rw [Function.update_of_ne h]
        show Set.indicator {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
          (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1
        rw [Set.indicator_of_mem]
        · rfl
        · simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
          exact fun _ => zero_mem _
    rw [e1, finprod_congr e2, finprod_one, mul_one]
    exact hf
  funext y
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.EmbChart.atPlace v (y i)) := by
    intro u hu
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hrz : r (fun i => GlobalTheory.EmbChart.atPlace v (y i)) = r 0 := by
    simpa using hrinv 0 _ hz
  have h2 := congrFun key (fun i => GlobalTheory.EmbChart.atPlace v (y i))
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.EmbChart.evFin_atPlace, hrz] at h2
  exact mul_right_cancel₀ hr0 h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedOfFixesPureTensorsVacuaOutsideStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_fixed_of_fixes_pureTensors_vacuaOutside : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))), M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) →
    (∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) ψ → ψ = M.vac v := by
  first | exact @GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed | exact GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed | (intros; apply GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutUnitaryPointStabilizesLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutUnitaryPointStabilizesLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
open scoped Classical

noncomputable section
namespace GlobalTheory.IdemCut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem smul_phi_of_mul_eq_zero {a e : AF F} (h : a * e = 0) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_zero, zero_smul, add_zero]

theorem smul_phi_of_mul_eq_self {a e : AF F} (h : a * e = a) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • M := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_self, zero_smul, zero_add]

theorem idempotentCut_latticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₁ ⊆ S →
      (∀ w ∉ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u * e = 0 ∨ u * e = u) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  intro F E _ _ _ _ _ σ B a a' G hG h
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h) G.W.L hG.hW.lat
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h⁻¹) G.W.L hG.hW.lat
  refine ⟨S₁ ∪ S₂, fun S e he hS hcut => ?_⟩
  have key : ∀ w ∉ S, ∀ (X : ℕ) (Xs : Spc F E X), ∀ γ,
      γ * (mat (loc e he h))ᵀ ∈ latAtV Xs G.W w ↔ γ ∈ latAtV Xs G.W w := by
    intro w hw X Xs γ
    have hw1 : w ∉ S₁ := fun h' => hw (hS (Finset.mem_union_left _ h'))
    have hw2 : w ∉ S₂ := fun h' => hw (hS (Finset.mem_union_right _ h'))
    refine GlobalTheory.T.tensorLattice_mul_transpose_stable_iff F E X _ Xs G.W w _ _ (mat_inv_mul (loc e he h)) ?_ ?_ γ
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₁ w hw1 u hu hint y hy
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc_inv]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₂ w hw2 u hu hint y hy
  exact ⟨fun w hw => key w hw _ G.V, fun w hw => key w hw _ G.V'⟩

end GlobalTheory.IdemCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentCutUnitaryPointStabilizesLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentCut_unitaryPoint_stabilizes_lattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₁ ⊆ S →
      (∀ w ∉ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u * e = 0 ∨ u * e = u) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  first | exact @GlobalTheory.IdemCut.idempotentCut_latticeStabilizer | exact GlobalTheory.IdemCut.idempotentCut_latticeStabilizer | (intros; apply GlobalTheory.IdemCut.idempotentCut_latticeStabilizer <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
open scoped Classical
namespace GlobalTheory.PlacePureFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

theorem side {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (om : Rep σ Y Wd) (h : UA σ Wd.J)
    (hloc : ∀ v, ∀ hh ∈ UAt σ Wd (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, hh)) φ φ₁)
    (S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
    (hfix : ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₀ ⊆ S →
      (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u * e = 0) →
      (∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * e = 0 ∨ u * e = u) →
      ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
        om (1, loc e he h) (pure f φ) = pure f φ)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
      (∀ v, Acts (evFin F v) (om (1, loc (idem F v) (idem_mul_self v) h)) (φ v) (φ₁ v)) ∧
      om (1, h) (pure f φ) = pure f φ₁ := by
  have hvAt : ∀ v, loc (idem F v) (idem_mul_self v) h ∈ UAt σ Wd (evFin F v) := by
    intro v u hu
    show u • (mat (loc (idem F v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  choose φ₁ hφ₁SB hφ₁Act using fun v => hloc v _ (hvAt v) (φ v) (hSB v)
  have hN : {v | ¬ φ v = M.vac v}.Finite := hvac
  have hN2 : {v | ¬ M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hM.std
  set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) := S₀ ∪ hN.toFinset ∪ hN2.toFinset with hSdef
  have hS₀ : S₀ ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hφS : ∀ w ∉ S, φ w = M.vac w := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_left _ (Finset.mem_union_right _ (hN.mem_toFinset.2 hc)))
  have hvacS : ∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := fun w hw => by
    by_contra hc; exact hw (Finset.mem_union_right _ (hN2.mem_toFinset.2 hc))
  have hidem_at : ∀ w v (u : AF F), At (evFin F w) u → w ≠ v → u * idem F v = 0 := by
    intro w v u hu hwv
    apply mul_idem_of_evFin
    rw [← idem_mul_of_at hu, map_mul, evFin_idem, if_neg (Ne.symm hwv), zero_mul]
  have key : ∀ v ∉ S, φ₁ v = φ v := by
    intro v hv
    have hA := hφ₁Act v
    rw [hφS v hv] at hA ⊢
    refine GlobalTheory.T.vacuum_fixed_of_fixes_pureTensors_vacuaOutside F E σ M om v _ S (hM.vac v).1 hvacS (fun f' φ' hSB' hout => ?_) (φ₁ v) hA
    refine hfix S (idem F v) (idem_mul_self v) hS₀ (fun w hw u hu => hidem_at w v u hu (fun e => hv (e ▸ hw)))
      (fun w _ u hu => ?_) f' φ' hSB' hout
    by_cases hwv : w = v
    · subst hwv; right; rw [mul_comm]; exact idem_mul_of_at hu
    · left; exact hidem_at w v u hu hwv
  refine ⟨φ₁, hφ₁SB, ?_, hφ₁Act, ?_⟩
  · filter_upwards [hvac, S.eventually_cofinite_notMem] with v hv hvS
    rw [key v hvS, hv]
  · have heS : idemS F S * idemS F S = idemS F S := idemS_mul_self S
    have heS' : (1 - idemS F S) * (1 - idemS F S) = 1 - idemS F S := by
      rw [sub_mul, one_mul, mul_sub, mul_one, heS, sub_self, sub_zero]
    have horth : idemS F S * (1 - idemS F S) = 0 := by rw [mul_sub, mul_one, heS, sub_self]
    have hdec : h = (S.toList.map fun v => loc (idem F v) (idem_mul_self v) h).prod * loc (1 - idemS F S) heS' h := by
      apply ua_ext
      rw [mat_mul, mat_prod_loc h _ S.nodup_toList, Finset.toList_toFinset, mat_loc, phi_mul_orth horth,
        add_sub_cancel, phi_one]
    have hnot : ∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * idemS F S = 0 := by
      intro w hw u hu
      rw [← idem_mul_of_at hu, mul_comm (idem F w), mul_assoc, idem_mul_idemS_of_notMem hw, mul_zero]
    have hk : om (1, loc (1 - idemS F S) heS' h) (pure f φ) = pure f φ := by
      refine hfix S _ heS' hS₀ (fun w hw u hu => ?_) (fun w hw u hu => Or.inr ?_) f φ hSB hφS
      · calc u * (1 - idemS F S) = (idem F w * u) * (1 - idemS F S) := by rw [idem_mul_of_at hu]
          _ = u * (idem F w - idem F w * idemS F S) := by ring
          _ = 0 := by rw [idem_mul_idemS_of_mem hw, sub_self, mul_zero]
      · rw [mul_sub, mul_one, hnot w hw u hu, sub_zero]
    have hmul : ∀ (a b : UA σ Wd.J) (x : (Fin n × Fin d → AF F) → ℂ), om (1, a * b) x = om (1, a) (om (1, b) x) := by
      intro a b x
      have : ((1 : UA σ Y.J), a * b) = (1, a) * (1, b) := by simp
      rw [this, map_mul]; rfl
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hM.std).mono fun v hv => hv.1.trans hv.2
    conv_lhs => rw [hdec]
    rw [hmul, hk, GlobalTheory.T.weilRep_list_prod_distinctPlaces_pureTensor F E σ om (fun v => loc (idem F v) (idem_mul_self v) h) φ φ₁ hSB hφ₁SB hφ₁Act hstd S.toList
      S.nodup_toList f]
    congr 1
    funext v
    by_cases hv : v ∈ S
    · rw [if_pos (Finset.mem_toList.2 hv)]
    · rw [if_neg (mt Finset.mem_toList.1 hv), key v hv]

end GlobalTheory.PlacePureFin
end
