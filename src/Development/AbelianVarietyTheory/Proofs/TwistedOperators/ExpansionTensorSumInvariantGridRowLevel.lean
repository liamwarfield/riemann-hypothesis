module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffScalarInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermDatumRowMoveLevelEdgeFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermDatumRowMoveLevelEdgeFactors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.FlatRowMove

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fill_move (G : Grid k) (hs : 1 ≤ G.s) {j : ℕ} (hj : j + 1 < G.m)
    (κ : GL (Fin (G.rank (j + 1, G.m))) k) (x : ColArgs G) (y : RowArgs G) (e : Vars G) :
    fill hs x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) e =
      G.moveArgs .one (Pi.mulSingle (j + 1, G.m) κ) (fill hs x y e) := by
  funext b
  cases b with
  | theta i l =>
    by_cases hi : i = G.m
    · subst hi
      have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (G.m, l) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      have h2 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (G.m, l + 1) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, h1, h2, map_one, inv_one, Units.val_one,
        Matrix.one_mul, Matrix.mul_one, fill_theta]
    · simp [fill, Grid.moveArgs, hi]
  | ex i l =>
    by_cases hl : l = G.m
    · subst hl
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex]
      by_cases hij : i = j
      · subst hij
        have h1 : (Pi.mulSingle (i + 1, G.m) κ : G.VertexGroup) (i, G.m) = 1 :=
          Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
        rw [h1, Pi.mulSingle_eq_same, Function.update_of_ne (by omega), Function.update_self,
          map_one, Units.val_one, Matrix.mul_one, Assignment.read, invT_inv_val, Matrix.transpose_mul]
      · by_cases hij' : i = j + 1
        · subst hij'
          have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (j + 1 + 1, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
          rw [h1, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one,
            Matrix.one_mul, Assignment.read, invT_val, Matrix.transpose_mul]
        · have h1 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (i, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          have h2 : (Pi.mulSingle (j + 1, G.m) κ : G.VertexGroup) (i + 1, G.m) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          rw [h1, h2, Function.update_of_ne hij', Function.update_of_ne hij]
          simp only [map_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    · simp [fill, Grid.moveArgs, hl]

theorem mulSingle_comm (G : Grid k) {X : ℕ × ℕ} (κ : GL (Fin (G.rank X)) k) (g : G.VertexGroup) (hg : g X = 1) :
    Pi.mulSingle X κ * g = g * Pi.mulSingle X κ := by
  funext Y
  by_cases hY : Y = X
  · subst hY; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne hY]

variable [MeasurableSpace k] [BorelSpace k]

theorem flat_move (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (g : G.VertexGroup) (T : G.Args → ℂ) {j : ℕ} (hj : j + 1 < G.m) (κ : GL (Fin (G.rank (j + 1, G.m))) k)
    (hg : g (j + 1, G.m) = 1)
    (hT : G.pathAct .one (oppositePath G.m) (Pi.mulSingle (j + 1, G.m) κ) T = T) (x : ColArgs G) (y : RowArgs G) :
    ((oppositePath G.m).map (G.edgeFactor .one (Pi.mulSingle (j + 1, G.m) κ))).prod *
      flatTensor hs ψ ν (GlobalTheory.FunObj.moved G keep g T) x
        (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
      flatTensor hs ψ ν (GlobalTheory.FunObj.moved G keep g T) x y := by
  have hF : ∀ z, ((oppositePath G.m).map (G.edgeFactor .one (Pi.mulSingle (j + 1, G.m) κ))).prod *
      GlobalTheory.FunObj.moved G keep g T (G.moveArgs .one (Pi.mulSingle (j + 1, G.m) κ) z) = GlobalTheory.FunObj.moved G keep g T z := by
    intro z
    have h := congrFun (congrArg (G.pathAct .one (oppositePath G.m) g) hT) z
    rw [← Grid.pathAct_mul, ← mulSingle_comm G κ g hg, Grid.pathAct_mul] at h
    simp only [GlobalTheory.FunObj.moved]
    rw [← h]
    simp only [Grid.pathAct]
    ring
  simp only [flatTensor, flatIntegrand, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only [fill_move G hs hj κ x y e, ← mul_assoc, hF]

theorem term_datum_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ (w : locPl G t) (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w.1).rank (j + 1, (locGrid G t w.1).m))) (Kw w.1)), κ ∈ givenLevel G t w.1 (j + 1, D.R.m) →
    ∀ (x : ColArgs (locGrid G t w.1)) (y : RowArgs (locGrid G t w.1)),
    ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m) κ))).prod *
      (S.term t Φ β w).datum x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
    (S.term t Φ β w).datum x y := by
  intro D T L sc G W U S t Φ β μ₀ hL hde hc ht w j hj κ hκ x y
  have hT := GlobalTheory.T.flippedLocalTotalTensor_fixed_by_innerVertex_level S Φ ht hL hde hc w.1 w.2 j hj κ hκ
  have hg : ((repsAt G t w.1).elt (β w)) (j + 1, D.R.m) = 1 := by
    simp only [Reps.elt, onColumn]
    exact dif_neg (by show j + 1 ≠ D.R.m; omega)
  exact flat_move (locGrid G t w.1) _ _ _ _ _ _ hj κ hg hT x y

end GlobalTheory.FlatRowMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermDatumRowMoveLevelEdgeFactorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termDatum_rowMove_level_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → ∀ (w : locPl G t) (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w.1).rank (j + 1, (locGrid G t w.1).m))) (Kw w.1)), κ ∈ givenLevel G t w.1 (j + 1, D.R.m) →
    ∀ (x : ColArgs (locGrid G t w.1)) (y : RowArgs (locGrid G t w.1)),
    ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m) κ))).prod *
      (S.term t Φ β w).datum x (Function.update (Function.update y j (y j * κ.val)) (j + 1) (κ⁻¹.val * y (j + 1))) =
    (S.term t Φ β w).datum x y := by
  first | exact @GlobalTheory.FlatRowMove.term_datum_move | exact GlobalTheory.FlatRowMove.term_datum_move | (intros; apply GlobalTheory.FlatRowMove.term_datum_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathEdgeFactorProdIntegralVertex
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathEdgeFactorProdIntegralVertex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section
namespace GlobalTheory.OppositeEdges

theorem oppositePath_prod_mulSingle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Γ : Grid k) (j : ℕ) :
    j + 1 < Γ.m → ∀ (κ : GL (Fin (Γ.rank (j + 1, Γ.m))) k), κ ∈ GlobalTheory.SplitWeil.KO k _ →
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (j + 1, Γ.m) κ))).prod =
      ((Γ.chi (Γ.m - (j + 1)) (gdet κ) : ℂˣ) : ℂ) * (((Γ.chi (Γ.m - j) (gdet κ))⁻¹ : ℂˣ) : ℂ) := by
  intro hj κ hκ
  set g : Γ.VertexGroup := Pi.mulSingle (j + 1, Γ.m) κ with hg
  have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
  have hK : ∀ Y, g Y ∈ GlobalTheory.SplitWeil.KO k _ := by
    intro Y
    by_cases hY : Y = (j + 1, Γ.m)
    · subst hY; simpa [hg] using hκ
    · rw [hg, Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have ha : ∀ Y, ∀ z : ℂ, apow (gdet (Assignment.one.read (g Y))) z = 1 := fun Y z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hK Y))) z

  have hfar : ∀ b : Edge, b.src ≠ (j + 1, Γ.m) → b.tgt ≠ (j + 1, Γ.m) → Γ.edgeFactor .one g b = 1 := by
    intro b h1 h2
    simp [Grid.edgeFactor, hg, Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2, hap]
  have htheta : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one g)).prod = 1 := by
    refine List.prod_eq_one fun c hc => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  have hex : (((List.range Γ.m).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one g)).prod =
      ∏ i ∈ Finset.range Γ.m, Γ.edgeFactor .one g (.ex i Γ.m) := by
    rw [List.map_map, Finset.prod_eq_multiset_prod]; rfl
  have hne : j ≠ j + 1 := by omega
  have hrest : ∀ i ∈ Finset.range Γ.m, i ≠ j ∧ i ≠ j + 1 → Γ.edgeFactor .one g (.ex i Γ.m) = 1 := by
    intro i _ hi
    apply hfar <;> simp [Edge.src, Edge.tgt] <;> omega
  rw [oppositePath, List.map_append, List.prod_append, htheta, mul_one, hex,
    Finset.prod_eq_mul j (j + 1) hne hrest (by simp; omega) (by simp; omega)]
  have hκa : ∀ z : ℂ, apow (gdet (Assignment.one.read κ)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO hκ)) z
  have hj1 : (j + 1 + 1, Γ.m) ≠ (j + 1, Γ.m) := by simp
  have hj0 : (j, Γ.m) ≠ (j + 1, Γ.m) := by simp
  simp only [Grid.edgeFactor, Edge.src, Edge.tgt, ha, mul_one, hg, Pi.mulSingle_eq_of_ne hj1,
    Pi.mulSingle_eq_of_ne hj0, Pi.mulSingle_eq_same, hκa, map_one, hap, Units.val_one, inv_one, one_mul]
  simp only [Grid.kappa, Grid.blockChar, MonoidHom.div_apply, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Nat.add_sub_cancel]
  have h1 := Units.ne_zero (Γ.chi (Γ.m - (j + 1)) (gdet κ))
  have h2 := Units.ne_zero (Γ.chi (Γ.m - j) (gdet κ))
  have h3 := Units.ne_zero ((Γ.eta ^ ((Γ.rank (j + 1, Γ.m) + 1) % 2)) (gdet κ))
  field_simp

end GlobalTheory.OppositeEdges
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathEdgeFactorProdIntegralVertexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oppositePath_edgeFactor_prod_integral_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Grid k) (j : ℕ),
    j + 1 < Γ.m → ∀ (κ : GL (Fin (Γ.rank (j + 1, Γ.m))) k), κ ∈ GlobalTheory.SplitWeil.KO k _ →
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (j + 1, Γ.m) κ))).prod =
      ((Γ.chi (Γ.m - (j + 1)) (gdet κ) : ℂˣ) : ℂ) * (((Γ.chi (Γ.m - j) (gdet κ))⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.OppositeEdges.oppositePath_prod_mulSingle | exact GlobalTheory.OppositeEdges.oppositePath_prod_mulSingle | (intros; apply GlobalTheory.OppositeEdges.oppositePath_prod_mulSingle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.RowVacScalar


set_option maxHeartbeats 1000000 in
theorem splitScal_mul_eq_oppositePath : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S t ht j hj k hk w hw hs
  have hK : inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w) _ := by
    have h1 := hk
    simp only [GridChoice.levRow, prodLev, Subgroup.mem_inf, Subgroup.mem_iInf] at h1
    have h2 := h1.1 ⟨w, hw⟩
    rw [Subgroup.mem_comap] at h2
    rwa [GlobalTheory.LastRowLat.givenLevel_inner G t w (j + 1, D.R.m) (by simp) (by simp; have := D.R.two_le_m; omega)] at h2
  have he : idemAt w * idemAt w = idemAt w := (Classical.epsilon_spec hs).1.1
  have d1 : ∀ V : HSp D, detIdl (idemAt w) V 1 = 1 := fun V => by
    unfold detIdl; split_ifs <;> simp
  have dneg : detIdl (idemAt w) (negSp (G.V (.grid (j + 1) D.R.m))) (negGA _ (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := by
    refine Units.ext ?_
    rw [detIdl_val he, detIdl_val he, mt_negGA]
  have hpar : Odd (G.pS (.chi (j + 1) D.R.m)).rank ↔ Odd (G.pT (.chi j D.R.m)).rank := by
    have r0 := (rank_vertex G t w (X := (j, D.R.m)) ⟨by omega, le_rfl⟩).symm
    have r2 := (rank_vertex G t w (X := (j + 1 + 1, D.R.m)) ⟨by omega, le_rfl⟩).symm
    change Odd (G.V (.grid (j + 1 + 1) D.R.m)).rank ↔ Odd (G.V (.grid j D.R.m)).rank
    rw [r0, r2]
    simp only [Grid.rank, locGrid]
    rw [show D.R.r + D.R.m * D.R.t + (j + 1 + 1) * sLen D = (D.R.r + D.R.m * D.R.t + j * sLen D) + 2 * sLen D by ring]
    rw [Nat.odd_add]
    exact ⟨fun h => h.2 (even_two_mul _), fun h => ⟨fun _ => even_two_mul _, fun _ => h⟩⟩
  have key : ∀ (a b η : (AE D)ˣ →* Circle) (n n' : ℕ), (Odd n ↔ Odd n') → ∀ x,
      (Formalism.IndefR.Lift.attChr a η n x)⁻¹ * Formalism.IndefR.Lift.attChr b η n' x = (a x)⁻¹ * b x := by
    intro a b η n n' h x
    unfold Formalism.IndefR.Lift.attChr
    by_cases hn : Odd n
    · rw [if_pos hn, if_pos (h.1 hn), MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv,
        mul_comm (η x), mul_mul_mul_comm, mul_inv_cancel, mul_one]
    · rw [if_neg hn, if_neg (fun h' => hn (h.2 h'))]
  have hχ : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ y, ((G.ch.chi i (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((G.ch.chiH i).loc w y : ℂˣ) : ℂ) := fun i h1 h2 y => by
    have := congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq i h1 h2) w)
    simpa [GlobalTheory.LFun.locChar] using this
  refine Eq.trans ?_ (GlobalTheory.T.oppositePath_edgeFactor_prod_integral_vertex (locGrid G t w) j hj _ hK).symm
  simp only [splitScal, GridData.toPair, splitFacO, map_one, d1, inv_one, one_mul, mul_one]
  have eqS : detIdl (idemAt w) (G.pS (Pair.chi j D.R.m)) ((negGA (G.V (Node.grid (j + 1) D.R.m))) (moved S j k)) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := dneg
  have eqT : detIdl (idemAt w) (G.pT (Pair.chi (j + 1) D.R.m)) (moved S j k) =
      detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) := rfl
  rw [eqS, eqT, GlobalTheory.T.determinantIdeleAtSplitPlace_moved_gridNode S t j hj k w hs, ← Circle.coe_mul]
  rw [GridData.chrT, GridData.chrS]
  rw [key (G.chr (Pair.chi j D.R.m)) (G.chr (Pair.chi (j + 1) D.R.m)) L.eta _ _ hpar.symm]
  rw [Circle.coe_mul, Circle.coe_inv]
  dsimp only [GridData.chr]
  rw [hχ _ (by omega) (by omega), hχ _ (by omega) (by omega)]
  simp only [locGrid, Units.val_inv_eq_inv_val]
  exact mul_comm _ _

end GlobalTheory.RowVacScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceScalarsMulEqOppositePathEdgeFactorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ w ∈ locPl G t, (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    GlobalTheory.RowVacScalar.splitScal G (.chi j D.R.m) w (G.toPair (.chi j D.R.m) 1 (moved S j k)).1
                 (G.toPair (.chi j D.R.m) 1 (moved S j k)).2 *
      GlobalTheory.RowVacScalar.splitScal G (.chi (j + 1) D.R.m) w (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).1
        (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 =
    ((oppositePath D.R.m).map ((locGrid G t w).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | exact GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath | (intros; apply GlobalTheory.RowVacScalar.splitScal_mul_eq_oppositePath <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVacScalar

private theorem map_mt_one_eq_one {D : D7} (V : HSp D) : (Formalism.L2.Theta.mt V 1).map (finPart D) = 1 := by
  rw [Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem scalars_eq_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S μ₀ hL t ht j hj k hk c₁ c₂ h₁ h₂
  obtain ⟨hA, hB, hC, hD⟩ := GlobalTheory.RowMovedLat.moved_pair_stab S ht j hj k hk
  have e₁ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t j hj.le _ hA ?g₁ hB ?l₁ c₁ h₁
  have e₂ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t (j + 1) hj _ ?g₂ hC ?l₂ hD c₂ h₂
  · rw [e₁, e₂, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors S ht j hj k hk w.1 w.2 ⟨_, GlobalTheory.RowVacScalar.isIdemAt_idemAt hL G t w.2⟩
  case g₁ =>
    dsimp only [GridData.toPair]
    exact one_mem _
  case l₁ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_mt_one_eq_one, Matrix.one_mulVec]
  case g₂ =>
    dsimp only [GridData.toPair]
    rw [map_one]
    exact one_mem _
  case l₂ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_one, map_mt_one_eq_one, Matrix.one_mulVec]

end GlobalTheory.RowVacScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  first | exact @GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | exact GlobalTheory.RowVacScalar.scalars_eq_edgeFactors | (intros; apply GlobalTheory.RowVacScalar.scalars_eq_edgeFactors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) :=
  Function.update (Function.update z (.inr ⟨j, by omega⟩)
    (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
      (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
    (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
      WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))

theorem movPt_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j + 1, hj⟩) = actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :=
  Function.update_self _ _ _

theorem movPt_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j, by omega⟩) = actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 (z (.inr ⟨j, by omega⟩)) :=
  (Function.update_of_ne (by simp) _ _).trans (Function.update_self _ _ _)

theorem movPt_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movPt S j hj k z a = z a :=
  (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)

theorem movFn_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j + 1, hj⟩) x = v (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) := by
  unfold movFn; rw [Function.update_self]

theorem movFn_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j, by omega⟩) x = v (.inr ⟨j, by omega⟩) (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) := by
  unfold movFn; rw [Function.update_of_ne (by simp), Function.update_self]

theorem movFn_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movFn S j hj k v a = v a := by
  unfold movFn; rw [Function.update_of_ne h2, Function.update_of_ne h1]

theorem scale_movFn_apply (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (a : Fin D.R.m ⊕ Fin D.R.m) :
    (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) =
      ((Pi.mulSingle (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) c₁ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a *
        (Pi.mulSingle (.inr ⟨j + 1, hj⟩ : Fin D.R.m ⊕ Fin D.R.m) c₂ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a) *
        v a (movPt S j hj k z a) := by
  have hne : (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨j + 1, hj⟩ := by simp
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    have e1 : movFn S j hj k v (.inr ⟨j + 1, hj⟩) (z (.inr ⟨j + 1, hj⟩)) =
        v (.inr ⟨j + 1, hj⟩) (movPt S j hj k z (.inr ⟨j + 1, hj⟩)) :=
      (movFn_two S j hj k v (z (.inr ⟨j + 1, hj⟩))).trans (congrArg (v _) (movPt_two S j hj k z).symm)
    rw [Pi.smul_apply, smul_eq_mul, e1]
    simp [scaleAt, Pi.mulSingle_apply, hne.symm]
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      have e1 : movFn S j hj k v (.inr ⟨j, by omega⟩) (z (.inr ⟨j, by omega⟩)) =
          v (.inr ⟨j, by omega⟩) (movPt S j hj k z (.inr ⟨j, by omega⟩)) :=
        (movFn_one S j hj k v (z (.inr ⟨j, by omega⟩))).trans (congrArg (v _) (movPt_one S j hj k z).symm)
      rw [Pi.smul_apply, smul_eq_mul, e1]
      simp [scaleAt, Pi.mulSingle_apply, hne, Function.update_of_ne hne]
    · rw [Pi.smul_apply, smul_eq_mul, movFn_other S j hj k v a h1' h2', movPt_other S j hj k z a h1' h2']
      simp [scaleAt, Pi.mulSingle_apply, h1', h2', Function.update_of_ne h1', Function.update_of_ne h2']

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem prod_scale_movFn (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) = c₁ * c₂ * ∏ a, v a (movPt S j hj k z a) := by
  rw [Finset.prod_congr rfl fun a _ => scale_movFn_apply S j hj k c₁ c₂ v z a, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle']

theorem isHalf_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (e : AE D) (a : Fin D.R.m ⊕ Fin D.R.m) :
    IsHalf e (movPt S j hj k z a) ↔ IsHalf e (z a) := by
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    rw [movPt_two]
    exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      rw [movPt_one]
      exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · rw [movPt_other S j hj k z a h1' h2']

theorem sum_fn_eq_zero {t : T} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hsupp : ∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (ha : ¬ IsHalf e (z a)) : (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) = 0 := by
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun d hd => ?_
  beta_reduce
  rw [Finset.prod_eq_zero (Finset.mem_univ a), mul_zero]
  rcases a with j | i
  · by_contra hne
    have h := (d.1 j).sb.1 _ hne
    rw [((hsupp d hd).1 j).2.1] at h
    exact ha h
  · by_contra hne
    have h := (d.2 i).sb.1 _ hne
    rw [((hsupp d hd).2 i).2.1] at h
    exact ha h

theorem sum_fn_of_half (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hexp : ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (x j)) →
      (∀ i, IsHalf e (y i)) → (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) =
        ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (h : ∀ a, IsHalf e (z a)) :
    (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w fun j => z (.inl j)) (S.rowAt t w fun i => z (.inr i)) := by
  rw [← hexp (fun j => z (.inl j)) (fun i => z (.inr i)) (fun j => h _) (fun i => h _)]
  refine Finsupp.sum_congr fun d _ => ?_
  rw [Fintype.prod_sum_type, mul_assoc]
  rfl

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inl_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inl i)) = fun i => z (.inl i) :=
  funext fun i => movPt_other S j hj k z _ (by simp) (by simp)

theorem inr_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inr i)) = Function.update (Function.update (fun i => z (.inr i)) ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) := by
  funext i
  let B : Fin D.R.m → Type := fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := by simp
  by_cases h2' : i = ⟨j + 1, hj⟩
  · subst h2'
    exact (movPt_two S j hj k z).trans (Function.update_self (β := B) (⟨j + 1, hj⟩ : Fin D.R.m) _ _).symm
  · by_cases h1' : i = ⟨j, by omega⟩
    · subst h1'
      exact (movPt_one S j hj k z).trans ((Function.update_of_ne (β := B) hne _ _).trans (Function.update_self (β := B) _ _ _)).symm
    · refine (movPt_other S j hj k z _ (fun h => h1' (Sum.inr_injective h)) (fun h => h2' (Sum.inr_injective h))).trans ?_
      symm
      refine (Function.update_of_ne (β := B) (a := i) h2' _ _).trans ?_
      exact Function.update_of_ne (β := B) (a := i) h1' _ _

theorem local_prod (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T} (hμ : L.Is μ₀)
    (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hU : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.grid (j + 1) D.R.m)) (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (c₁ c₂ : ℂ)
    (h1 : W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m))
    (h2 : W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m))
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    c₁ * c₂ * ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))))) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) := by
  have hκ : ∀ w : locPl G t, inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ givenLevel G t w.1 (j + 1, D.R.m) := fun w =>
    Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w
  rw [GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row S hμ hU j hj k hk c₁ c₂ h1 h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [GlobalTheory.RowMoveAt.rowAt_move S hU j hj k w.1 w.2 y]
  exact GlobalTheory.T.termDatum_rowMove_level_edgeFactors S β hμ hq hc hU w j hj _ (hκ w) _ _

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv

theorem sum_prod_scale_movFn_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hc hU hβ hE hv j hj k hk c₁ c₂ h1 h2 z
  obtain ⟨e, -, hsupp, hexp⟩ := hE
  have hL : (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) =
      c₁ * c₂ * τ.sum fun d c => c * ∏ a, fnOf d a (movPt S j hj k z a) := by
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [prod_scale_movFn]
    ring
  rw [hL]
  by_cases hall : ∀ a, IsHalf e (z a)
  · rw [sum_fn_of_half S τ e hexp z hall,
      sum_fn_of_half S τ e hexp _ fun a => (isHalf_movPt S j hj k z e a).2 (hall a), inl_movPt, inr_movPt]
    exact local_prod S β hμ hq hc hU j hj k hk c₁ c₂ h1 h2 (fun i => z (.inl i)) (fun i => z (.inr i))
  · push_neg at hall
    obtain ⟨a, ha⟩ := hall
    rw [sum_fn_eq_zero τ e hsupp z a ha,
      sum_fn_eq_zero τ e hsupp _ a (fun h => ha ((isHalf_movPt S j hj k z e a).1 h)), mul_zero]

end GlobalTheory.RowVertexInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_expansion_functions_rowVertex_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | exact GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionTensorSumInvariantGridRowLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem sum_prod_moveV_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hQ hU hβ hE hv j hj k hk z
  obtain ⟨c₁, c₂, Tm, h1, h2, hT⟩ := GlobalTheory.RowVertexInv.FactorTheta.vecOf_eq_intertwiner S hE hv j hj k hk
  have hB := GlobalTheory.T.sum_prod_expansion_functions_rowVertex_invariant S hμ hq hQ hU hβ hE hv j hj k hk c₁ c₂ h1 h2
  let M : MultilinearMap (RingHom.id ℂ) (fun a : Fin D.R.m ⊕ Fin D.R.m => ↥(⊤ : Submodule ℂ (FactorFn G t a))) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin D.R.m ⊕ Fin D.R.m) ℂ).compLinearMap fun a =>
      (LinearMap.proj (z a)) ∘ₗ Tm a ∘ₗ (⊤ : Submodule ℂ (FactorFn G t a)).subtype
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq (X := fun a => WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (fun a => ⊤) M τ τ (fun d a => ⟨scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a, trivial⟩)
    (fun d a => ⟨fnOf d a, trivial⟩) hB
  simp only [smul_eq_mul] at key
  convert key using 1
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).2]
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).1]

end GlobalTheory.RowVertexInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionTensorSumInvariantGridRowLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionTensorSum_invariant_gridRowLevel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_moveV_eq | exact GlobalTheory.RowVertexInv.sum_prod_moveV_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_moveV_eq <;> assumption)
end
