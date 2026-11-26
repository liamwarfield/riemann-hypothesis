module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SingularWeightMonotoneRegularization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDat

section Halves

variable {D : D7}

theorem hO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) : hO S₁ S₂ z (cA D a • y) = hO S₁ S₂ (a • z) y := by
  unfold hO
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun s _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  ring

theorem symplO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) :
    symplO S₁ S₂ z (cA D a • y) = symplO S₁ S₂ (a • z) y := by
  unfold symplO
  rw [hO_cA_smul]

theorem symplO_zero_right' (S₁ S₂ : HSp D) (z : WO S₁ S₂) : symplO S₁ S₂ z 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_smul_self {m n : ℕ} {b : AE D} (hb : b * b = b) (x : Matrix (Fin m) (Fin n) (AE D)) : IsHalf b (b • x) :=
  fun p q => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hb]

theorem smul_of_isHalf {m n : ℕ} {b : AE D} {x : Matrix (Fin m) (Fin n) (AE D)} (hx : IsHalf b x) : b • x = x :=
  Matrix.ext fun p q => hx p q

theorem smul_eq_zero_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) (c : AF D.host.F) (hc : evFin D.host.F v c = 0) : c • x = 0 := by
  have h0 : c * GlobalTheory.LatVac.liftV v 1 = 0 := GlobalTheory.LatVac.at_liftV v 1 c hc
  ext p q
  rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def]
  have e : algebraMap (AF D.host.F) (AE D) c * x p q =
      b * algebraMap (AF D.host.F) (AE D) (c * GlobalTheory.LatVac.liftV v 1) * x p q := by
    conv_lhs => rw [← hx p q, ← hb]
    rw [map_mul]
    ring
  rw [e, h0, map_zero, mul_zero, zero_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem at_of_mixHalf (e : Num G i j) (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : Pt G i j} (hu : u ∈ mixHalf e b) :
    At (evFin D.host.F v) u := by
  intro c hc
  apply (maps e).injective
  rw [map_smul, map_zero, maps_apply, Prod.smul_mk, smul_eq_zero_of_isHalf v hb hu.1 c hc,
    smul_eq_zero_of_isHalf v hb hu.2 c hc, Prod.mk_zero_zero]

theorem ofMaps_smul_mem (e : Num G i j) {b : AE D} (hb : b * b = b) (x₁ : HomV G i j) (x₂ : HomW G i j) :
    ofMaps e (b • x₁, b • x₂) ∈ mixHalf e b := by
  refine ⟨?_, ?_⟩
  · show IsHalf b (mapV e (ofMaps e _))
    rw [mapV_ofMaps]
    exact isHalf_smul_self hb _
  · show IsHalf b (mapW e (ofMaps e _))
    rw [mapW_ofMaps]
    exact isHalf_smul_self hb _

theorem ofMaps_add_ofMaps (e : Num G i j) (v : Pl D.host.F) {a : AE D}
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) {u : Pt G i j}
    (hu : At (evFin D.host.F v) u) :
    ofMaps e (a • mapV e u, a • mapW e u) + ofMaps e (cA D a • mapV e u, cA D a • mapW e u) = u := by
  have h1 : (1 - GlobalTheory.LatVac.liftV v 1) • u = 0 :=
    hu _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  have hℓu : GlobalTheory.LatVac.liftV v 1 • u = u := by
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  apply (maps e).injective
  refine Prod.ext ?_ ?_
  · show mapV e (_ + _) = mapV e u
    rw [mapV_add, mapV_ofMaps, mapV_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapV_smul, hℓu]
  · show mapW e (_ + _) = mapW e u
    rw [mapW_add, mapW_ofMaps, mapW_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapW_smul, hℓu]

theorem infPart_algebraMap_liftV (v : Pl D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) = 0 :=
  GlobalTheory.LatVac.infPart_pair (GlobalTheory.AdelicU.singleFin v 1) 1

theorem map_infPart_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) : x.map (infPart D) = 0 := by
  ext p q
  rw [Matrix.map_apply, Matrix.zero_apply, ← hx p q, ← hb, map_mul, map_mul, infPart_algebraMap_liftV, mul_zero, zero_mul]

theorem mapV_mem_latV_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid (i + 1) (j + 1))))
    (hT : IsSelfDualC (spV G i j) (G.Λ (.grid i (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapV e x ∈ latV G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.1) fun l hl => ?_
  have hy : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact isHalf_smul_self hcc _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact fun p q => mul_zero _
  have hyl : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact zero_mem _
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.1, symplO_zero_right',
    add_zero] at h
  exact h

theorem mapW_mem_latW_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (spV₁ G i j) (G.Λ (.grid (i + 1) j)))
    (hT : IsSelfDualC (spW G i j) (G.Λ (.grid (i + 1) (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapW e x ∈ latW G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.2) fun l hl => ?_
  have hy : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact fun p q => mul_zero _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact isHalf_smul_self hcc _
  have hyl : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact zero_mem _
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.2, symplO_zero_right',
    zero_add] at h
  exact h

theorem halves_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ (v : Pl D.host.F) (a : AE D), IsSplitIdem D a →
    a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) →
    (∀ u ∈ mixHalf e a, At (evFin D.host.F v) u) ∧ (∀ u ∈ mixHalf e (cA D a), At (evFin D.host.F v) u) ∧
    (∀ u : Pt G i j, At (evFin D.host.F v) u → ∃ x ∈ mixHalf e a, ∃ y ∈ mixHalf e (cA D a), u = x + y) ∧
    (∀ x ∈ mixHalf e a, (∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → W.ψ (sympPt Γ x y) = 1) → x ∈ latPt e v) ∧
    ∀ u : Pt G i j, ofMaps e (a • mapV e u, a • mapW e u) ∈ mixHalf e a ∧
      (∀ y ∈ mixHalf e (cA D a), sympPt Γ u y = sympPt Γ (ofMaps e (a • mapV e u, a • mapW e u)) y) ∧
      (mapV e u ∈ latV G i j → mapW e u ∈ latW G i j → ofMaps e (a • mapV e u, a • mapW e u) ∈ latPt e v) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v a ha hsum
  obtain ⟨haa, hac, -⟩ := ha
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, haa]
  have hca : cA D a * a = 0 := by rw [mul_comm, hac]
  have ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a := by
    rw [← hsum, mul_add, haa, hac, add_zero]
  have hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a := by
    rw [← hsum, mul_add, hca, hcc, zero_add]
  have hfa : finPart D a ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa])
  have hfc : finPart D (cA D a) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
  have hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have hT₁ : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨fun u hu => at_of_mixHalf e v ha1 hu, fun u hu => at_of_mixHalf e v hc1 hu, fun u hu =>
    ⟨_, ofMaps_smul_mem e haa _ _, _, ofMaps_smul_mem e hcc _ _, (ofMaps_add_ofMaps e v hsum hu).symm⟩,
    fun x hx hψ => ⟨at_of_mixHalf e v ha1 hx,
      mapV_mem_latV_of_char e Γ hW hWW W.ψ_std hS hT v ha1 hcc hc1 hfc hx hψ,
      mapW_mem_latW_of_char e Γ hW hWW W.ψ_std hS₁ hT₁ v ha1 hcc hc1 hfc hx hψ⟩, fun u => ?_⟩
  refine ⟨ofMaps_smul_mem e haa _ _, fun y hy => ?_, fun hV hW' => ?_⟩
  · rw [symp_eq e Γ hW hWW, symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, ← symplO_cA_smul, ← symplO_cA_smul,
      smul_of_isHalf hy.1, smul_of_isHalf hy.2]
  · refine ⟨at_of_mixHalf e v ha1 (ofMaps_smul_mem e haa _ _), ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hV
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hW'

end Halves

end GlobalTheory.BigDat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThreeRLtGOfParams
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.BigOn

theorem three_r_lt_g_of_params (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (k : Fin 2) :
    3 * D.R.r < D.host.g k := by
  obtain ⟨Y, hY1, -, -, hY4⟩ := P.g_Y
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb2 : 2 ≤ L.sc.b := by
    unfold Scale.b
    have := Real.add_one_le_exp L.sc.L
    linarith
  have hmk := D.R.m_add_three_le_k
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hkb : (2 : ℝ) * D.R.k ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have hpow : (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 = ((D.R.k : ℝ) * L.sc.b) ^ 8 := by ring
  have h7 : (2 : ℝ) ^ 7 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
    pow_le_pow_left₀ (by norm_num) (by nlinarith) 7
  have hbig : (6 : ℝ) * D.R.k < ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
    rw [← hpow]
    have : (2 : ℝ) * D.R.k * 2 ^ 7 ≤ (D.R.k : ℝ) * L.sc.b * ((D.R.k : ℝ) * L.sc.b) ^ 7 :=
      mul_le_mul hkb h7 (by norm_num) (by positivity)
    nlinarith
  have hr' : ((3 * D.R.r : ℕ) : ℝ) ≤ 6 * D.R.k := by
    have : 3 * D.R.r ≤ 6 * D.R.k := by omega
    exact_mod_cast this
  have hg : ((3 * D.R.r : ℕ) : ℝ) < (D.host.g k : ℝ) := by
    linarith [(hY4 k).1]
  exact_mod_cast hg

end GlobalTheory.BigOn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAdjointAtLiftEqLowestKTypeRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAdjointAtLiftEqLowestKTypeRestriction
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFireLift

theorem lift_postOn {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (X : MMap M) :
    PiTensorProduct.lift (postOn M L X) = L ∘ₗ PiTensorProduct.lift X := by
  ext v
  simp [postOn]

theorem thetaFireL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireL (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hLev hGrp hMod hThP hv0 IL μ hμ i x
  have hfm : ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) ∈ LinearMap.range (R.extV i (tupT μ)) ⊓
      RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false)))
        (levChi _ (R.βV i) (RecTie.datVP R i (tupT μ) (R.levR F false))) := (IL.jMt μ hμ i x).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm
      ⟨((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : R.extV i (tupT μ) y = ((IL.jMt μ hμ i x).1 : GA D (Vc D i) → (R.cV i).W) := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (hinj i (tupT μ))).apply_symm_apply _)
  have hM := GlobalTheory.T.thetaLift_mem_multiplicitySpace_baseLevel R F hLev hMod hThP hv0 false i (tupT μ) y (by rw [hyf]; exact hfm.2)
  refine ⟨PiTensorProduct.lift (R.thF i (tupT μ) y), ?_, ?_, ?_⟩
  · exact Submodule.mem_map_of_mem hM
  · rw [← hy]; rfl
  · have hG : R.eWf i (sg0 D A) ∘ₗ PiTensorProduct.lift (R.thF i (tupT μ) y) ∈
        (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).map
          (PiTensorProduct.lift : MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap := by
      rw [← lift_postOn]
      exact Submodule.mem_map_of_mem (GlobalTheory.GoodProjLevel.proj_mem_good R hLev hGrp.record hv0 i _ _ hM)
    exact hG

end GlobalTheory.ThetaFireLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAdjointAtLiftEqLowestKTypeRestrictionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaAdjoint_at_lift_eq_lowestKType_restriction : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ IL : RecTie.LiftIds (RecTie.toLiftReal R F tupT hm hTop hinj), RecTie.ThetaFireL (RecTie.toLiftReal R F tupT hm hTop hinj) IL := by
  first | exact @GlobalTheory.ThetaFireLift.thetaFireL | exact GlobalTheory.ThetaFireLift.thetaFireL | (intros; apply GlobalTheory.ThetaFireLift.thetaFireL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPart
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
open GlobalTheory.CharRealise

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)


set_option maxHeartbeats 4000000 in
theorem iw_split_eq (j : Fin D.R.m) (t : p.P.A3.fam3.base3.Tup) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (p.S false).Iw j t w = (S2 p).Iw j t w := by
  show ((p.R.toCx3 p.F).data p.F.cr false).Iw j t w = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl


set_option maxHeartbeats 4000000 in
theorem d_split_eq : (p.S false).D = (S2 p).D := by
  show ((p.R.toCx3 p.F).data p.F.cr false).D = _
  rw [toCx3_eq_one p.R p.F p.phsOne]
  rfl


set_option maxHeartbeats 4000000 in
theorem onWith_of_split : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), ∀ (C CH : ℝ) (err : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ), ONwith (S2 p) ((R2 p).num (F2 p) C CH) err → ONwith (p.S false) (p.N C CH) err ∧ (p.S false).D = (S2 p).D := by
  intro D L hT Gi Gl Kc Y cX ex Csz p C CH err h
  obtain ⟨h1, h2, h3⟩ := h
  have eD := d_split_eq p
  refine ⟨⟨fun w hw => ?_, fun w hw j => h2 w hw j, fun j => h3 j⟩, eD⟩
  have := h1 w hw
  simp only [iw_split_eq p, eD]
  exact this

end GlobalTheory.BigOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPartStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onClauses_with_error_of_splitPart : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), ∀ (C CH : ℝ) (err : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ), ONwith (S2 p) ((R2 p).num (F2 p) C CH) err → ONwith (p.S false) (p.N C CH) err ∧ (p.S false).D = (S2 p).D := by
  first | exact @GlobalTheory.BigOn.onWith_of_split | exact GlobalTheory.BigOn.onWith_of_split | (intros; apply GlobalTheory.BigOn.onWith_of_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleReadBaseTupleEqFamily
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.TwistBoundAtPlace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem tupleRead_baseTuple_eq_family : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 :=
  p.charW.base.lev.xi_inj (by rw [p.tupXi D.what₂.mu0 (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one, p.charW.base.lev.xi_base])

theorem twistedAt_of_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : TwistedAt D (D.plEq.symm v) := by
  intro he
  apply p.charW.tup.mu_ne v hv
  have := p.tupAt (D.plEq.symm v)
  rw [he, tupleRead_baseTuple_eq_family, Equiv.apply_symm_apply] at this
  exact this.symm

theorem conj_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : Formalism.DivisionValues.conjPl v ∈ p.R.twPl := by
  by_contra h
  have := p.charW.tup.mu_off _ h
  rw [p.charW.tup.mu_conj] at this
  exact p.charW.tup.mu_ne v hv this

end Point


set_option maxHeartbeats 1600000 in
theorem hasTwistBound_at {eps : ℝ} {Fm : FamP eps} {x : ℝ} {hx : Fm.x1 < x} {i : Fm.Ix x} (p : Pt Fm x hx i)
    {r : TwoRuns p.T p.P.Gp} {c : OnConst} {O : Obj p c} (hR : RecAt p (Fm.parT x hx i) r O)
    (hE : ∀ v ∈ p.R.twPl, ∀ j, GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0
      (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v))
    (hS : LeafSup O) (hK : GlobalTheory.TraceClassRank.RankAtPlaces O)
    {N0 : (Fm.D x i).ntw.Tw → ℕ} {S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)}
    (hG : Formalism.MainNotions.TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩) : HasTwistBound O := by
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hR.1.tied
  have tied : ∀ v ∈ p.R.twPl, TwistedAt (Fm.D x i) ((Fm.D x i).plEq.symm v) ∧
      ∀ j, GlobalTheory.TwistIndex.TiedAt p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) O v j (id j) := fun v hv =>
    ⟨twistedAt_of_mem p hv, fun j => ⟨(r.used v).full, p.alg, R2 p, p.κ, p.v₀, (hR.1.ok.laws v).p, fw2 p, hinj,
      (Fm.ex x hx i).errX, ownAt (Fm.D x i) v, _, _, _, z j, act j, GlobalTheory.OntoChain.mirIncl (R2 p), r.lev j, (F2 p).P0, (F2 p).ψ0⁻¹, 1, y v j,
      (ht v j).1, hE v hv j⟩⟩
  exact GlobalTheory.TwistIndex.exists_leafTW1_of_twGoodAt p.P.A3.A (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩ hG O id
    Function.injective_id (GlobalTheory.TwistIndex.goodPartLattice_of_leafSup hS)
    (fun w hw => ⟨fun j => ((hK w hw).1 j).2.1, fun j => ((hK w hw).2 j).2.1⟩)
    (fun w hw => ⟨tied w hw, tied _ (conj_mem p hw)⟩)

end GlobalTheory.BigOn.TwistBoundAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserLeftPreservesVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserLeftPreservesVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VacTransportLeft

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β]

theorem hTens_eq_left (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ j, ∑ l, JB j l * (xᵀ * JA * y.map c) j l := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (γ := β)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem symp_mul_left [DecidableEq α] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (g : Matrix α α A)
    (hg : gᵀ * JA * g.map c = JA) (x y : Matrix α β A) :
    symp c ξ JA JB (g * x) (g * y) = symp c ξ JA JB x y := by
  have e : (g * x)ᵀ * JA * (g * y).map c = xᵀ * JA * y.map c := by
    have hm : (g * y).map c = g.map c * y.map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul]
    calc xᵀ * gᵀ * JA * (g.map c * y.map c) = xᵀ * (gᵀ * JA * g.map c) * y.map c := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_left, hTens_eq_left, e]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem vecMulVec_mem_left {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fin d → E} (hy : y ∈ W.L)
    {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i)) ∈ latAtV X W v := by
  let f : (Fin n → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i))
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun z z' => by ext i j; simp [Matrix.vecMulVec_apply, add_mul] }
  have : GlobalTheory.InertSph.latAt X v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hz

theorem inv_mul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {k : UA σ X.J}
    (hk : k ∈ GlobalTheory.InertSph.KAt σ X v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    mat k⁻¹ * γ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => mat k⁻¹ * γ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.mul_add] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt X v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    have e : mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) =
        Matrix.vecMulVec (mat k⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (x i)))
          (fun j => inclR (F := F) (AF F) (y j)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_left X W v hy (hk.2 _ hz).2
  exact this hγ

theorem transport_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (k, 1)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr
  have etens : ∀ (c : ℂ) (f : (Fin a × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hγ' : mat k⁻¹ * γ ∈ latAtV G.V G.W v := inv_mul_mem G.V G.W v hk hγ
  have hback : actAB (cA σ) (k, (1 : UA σ G.W.J)) (mat k⁻¹ * γ) = γ := by
    change mat k * (mat k⁻¹ * γ) * (1 : Matrix _ _ _)ᵀ = γ
    have e : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
    rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]
  have hsy := symp_mul_left (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹)
    (k⁻¹).2 γ γ
  have h1 := hS.impl (k, 1) (mat k⁻¹ * γ) _ hr'.2
  rw [hback, hfix _ hγ' r hr', hsy, etens, map_smul, hact r hr'] at h1
  rw [← h1, etens]

end GlobalTheory.VacTransportLeft

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserLeftPreservesVacuumStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_latticeStabiliser_left_preserves_vacuumType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (k, 1)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.VacTransportLeft.transport_left | exact GlobalTheory.VacTransportLeft.transport_left | (intros; apply GlobalTheory.VacTransportLeft.transport_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.SchrFixUniq

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

theorem schr_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w : (κ → R) × (κ → R)) (a : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (a • φ) = a • schr ψ w φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem schr_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x
  simp [schr]

theorem char_ne_zero {R : Type} [CommRing R] (ψ : AddChar R ℂ) (x : R) : ψ x ≠ 0 := by
  intro hx
  have h2 : ψ (x + -x) = ψ x * ψ (-x) := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at h2
  exact one_ne_zero h2

theorem common_eigen {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (S : Set ((κ → R) × (κ → R))) (f g : (κ → R) → ℂ) (hf : ∀ s ∈ S, schr ψ s f = f)
    (hg : ∀ s ∈ S, schr ψ s g = g) (l : (κ → R) × (κ → R)) (hl : l ∈ AddSubgroup.closure S) :
    ∃ χ : ℂ, χ ≠ 0 ∧ schr ψ l f = χ • f ∧ schr ψ l g = χ • g := by
  induction hl using AddSubgroup.closure_induction with
  | mem s hs => exact ⟨1, one_ne_zero, by rw [hf s hs, one_smul], by rw [hg s hs, one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [schr_zero', one_smul], by rw [schr_zero', one_smul]⟩
  | add w w' _ _ h h' =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    obtain ⟨χ', hχ', h1', h2'⟩ := h'
    have hz := char_ne_zero ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2))
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ w' φ = χ' • φ →
        schr ψ (w + w') φ = ((ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)))⁻¹ * (χ' * χ)) • φ := by
      intro φ a b
      have e := schr_comp ψ w w' φ
      rw [b, schr_smul', a, smul_smul] at e
      rw [mul_smul, e, smul_smul, inv_mul_cancel₀ hz, one_smul]
    exact ⟨_, mul_ne_zero (inv_ne_zero hz) (mul_ne_zero hχ' hχ), key f h1 h1', key g h2 h2'⟩
  | neg w _ h =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ (-w) φ = χ⁻¹ • φ := by
      intro φ a
      have e := schr_comp ψ (-w) w φ
      have e0 : ⅟(2 : R) * ((-w).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (-w).2) = 0 := by
        simp
      rw [a, schr_smul', neg_add_cancel, schr_zero', e0, AddChar.map_zero_eq_one, one_smul] at e
      conv_rhs => rw [← e]
      rw [smul_smul, inv_mul_cancel₀ hχ, one_smul]
    exact ⟨_, inv_ne_zero hχ, key f h1, key g h2⟩

theorem exists_shift {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψk : AddChar (Fv F v) ℂ)
    (hc : Continuous ψk) (h1 : ψk ≠ 1) : ∃ a : Fv F v, a ≠ 0 ∧ ∀ x : Fv F v,
      (∀ y ∈ v.adicCompletionIntegers F, ψk (a * (x * y)) = 1) ↔ x ∈ v.adicCompletionIntegers F := by
  have hne : ∃ t, ψk t ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (AddChar.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued ψk hc hne
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have ha0 : (Valued.v a : WithZero (Multiplicative ℤ)) ≠ 0 := by rw [ha]; exact WithZero.exp_ne_zero
  refine ⟨a, by simpa using ha0, fun x => ?_⟩
  have h := hn (a * x)
  rw [← ha, map_mul, mul_le_iff_le_one_right (zero_lt_iff.2 ha0)] at h
  simpa only [HeightOneSpectrum.mem_adicCompletionIntegers, mul_assoc] using h

theorem exists_pair {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψk : AddChar (Fv F v) ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v) (hc0 : c ≠ 0)
    (hself : ∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1)
    (hbd : ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F)
    (η : κ → Fv F v) (hη : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) : ∃ y, (η, y) ∈ Λ := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_shift v ψk hc h1
  let Λ' : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := {w | (w.1, a • w.2) ∈ Λ}
      add_mem' := fun {x y} hx hy => by
        have := Λ.add_mem hx hy
        simpa [smul_add] using this
      zero_mem' := by
        show ((0 : κ → Fv F v), a • (0 : κ → Fv F v)) ∈ Λ
        rw [smul_zero]
        exact Λ.zero_mem
      neg_mem' := fun {x} hx => by
        have := Λ.neg_mem hx
        simpa using this }
  have hΛ' : ∀ w, w ∈ Λ' ↔ (w.1, a • w.2) ∈ Λ := fun _ => Iff.rfl
  have hbd' : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ', ∀ i,
      c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by
    rcases (v.adicCompletionIntegers F).mem_or_inv_mem a with h | h
    · refine ⟨a * c, mul_ne_zero ha hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨by rw [mul_assoc]; exact mul_mem h p, ?_⟩
      convert q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · refine ⟨c, hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨p, ?_⟩
      convert mul_mem h q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  obtain ⟨c', hc', hb'⟩ := hbd'
  have hs' : ∀ w, w ∈ Λ' ↔ ∀ l ∈ Λ', (ψk.mulShift a) (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
    intro w
    rw [hΛ', hself]
    constructor
    · intro h l hl
      have := h _ ((hΛ' l).1 hl)
      simp only [dotProduct_smul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_sub]
      exact this
    · intro h l hl
      have := h (l.1, a⁻¹ • l.2) (by rw [hΛ']; simpa [smul_smul, mul_inv_cancel₀ ha] using hl)
      rw [AddChar.mulShift_apply, mul_sub] at this
      simp only [dotProduct_smul, smul_eq_mul] at this ⊢
      rwa [mul_inv_cancel_left₀ ha] at this
  obtain ⟨y, hy⟩ := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (ψk.mulShift a) Λ' c' hc'
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x) hs' hb' η (fun b hb => by
      have := hη _ ((hΛ' _).1 hb)
      rwa [dotProduct_smul, smul_eq_mul, ← AddChar.mulShift_apply] at this)
  exact ⟨_, (hΛ' _).1 hy⟩

theorem proportional_of_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ (S : Set ((κ → Fv F v) × (κ → Fv F v))) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v),
    Λ ≤ AddSubgroup.closure S → c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ f g : (κ → Fv F v) → ℂ, (∀ s ∈ S, schr ψk s f = f) → (∀ s ∈ S, schr ψk s g = g) → f ≠ 0 → ∃ a : ℂ, g = a • f := by
  intro F _ _ v κ _ ψk hc h1 S Λ c hS hc0 hself hbd f g hf hg hf0
  classical
  have hall : ∀ l, ∃ χ : ℂ, l ∈ Λ → schr ψk l f = χ • f ∧ schr ψk l g = χ • g := by
    intro l
    by_cases hl : l ∈ Λ
    · obtain ⟨χ, -, h⟩ := common_eigen ψk S f g hf hg l (hS hl)
      exact ⟨χ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose χ hχ using hall
  refine GlobalTheory.heisenbergEigen_proportional ψk Λ χ f g (fun l hl ξ => ?_) (fun l hl ξ => ?_) hf0
    (exists_pair v ψk hc h1 Λ c hc0 hself hbd)
  · have := congrFun (hχ l hl).1 ξ
    rw [← invOf_eq_inv]
    exact this
  · have := congrFun (hχ l hl).2 ξ
    rw [← invOf_eq_inv]
    exact this

end GlobalTheory.SchrFixUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ (S : Set ((κ → Fv F v) × (κ → Fv F v))) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v),
    Λ ≤ AddSubgroup.closure S → c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ f g : (κ → Fv F v) → ℂ, (∀ s ∈ S, schr ψk s f = f) → (∀ s ∈ S, schr ψk s g = g) → f ≠ 0 → ∃ a : ℂ, g = a • f := by
  first | exact @GlobalTheory.SchrFixUniq.proportional_of_fixed | exact GlobalTheory.SchrFixUniq.proportional_of_fixed | (intros; apply GlobalTheory.SchrFixUniq.proportional_of_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSphericalStabilizerPreservesLattice
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertSphStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma incM_vecMulVec {n d : ℕ} (x : Fin n → E) (y : Fin d → E) :
    incM F (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (fun j => inclR (F := F) (AF F) (y j)) := by
  ext i j
  simp [incM, Matrix.vecMulVec_apply, map_mul]

lemma smul_vecMulVec {n d : ℕ} (a : AF F) (p : Fin n → AE F E) (q : Fin d → AE F E) :
    a • Matrix.vecMulVec p q = Matrix.vecMulVec p (a • q) := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_smul_comm]

lemma vecMulVec_mul_transpose {n d : ℕ} (p : Fin n → AE F E) (q : Fin d → AE F E)
    (M : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d → AE F E} (hq : q ∈ GlobalTheory.InertSph.latAt W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v := by
  induction hq using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    rw [incM_vecMulVec, smul_vecMulVec]
  | zero =>
    have h0 : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [h0]; exact (latAtV X W v).zero_mem
  | add z z' _ _ h h' =>
    rw [Matrix.vecMulVec_add]
    exact (latAtV X W v).add_mem h h'
  | neg z _ h =>
    rw [Matrix.vecMulVec_neg]
    exact (latAtV X W v).neg_mem h

end GlobalTheory.InertSphStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodLatticeNeBot
set_option synthInstance.maxHeartbeats 400000
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CovTop.ne_bot_of_isLattice_coords {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (M : Submodule O V) {d : ℕ} (hd : 0 < d) (b : Fin d → V) (hb : LinearIndependent K b)
    (hM : Submodule.IsFullLattice K (M.comap ((Fintype.linearCombination K b).restrictScalars O))) : M ≠ ⊥ := by
  rintro rfl
  have hinj : Function.Injective (Fintype.linearCombination K b) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by rwa [Fintype.linearCombination_apply] at hc))
  have h0 : (⊥ : Submodule O V).comap ((Fintype.linearCombination K b).restrictScalars O) = ⊥ := by
    rw [Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.2 hinj
  have h := Submodule.IsFullLattice.span_eq_top (self := hM)
  rw [h0] at h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simp at h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.ClassCover

variable {L : Type} [Field L] [NumberField L]

def toIdeles : (FiniteAdeleRing (𝓞 L) L)ˣ →* Neutral.B1.Ideles L :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem eq_diag_mul_of_classOf (y : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles y) = 1) :
    ∃ (k : Lˣ) (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((u : FiniteAdeleRing (𝓞 L) L) P) = 1) ∧
      y = Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom k * u := by
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 L) L).2, ((u⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2, ?_, ?_⟩,
    fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((toIdeles y : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 =
        ((Neutral.B1.diagUnits L k * u : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 := by rw [he]
    exact h2

end GlobalTheory.ClassCover
end
end
