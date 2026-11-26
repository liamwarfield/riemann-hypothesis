module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.FlatVal

variable {D : D7} {L : SizeData₂ D}

theorem isComplexData {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) {Y : Deep T.toCore j} {e : ℕ} {o : ℝ}
    (hG : Y.Good e o) : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict := by
  have hV : Formalism.L2.Pj.FinVol (D.sp.W j) := by
    have h := hT.finVol j hj _ T.good_σ₀
    rwa [hT.spaceW j hj _ T.good_σ₀] at h
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hG.lev.1.2.1, hT.pins.2.1.1]
  refine ⟨hG.lev.2, fun σ hσ => ⟨hG.unf σ hσ, ?_, hV, hG.xiAbs σ hσ⟩⟩
  obtain ⟨th, hr, h1, h2⟩ := hG.dictU σ hσ
  exact ⟨Y.Kf, th, hr, hM ▸ hG.levelK, h1, h2⟩

theorem abs_log_sub_lrd_le {PP A M : ℝ} (h : HostNum D L PP A M) :
    |Real.log (D.host.d : ℝ) - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E| ≤ 3 * L.sc.L := by
  have hL := h.big.2.1
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8
  have h0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := by rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
    rw [rootDiscr_def, Int.cast_abs, Real.log_rpow (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero _))), h.deg]; push_cast; ring
  have h2 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E := by rw [h1]; positivity
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
    rw [h1, div_le_iff₀ (by linarith)]; linarith [h.disc]
  have h4 := Real.log_natCast_nonneg D.host.d
  exact abs_le.2 ⟨by linarith, by linarith [h.logd]⟩

theorem log_level_le (P : ParameterChoice' D L) {PP A M : ℝ} (h : HostNum D L PP A M) :
    Real.log ((LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 : ℕ) : ℝ) ≤ 40 * L.sc.L := by
  have hL := h.big.2.1
  have hc0 : (LevelStarExponents.condE D : ℝ) ≠ 0 := by
    have := (GlobalTheory.BadLog.log_level_le P).1
    exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul this)
  have a0 : (D.host.g 0 : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have a1 : (D.host.g 1 : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  have hc := (Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.log_cond_le P).1
  have l15 : Real.log 15 ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  push_cast
  rw [Real.log_mul (mul_ne_zero hc0 (mul_ne_zero a0 a1)) (by norm_num), Real.log_mul hc0 (mul_ne_zero a0 a1),
    Real.log_mul a0 a1]
  linarith [h.logg 0, h.logg 1]

end GlobalTheory.CovTop.FlatVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem eq_refl_of_isometry_congMod : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) →
    ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  intro X _ _ _ β hpos e he N hN hc
  choose u hu using hc
  have hQ0 : ∀ x, 0 ≤ β x x := fun x => by
    by_cases h : x = 0
    · simp [h]
    · exact (hpos x h).le
  have hdec : ∀ x, x ≠ 0 → β (u x) (u x) < β x x := by
    intro x hx
    have h1 : 0 ≤ β (e x + x) (e x + x) := hQ0 _
    have h2 : β (e x - x) (e x - x) = (N : ℤ) * ((N : ℤ) * β (u x) (u x)) := by
      rw [show e x - x = N • u x by rw [hu x]; abel]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, he x x] at h1 h2
    have hc := hpos x hx
    have hd := hQ0 (u x)
    have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul hN' hN' (by norm_num) (by omega)) hd]
  have hnil : ∀ n : ℕ, ∀ x, (β x x).toNat = n → ∃ k, u^[k] x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn
      by_cases hx : x = 0
      · exact ⟨0, by simpa using hx⟩
      · have hlt := hdec x hx
        have hd := hQ0 (u x)
        obtain ⟨k, hk⟩ := ih (β (u x) (u x)).toNat (by omega) (u x) rfl
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
  ext y
  by_contra hne
  have huy : u y ≠ 0 := fun h => hne (by rw [hu y, h]; simp)
  classical
  have hex : ∃ k, u^[k] y = 0 := hnil _ y rfl
  have hk : u^[Nat.find hex] y = 0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, u^[j] y ≠ 0 := fun j hj => Nat.find_min hex hj
  have hy0 : y ≠ 0 := fun h => hne (by simp [h])
  have hk2 : 2 ≤ Nat.find hex := by
    by_contra h
    interval_cases h' : Nat.find hex
    · exact hy0 (by simpa using hk)
    · exact huy (by simpa using hk)
  have hux : u (u^[Nat.find hex - 2] y) ≠ 0 := by
    rw [← Function.iterate_succ_apply' u]
    exact hmin _ (by omega)
  have huux : u (u (u^[Nat.find hex - 2] y)) = 0 := by
    rw [← Function.iterate_succ_apply' u, ← Function.iterate_succ_apply' u]
    rw [show (Nat.find hex - 2).succ.succ = Nat.find hex by omega]
    exact hk
  set x := u^[Nat.find hex - 2] y
  have key := he x (u x)
  rw [hu x, hu (u x), huux] at key
  simp only [smul_zero, add_zero, map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at key
  have hp := hpos (u x) hux
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith [mul_pos hN0 hp]

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThreeStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_eq_refl_of_congr_mod_ge_three : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) → ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  first | exact @GlobalTheory.Poinc.eq_refl_of_isometry_congMod | exact GlobalTheory.Poinc.eq_refl_of_isometry_congMod | (intros; apply GlobalTheory.Poinc.eq_refl_of_isometry_congMod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open TopForm

section Pair

variable {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}

def topPair (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) : Forms α n →ₗ[A] A :=
  letI := α.toAlgebra
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap
    (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)))

end Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev PairIx (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) : Type :=
  Σ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, Fin (Dw.mult τ.1) × Fin (Dw.mult ((starRingEnd ℂ).comp τ.1))

def symPair {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : PairIx H Dw) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b =>
    (if a = e ⟨P.1.1, P.2.1⟩ ∧ b = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ then 1 else 0) +
      (if a = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ b = e ⟨P.1.1, P.2.1⟩ then 1 else 0)

abbrev genPt (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z :=
  (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))

abbrev GenDer (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Type :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField

def GenKS (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left))
    (D : Fin Dw.dim → GenDer TF Z) : Prop :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (ε : Fin Dw.dim ≃ PairIx H Dw)
    (Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U),
    spMap ρ ≫ LogKS.chart U = genPt TF Z ≫ (barComp TF.Y Z).ι ∧
    (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    (∀ τ i, w τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧
    (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (Dl j).1 (symPair e (ε j))) ∧
    ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r)

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

open TopForm

theorem topPair_dForm {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) (f : Fin n → A) :
    topPair α D (dForm α f) = (Matrix.of fun i j => (letI := α.toAlgebra; (D j : Derivation k A A)) (f i)).det := by
  letI := α.toAlgebra
  rw [dForm_eq, topPair, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  change Matrix.det (Matrix.of _) = _
  congr 1
  ext i j
  exact Derivation.liftKaehlerDifferential_comp_D (D j) (f i)

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.QWDom

open Matrix in
theorem exists_pos_posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (A - c • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ _)⟩
  refine ⟨c, hc, ?_⟩
  have hs := hA.1.spectral_theorem
  have h1 : c • (1 : Matrix n n ℝ) = Unitary.conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary (c • 1) := by
    rw [map_smul, map_one]
  rw [h1]
  conv => arg 1; arg 1; rw [hs]
  rw [← map_sub, Unitary.conjStarAlgAut_apply]
  rw [Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  rw [smul_one_eq_diagonal, diagonal_sub]
  exact PosSemidef.diagonal fun i => by simpa using hle i

open Matrix in
theorem gram_nonneg_int {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (z : Fin s → ℤ) : 0 ≤ ∑ u, ∑ v, z u * β (y u) (y v) * z v := by
  have h := hβ (∑ u, z u • y u)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
  have e : ∑ u, ∑ v, z u * β (y u) (y v) * z v = ∑ x, z x * ∑ x1, z x1 * β (y x1) (y x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [e]; exact h

open Matrix in
theorem gram_nonneg_rat {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (q : Fin s → ℚ) :
    0 ≤ ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
  set D : ℕ := ∏ u, (q u).den with hD
  have hDpos : (0 : ℝ) < D := by
    have : 0 < D := Finset.prod_pos fun u _ => (q u).den_pos
    exact_mod_cast this
  have hz : ∀ u, ∃ z : ℤ, (q u : ℝ) * D = z := by
    intro u
    obtain ⟨k, hk⟩ : (q u).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ u)
    refine ⟨(q u).num * k, ?_⟩
    rw [hk]
    have hq : (q u : ℝ) = (q u).num / (q u).den := by exact_mod_cast (Rat.num_div_den (q u)).symm
    have hd : ((q u).den : ℝ) ≠ 0 := by exact_mod_cast (q u).den_nz
    rw [hq]; push_cast; field_simp
  choose z hz using hz
  have h0 : (0 : ℝ) ≤ ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) := by
    exact_mod_cast gram_nonneg_int β hβ y z
  have : ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) =
      (D : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
    simp only [← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [this] at h0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h0

open Matrix in
theorem gram_posSemidef {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hsym : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) :
    (Matrix.of fun u v => (β (y u) (y v) : ℝ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext u v
    simp [conjTranspose_apply, hsym (y u) (y v)]
  · have hcl : IsClosed {x : Fin s → ℝ | 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v} :=
      isClosed_le continuous_const (by fun_prop)
    have hx : 0 ≤ ∑ u, ∑ v, x u * (β (y u) (y v) : ℝ) * x v :=
      (DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl
        fun q => gram_nonneg_rat β hβ y q
    simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
    refine le_of_le_of_eq hx (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_)
    ring

open Matrix in
theorem qW_ge : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  intro s W hW
  obtain ⟨c, hc, hP⟩ := exists_pos_posSemidef_sub_smul_one hW
  refine ⟨c / 2, by positivity, fun X _ β hsym hβ y => ?_⟩
  have hM := gram_posSemidef β hsym hβ y
  have ht := GlobalTheory.trace_mul_nonneg_of_posSemidef hP hM
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, sub_nonneg] at ht
  simp only [trace, diag, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, transpose_apply, Matrix.of_apply,
    smul_eq_mul] at ht
  have e : ∑ u, ∑ v, ((W u v + W v u : ℤ) : ℝ) * (β (y v) (y u) : ℝ) = 2 * (qW W β y : ℝ) := by
    simp only [qW, Int.cast_sum, Int.cast_mul, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [two_mul]
    congr 1
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [hsym]
    · rw [Finset.sum_comm]
  push_cast at ht e ⊢
  linarith

end GlobalTheory.Poinc.QWDom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonalStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedLatticeQuadraticSum_ge_diagonal : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  first | exact @GlobalTheory.Poinc.QWDom.qW_ge | exact GlobalTheory.Poinc.QWDom.qW_ge | (intros; apply GlobalTheory.Poinc.QWDom.qW_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.DimAtOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_dimAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := by
  intro D i τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt
  have h := Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ (GlobalTheory.AdelicScalar.sig_add i τ)
  have h1 : (1 : ℚ) ≤ dimK _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) τ) :=
    one_le_mul_of_one_le_of_one_le (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.1) (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.2.1)
  exact_mod_cast h1

end GlobalTheory.DimAtOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT

noncomputable section

namespace GlobalTheory.DefHalf

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

def sigC (p : PtAt ex Csz) : p.T.Q.c.F →+* ℂ := D.what₂.embLL.comp (algebraMap p.T.Q.c.F D.what₂.LL)

abbrev CF (p : PtAt ex Csz) (i : Fin D.R.m) : Submodule p.T.Q.c.F (p.T.R ((i : ℕ) + 1)) :=
  p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n

end GlobalTheory.DefHalf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

theorem isProjOver_locallyOfFiniteType : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsProjOver s → LocallyOfFiniteType s := by
  rintro R _ X s ⟨N, i, hi, rfl⟩
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFiniteType_of_isProjOver : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → LocallyOfFiniteType s := by
  first | exact @GlobalTheory.isProjOver_locallyOfFiniteType | exact GlobalTheory.isProjOver_locallyOfFiniteType | (intros; apply GlobalTheory.isProjOver_locallyOfFiniteType <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

variable {S : Scheme.{0}}

def SiegKerBy {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) (d : ℕ) : Prop :=
  Out.RelAmple c.A c.diag ∧
    ∀ (T : Over S) (x : T ⟶ c.A),
      (∃ t : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, t.IsGen) → x ^ d = 1

def IsSympLev {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type} [CommRing B] (ζ : B)
    (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
      (z : k) = β ζ →
      (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
      (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
      ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
        (unitOn (z ^ (2 * omegaStd a b)))

theorem SiegPre.isSympLev {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) :
    IsSympLev c.P h M ζ s c.lev :=
  ⟨c.lev_add, c.lev_tors, c.geom⟩

def SDRep (h M d : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp (cycAway M)) (u : SiegPre h M (zetaAway M) s),
    SiegKerBy u d ∧ IsUnit ((d : ℕ) : Γ(X, ⊤)) ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t),
      IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃! f : S ⟶ X, f ≫ s = t ∧ SiegPB c u f

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def HasLevelStructureOfLevel (b : Base D R) (N h M : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (t₁ : S ⟶ Sp (cycAway M)) (o : Obj b N t)
      (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)), IsSympLev o.P h M (zetaAway M) t₁ l →
      ∃! f : S ⟶ X, f ≫ s = t ∧ f ≫ s₁ = t₁ ∧ ∃ m : ObjMap o u f, ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left

theorem Datum.two_le_finrank_La {p : ℕ} [Fact p.Prime] (D : Datum p) : 2 ≤ Module.finrank ℤ D.La := by
  haveI := D.freeLa
  haveI := D.finLa
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hpos : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  by_contra hlt
  have h1 : Module.finrank ℤ D.La = 1 := by omega
  let bs := Module.finBasisOfFinrankEq ℤ D.La h1
  have hzero : ∀ x y : D.La, D.EF x y = 0 := by
    intro x y
    have hx : x = bs.repr x 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr x]
      simp
    have hy : y = bs.repr y 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr y]
      simp
    rw [hx, hy, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, D.alt, smul_zero, smul_zero]
  have hsub : ∀ x : D.La, x = 0 := by
    intro x
    apply D.nondeg
    ext y
    simp [hzero]
  have : Module.finrank ℤ D.La = 0 := by
    haveI : Subsingleton D.La := ⟨fun a b => by rw [hsub a, hsub b]⟩
    exact Module.finrank_zero_of_subsingleton
  omega

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def offCM (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) : ℤ :=
  if τ (H.rt : E) = H.rt0 then 0 else if conjEmb τ (H.rt : E) = H.rt0 then 1 else 0

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exOf_hodgeWt (Dw : Datum H) :
    GlobalTheory.AllWt.exOf Dw (hodgeWt Dw) 0 = fun ix => ix.elim 0 fun x => offCM H x.1 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · simp only [GlobalTheory.AllWt.exOf, exZ, GlobalTheory.AllWt.wtOf, Option.elim, offCM, hodgeWt, CompHt.barWt]
    by_cases h : τ (H.rt : E) = H.rt0
    · simp only [dif_pos h, if_pos h]
      split_ifs <;> omega
    · have hm : Dw.mult τ = Dw.q := by simp [Datum.mult, h]
      have hi : (i : ℕ) < Dw.q := lt_of_lt_of_eq i.2 hm
      simp only [dif_neg h, if_neg h]
      by_cases h' : conjEmb τ (H.rt : E) = H.rt0
      · simp only [dif_pos h', if_pos h', dif_pos hi]
        split_ifs <;> omega
      · simp only [dif_neg h', if_neg h']

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def DetEqns (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (φ₀ : c.F →+* (X₀ TF.Y Z).functionField)
    (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι))
    (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)) : Prop :=
  ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x)
    (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι))
    (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField)
    (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ),
    (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧
    (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧
    (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
      (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)
      (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k)
      (A τ i) (f₀.v τ i)) ∧
    D.IsEqn x (∏ τ, d τ ^ (-a τ))

section Eqv

def EqvLin {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X) (G' : Over X)
    [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  IsGrpPullback G' t.G p ψ ∧ (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (t.act.act a).left) ∧
    (∀ γ, IsGrpPullback G' G' (ρ' γ).asIso.hom (m γ)) ∧ (∀ γ a, (act'.act a).left ≫ m γ = m γ ≫ (act'.act a).left) ∧
    (∀ γ₁ γ₂, m (γ₁ * γ₂) = m γ₂ ≫ m γ₁) ∧
    ∀ γ (x : X), X.fromSpecResidueField x ≫ (ρ' γ).asIso.hom = X.fromSpecResidueField x →
      ∀ (T : Scheme.{0}) (w : T ⟶ G'.left) (v : T ⟶ Spec (X.residueField x)),
        w ≫ G'.hom = v ≫ X.fromSpecResidueField x → w ≫ m γ = w

end Eqv

end GlobalTheory.HodgeLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ChartEigFrame

open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem tanPull_injective_of_chart {V K : Type} [CommRing V] [CommRing K] (ρ : V →+* K) (hρ : Function.Injective ρ)
    (M : MChart Y) {x : Sp V ⟶ Y.X} {x' : Sp K ⟶ Y.X} (e : spMap ρ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ M.U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ M.U) : Function.Injective (tanPull (G := Y.t.G) ρ e) := by
  intro u u' huu
  obtain ⟨cv, rfl⟩ := (vec M x h).surjective u
  obtain ⟨cv', rfl⟩ := (vec M x h).surjective u'
  rw [tanPull_vec M ρ e h h', tanPull_vec M ρ e h h'] at huu
  have := (vec M x' h').injective huu
  congr 1
  funext j
  exact hρ (congrFun this j)

theorem exists_eigFrame_of_top {X : FlagCover Y} {V K : Type} [CommRing V] [CommRing K] [Algebra c.F K]
    (ρ : V →+* K) (hρ : Function.Injective ρ) (φ : c.F →+* V) (hφ : ρ.comp φ = algebraMap c.F K)
    (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ (spMap ρ ≫ q) ⁻¹ᵁ X.F.U k)
    (htop : ∀ σ, initSpan K (X.F.vecAt k (spMap ρ ≫ q) hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ q) ≫ X.π) σ) :
    ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (tv (X.F.vecAt k q hz rfl τ i)).left := by
  have hx : ⊤ ≤ (q ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz rfl
  have hx' : ⊤ ≤ ((spMap ρ ≫ q) ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hz' rfl
  have e : spMap ρ ≫ (q ≫ X.π) = (spMap ρ ≫ q) ≫ X.π := (Category.assoc _ _ _).symm
  have hinj := tanPull_injective_of_chart ρ hρ (X.F.M k).toMChart e hx hx'
  have hpull : ∀ τ i, tanPull ρ e (X.F.vecAt k q hz rfl τ i) = X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i :=
    fun τ i => X.F.tanPull_vecAt k ρ q hz hz' rfl rfl e τ i
  have hmem : ∀ τ i, X.F.vecAt k (spMap ρ ≫ q) hz' rfl τ i ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun τ i => by
    rw [← htop τ]
    exact Submodule.subset_span ⟨i, i.2, rfl⟩
  have hsmul : ∀ (τ : E →+* ℂ) (a : 𝓞 E) (w : TanM (q ≫ X.π) Y.t.G),
      tanPull ρ e (φ (embK c τ a) • w) = algebraMap c.F K (embK c τ a) • tanPull ρ e w := fun τ a w => by
    rw [map_smulₛₗ, ← hφ]
    rfl
  refine ⟨GlobalTheory.ShFam.EigFrame.ofVec (fun τ i => X.F.vecAt k q hz rfl τ i) (fun τ i a => ?_) (fun τ w hw => ?_),
    fun τ i => rfl⟩
  · apply hinj
    rw [tanPull_actR, hsmul, hpull]
    exact hmem τ i a
  · have hw' : tanPull ρ e w ∈ eigLie c ((spMap ρ ≫ q) ≫ X.π) τ := fun a => by
      rw [← tanPull_actR, hw a, hsmul]
    rw [← htop τ] at hw'
    obtain ⟨a, -, ha⟩ := mem_initSpan.1 hw'
    obtain ⟨W, hW⟩ := X.F.uAt_split k q hz τ
    obtain ⟨cv, rfl⟩ := (vec (X.F.M k).toMChart (q ≫ X.π) hx).surjective w
    rw [X.F.sum_vecAt, tanPull_vec (X.F.M k).toMChart ρ e hx hx'] at ha
    have hc := (vec (X.F.M k).toMChart _ hx').injective ha
    rw [X.F.uAt_spMap k ρ q hz hz'] at hc
    have hWρ : W.map ρ * (X.F.uAt k q hz τ).map ρ = 1 := by
      rw [← Matrix.map_mul, hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have ha2 : (W.map ρ).mulVec (fun j => ρ (cv j)) = a := by
      rw [← hc, Matrix.mulVec_mulVec, hWρ, Matrix.one_mulVec]
    refine ⟨W.mulVec cv, ?_, fun b hb => ?_⟩
    · show _ = ∑ i, _ • X.F.vecAt k q hz rfl τ i
      rw [X.F.sum_vecAt]
      congr 1
      funext j
      apply hρ
      rw [RingHom.map_mulVec]
      have : (ρ ∘ W.mulVec cv) = a := by
        rw [← ha2]
        funext i
        exact RingHom.map_mulVec ρ W cv i
      rw [this, hc]
    · have hb' : vec (X.F.M k).toMChart (q ≫ X.π) hx cv =
          vec (X.F.M k).toMChart (q ≫ X.π) hx ((X.F.uAt k q hz τ).mulVec b) := by
        rw [← X.F.sum_vecAt]
        exact hb
      have := (vec (X.F.M k).toMChart _ hx).injective hb'
      rw [this, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]

theorem exists_eigFrame_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y X V K _ _ _ _ _ _ φ hφ q k hz yF hyF hpt
  have hz' : ⊤ ≤ (spMap (algebraMap V K) ≫ q) ⁻¹ᵁ X.F.U k := le_preimage_comp _ hz
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap (algebraMap V K) ≫ q) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap (algebraMap V K) ≫ q) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  exact exists_eigFrame_of_top (algebraMap V K) (IsFractionRing.injective V K) φ hφ q k hz hz'
    (key _ hpt fun σ => X.top K yF hyF _ hpt k hz' σ)

end GlobalTheory.ChartEigFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomainStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenspaceFrame_flagCover_chart_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : FlagCover Y) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V), (algebraMap V K).comp φ = algebraMap c.F K → ∀ (q : Sp V ⟶ X.YY) (k : X.F.J) (hz : ⊤ ≤ q ⁻¹ᵁ X.F.U k) (yF : Sp K ⟶ Xo.XF c), yF ≫ pullback.snd _ _ = spMap (algebraMap c.F K) → (spMap (algebraMap V K) ≫ q) ≫ X.π = yF ≫ Y.j → ∃ f : GlobalTheory.ShFam.EigFrame Y φ (q ≫ X.π), ∀ τ i, f.v τ i = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (X.F.vecAt k q hz rfl τ i)).left := by
  first | exact @GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt | exact GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt | (intros; apply GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev ThAt (a : AE D) (b Φ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) a
    (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 b Φ f


open Classical in
def adjDat (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0


variable {R} in
open Classical in
def keepPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∈ Q'


variable {R} in
open Classical in
def flipPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∉ Q'

end Defs

theorem suppAt_mul' {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hm : mt V (a * b) = mt V a * mt V b := by first | rfl | simp [Formalism.L2.Theta.mt]
  have key : mt V a * mt V b - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by noncomm_ring
  rw [hm, key, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

end GlobalTheory.BigOn.Exp.TupLe.Swap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm

namespace GlobalTheory.FlatModel

theorem exists_affine_normal_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

end GlobalTheory.FlatModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialOfIsSubquotient
open GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.TypeTwo.PowIrrProof

theorem equiv_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
    (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  letI : ρ.IsIrreducible := hρ
  rcases eq_bot_or_eq_top S with rfl | rfl
  · obtain ⟨v, rfl⟩ := hf y
    have hv : v = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 v.property)
    exact (hy (by rw [hv, map_zero])).elim
  · let e := (topEquiv ρ).symm
    let F : ρ.IntertwiningMap σ := f.comp e.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp e.toLinearEquiv.surjective
    have hi : Function.Injective F :=
      (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right fun hF => by
        obtain ⟨x, hx⟩ := hs y
        exact hy (by simpa [hF] using hx.symm)
    exact ⟨F.ofBijective ⟨hi, hs⟩⟩

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W] :
    Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  letI : Nontrivial S.toSubmodule := hf.nontrivial
  exact Subtype.val_injective.nontrivial (α := S.toSubmodule)

end GlobalTheory.TypeTwo.PowIrrProof
end
end
