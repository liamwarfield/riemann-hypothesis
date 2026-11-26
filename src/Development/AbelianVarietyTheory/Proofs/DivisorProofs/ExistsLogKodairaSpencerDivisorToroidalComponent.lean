module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldTopFormPairingRegularAtPointStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrix
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

namespace GlobalTheory.LogKSDiv

theorem topPair_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  intro k A _ _ α n D D' L hD η
  letI := α.toAlgebra
  have key : (Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)) :
        (Ω[A⁄k]) [⋀^Fin n]→ₗ[A] A) =
      L.det • Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j)) := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    change Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j) (v i)) =
      L.det * Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j) (v i))
    rw [mul_comm, ← Matrix.det_mul]
    congr 1
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, Matrix.mul_apply, hD j, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  show (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η = L.det * (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η
  rw [key, map_smul, LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.LogKSDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrixStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormDerivationDetPairing_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_change_matrix | exact GlobalTheory.LogKSDiv.topPair_change_matrix | (intros; apply GlobalTheory.LogKSDiv.topPair_change_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChange
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

theorem GlobalTheory.LogKSDiv.topPair_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) → (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) → ∃ u : (X₀ TF.Y Z).functionField, (u = 1 ∨ u = -1) ∧ ∀ η : RatForms (s₀ TF.Y Z) Dw.dim, GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D η = u * ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D' η := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hF _ _ w w' D D' A d hw hw' hA hd
  obtain ⟨n, n', e, e', ε, ε', L, hM, hD⟩ := GlobalTheory.T.genericPoint_logKodairaSpencer_frame_change E H Dw l Xo c TF Z hpq hF w w' D D' A hw hw' hA
  obtain ⟨u, hu, hdet⟩ := GlobalTheory.T.det_frameChange_balancedTensors_cmType E H Dw _ A n n' e e' ε ε' L hM
  refine ⟨u, hu, fun η => ?_⟩
  rw [GlobalTheory.T.topFormDerivationDetPairing_change_matrix _ D D' L hD η, hdet]
  congr 2
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  split_ifs <;> simp [zpow_natCast, hd]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChangeStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_wedge_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) → (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) → ∃ u : (X₀ TF.Y Z).functionField, (u = 1 ∨ u = -1) ∧ ∀ η : RatForms (s₀ TF.Y Z) Dw.dim, GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D η = u * ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_frameChange | exact GlobalTheory.LogKSDiv.topPair_frameChange | (intros; apply GlobalTheory.LogKSDiv.topPair_frameChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerLocalEigenFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadEigenFrameLieAlgebraToroidalComponen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadEigenFrameLieAlgebraToroidalComponen
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

namespace GlobalTheory.LogKSDiv.SpreadFrame

open scoped Matrix

theorem clear_eq {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (M : Submonoid R) [IsLocalization M L]
    {ι : Type} [Fintype ι] (X Y : ι → R) (h : ∀ i, algebraMap R L (X i) = algebraMap R L (Y i)) :
    ∃ u ∈ M, ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ u) → ∀ i, ψ (X i) = ψ (Y i) := by
  classical
  choose u hu using fun i => IsLocalization.exists_of_eq (M := M) (S := L) (h i)
  refine ⟨∏ i, (u i : R), M.prod_mem fun i _ => (u i).2, fun S _ ψ hψ i => ?_⟩
  have hp : IsUnit (ψ (u i)) :=
    isUnit_of_dvd_unit (map_dvd ψ (Finset.dvd_prod_of_mem (fun p => (u p : R)) (Finset.mem_univ i))) hψ
  have := congrArg ψ (hu i)
  rw [map_mul, map_mul] at this
  exact hp.mul_left_cancel this

theorem spread_exact {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (M : Submonoid R) [IsLocalization M L]
    {n N : ℕ} (B : Fin N → Fin n → L) (hu : ∀ v, ∃! a : Fin N → L, v = ∑ j, a j • B j)
    (P : Fin N → Matrix (Fin n) (Fin n) R) (hP : ∀ j, (P j).map (algebraMap R L) *ᵥ B j = B j) :
    ∃ g ∈ M, ∃ (s : R) (B₀ : Fin N → Fin n → R), (∀ j i, algebraMap R L (B₀ j i) = algebraMap R L s * B j i) ∧
      ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ g) → IsUnit (ψ s) ∧
        (∀ j, (P j).map ψ *ᵥ (ψ ∘ B₀ j) = ψ ∘ B₀ j) ∧ ∀ v, ∃! a : Fin N → S, v = ∑ j, a j • (ψ ∘ B₀ j) := by
  classical
  have hs : ∀ {S : Type} [CommRing S] (B : Fin N → Fin n → S) (a : Fin N → S),
      ∑ j, a j • B j = (Matrix.of B)ᵀ *ᵥ a := fun B a => by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  choose A hA using fun k => (hu (Pi.single k 1)).exists
  let Bm : Matrix (Fin n) (Fin N) L := (Matrix.of B)ᵀ
  let Am : Matrix (Fin N) (Fin n) L := (Matrix.of A)ᵀ
  have h1 : Bm * Am = 1 := by
    ext i k
    have := congrFun (hA k) i
    rw [hs] at this
    simpa [Bm, Am, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using
      this.symm
  have h2 : Am * Bm = 1 := by
    ext i j
    have e1 : B j = ∑ k, (Am *ᵥ B j) k • B k := by
      rw [hs, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have e2 : B j = ∑ k, (Pi.single j 1 : Fin N → L) k • B k := by
      simp [Pi.single_apply]
    have := congrFun ((hu (B j)).unique e1 e2) i
    simpa [Bm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
  obtain ⟨s, hsB⟩ := IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin n × Fin N => Bm p.1 p.2)
  obtain ⟨s', hsA⟩ := IsLocalization.exist_integer_multiples M Finset.univ (fun p : Fin N × Fin n => Am p.1 p.2)
  choose B₁ hB₁ using fun i j => hsB (i, j) (Finset.mem_univ _)
  choose A₁ hA₁ using fun i j => hsA (i, j) (Finset.mem_univ _)
  have eB : (Matrix.of B₁).map (algebraMap R L) = (s : R) • Bm := by ext i j; exact hB₁ i j
  have eA : (Matrix.of A₁).map (algebraMap R L) = (s' : R) • Am := by ext i j; exact hA₁ i j
  have sm : ∀ {S : Type} [CommRing S] (ψ : R →+* S) {a b : ℕ} (r : R) (X : Matrix (Fin a) (Fin b) R),
      (r • X).map ψ = ψ r • X.map ψ := fun ψ _ _ r X => by ext i j; simp
  have cl : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) R), X.map (algebraMap R L) = Y.map (algebraMap R L) →
      ∃ u ∈ M, ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ u) → X.map ψ = Y.map ψ := fun {a b} X Y h => by
    obtain ⟨u, hu, k⟩ := clear_eq M (fun p : Fin a × Fin b => X p.1 p.2) (fun p => Y p.1 p.2)
      (fun p => congrFun (congrFun h p.1) p.2)
    exact ⟨u, hu, fun S _ ψ hψ => Matrix.ext fun i j => k S ψ hψ (i, j)⟩
  obtain ⟨u₁, hu₁, k₁⟩ := cl (Matrix.of B₁ * Matrix.of A₁) (((s : R) * s') • 1) (by
    rw [Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h1, sm, algebraMap_smul, mul_smul,
      Matrix.map_one _ (map_zero _) (map_one _)])
  obtain ⟨u₂, hu₂, k₂⟩ := cl (Matrix.of A₁ * Matrix.of B₁) (((s : R) * s') • 1) (by
    rw [Matrix.map_mul, eB, eA, Matrix.smul_mul, Matrix.mul_smul, h2, sm, algebraMap_smul, mul_comm, mul_smul,
      Matrix.map_one _ (map_zero _) (map_one _)])
  obtain ⟨u₃, hu₃, k₃⟩ := clear_eq M (fun p : Fin N × Fin n => (P p.1 *ᵥ fun i => B₁ i p.1) p.2)
    (fun p => B₁ p.2 p.1) (fun p => by
      have e : (algebraMap R L ∘ fun i => B₁ i p.1) = algebraMap R L (s : R) • B p.1 := by
        funext i; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]; rw [hB₁, Algebra.smul_def]; rfl
      have := congrFun (hP p.1) p.2
      rw [show (algebraMap R L ((P p.1 *ᵥ fun i => B₁ i p.1) p.2)) =
          ((P p.1).map (algebraMap R L) *ᵥ (algebraMap R L ∘ fun i => B₁ i p.1)) p.2 from
          (RingHom.map_mulVec _ _ _ _), e, Matrix.mulVec_smul, Pi.smul_apply, this, hB₁]
      simp only [smul_eq_mul, Algebra.smul_def]; rfl)
  refine ⟨u₁ * u₂ * u₃ * (s * s'), M.mul_mem (M.mul_mem (M.mul_mem hu₁ hu₂) hu₃) (M.mul_mem s.2 s'.2), s,
    fun j i => B₁ i j, fun j i => by rw [hB₁, Algebra.smul_def]; rfl, fun S _ ψ hψ => ?_⟩
  rw [map_mul, map_mul, map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff] at hψ
  obtain ⟨⟨⟨w₁, w₂⟩, w₃⟩, ws, ws'⟩ := hψ
  have q₁ := k₁ S ψ w₁
  have q₂ := k₂ S ψ w₂
  rw [Matrix.map_mul, sm, Matrix.map_one _ (map_zero _) (map_one _)] at q₁ q₂
  have hw : IsUnit (ψ ((s : R) * s')) := by rw [map_mul]; exact ws.mul ws'
  obtain ⟨w, hw'⟩ := hw
  rw [← hw'] at q₁ q₂
  have eb : (Matrix.of fun j => ψ ∘ fun i => B₁ i j)ᵀ = (Matrix.of B₁).map ψ := rfl
  generalize (Matrix.of A₁).map ψ = A' at q₁ q₂
  have can : ∀ {a : ℕ} {x y : Fin a → S}, (w : S) • x = (w : S) • y → x = y := fun h =>
    (MulAction.injective w : Function.Injective fun x => w • x) h
  refine ⟨ws, fun j => ?_, fun v => ?_⟩
  · funext i
    have := k₃ S ψ w₃ (j, i)
    simp only at this
    rw [RingHom.map_mulVec] at this
    exact this
  · simp only [hs, eb]
    refine ⟨(↑w⁻¹ : S) • (A' *ᵥ v), can ?_, fun a ha => can ?_⟩
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, q₁, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
        Units.mul_inv, one_smul]
    · rw [smul_smul, Units.mul_inv, one_smul, ha, Matrix.mulVec_mulVec, q₂, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem basis_of_split {S M ι : Type} [CommRing S] [AddCommGroup M] [Module S M] [Fintype ι] [DecidableEq ι]
    (p : ι → Module.End S M) (hsum : ∑ τ, p τ = 1) (W : ι → Submodule S M) (hp1 : ∀ τ m, p τ m ∈ W τ)
    (hp2 : ∀ mm : ι → M, (∀ σ, mm σ ∈ W σ) → ∀ τ, p τ (∑ σ, mm σ) = mm τ)
    {κ : ι → Type} [∀ τ, Fintype (κ τ)] (b : ∀ τ, κ τ → M) (hb : ∀ τ i, b τ i ∈ W τ)
    (hbu : ∀ τ w, w ∈ W τ → ∃! a : κ τ → S, w = ∑ i, a i • b τ i) :
    ∀ v, ∃! a : (Σ τ, κ τ) → S, v = ∑ j, a j • b j.1 j.2 := by
  intro v
  have split : ∀ a : (Σ τ, κ τ) → S, ∑ j, a j • b j.1 j.2 = ∑ τ, ∑ i, a ⟨τ, i⟩ • b τ i :=
    fun a => Fintype.sum_sigma _
  choose c hc hcu using fun τ => hbu τ (p τ v) (hp1 τ v)
  refine ⟨fun j => c j.1 j.2, ?_, fun a ha => ?_⟩
  · show v = _
    rw [split]
    calc v = (∑ τ, p τ) v := by rw [hsum]; rfl
      _ = _ := by rw [LinearMap.sum_apply]; exact Finset.sum_congr rfl fun τ _ => hc τ
  · funext j
    obtain ⟨τ, i⟩ := j
    have ha : v = _ := ha
    rw [split] at ha
    have hm : ∀ σ, (∑ i, a ⟨σ, i⟩ • b σ i) ∈ W σ := fun σ =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb σ i)
    have e := hp2 _ hm τ
    rw [← ha] at e
    exact congrFun (hcu τ (fun i => a ⟨τ, i⟩) e) i

end GlobalTheory.LogKSDiv.SpreadFrame

namespace GlobalTheory.LogKSDiv.SpreadFrame

theorem eps_dual {R S : Type} [CommRing R] [CommRing S] (θ : R →+* S) (c : R) :
    spMap (epsMul (θ c)) ≫ spMap (dualMap θ) = spMap (dualMap θ) ≫ spMap (epsMul c) := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul, dualMap, mul_comm]

theorem dual_dual {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (θ : S →+* T) (l : R →+* S) :
    spMap (dualMap θ) ≫ spMap (dualMap l) = spMap (dualMap (θ.comp l)) := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem cancel_eps {R : Type} [CommRing R] {T : Scheme.{0}} {a b : Sp (DualNumber R) ⟶ T} {u : R} (hu : IsUnit u)
    (h : spMap (epsMul u) ≫ a = spMap (epsMul u) ≫ b) : a = b := by
  obtain ⟨u, rfl⟩ := hu
  have e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _ := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Spec.map_id]
    congr 1
    ext z <;> simp [epsMul]
  calc a = (spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R))) ≫ a := by rw [e, Category.id_comp]
    _ = (spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R))) ≫ b := by rw [Category.assoc, h, Category.assoc]
    _ = b := by rw [e, Category.id_comp]

end GlobalTheory.LogKSDiv.SpreadFrame

section Spread

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj


set_option maxHeartbeats 400000 in
open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigSpread in
theorem GlobalTheory.LogKSDiv.exists_spread_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (_ : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (φU : c.F →+* Γ(TF.Y.X, U.1)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v (Pi.single (e ⟨τ, i⟩) (φU (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)) ∧ (∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) := open GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigSpread GlobalTheory.LieLocBasis GlobalTheory.LogKSDiv.SpreadFrame ReciprocityTheory.ChartRestriction.G.PullbackSections in open ReciprocityTheory.ChartRestriction.G.Chart (sp IsUnivChart tmap) in open scoped Matrix in by
  intro E _ _ _ H Dw l Xo c TF Z _ x φ f hφ
  classical
  let y : TF.Y.X := (barComp TF.Y Z).ι x
  have hyb : y ∈ barComp TF.Y Z := by
    show (barComp TF.Y Z).ι x ∈ _
    have := Scheme.Opens.ι_apply (barComp TF.Y Z) x
    exact this ▸ x.2
  replace hφ : (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι ≫ TF.Y.s = spMap φ := hφ
  obtain ⟨f, rfl⟩ : ∃ f' : ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι), f' = f :=
    ⟨f, rfl⟩
  obtain ⟨U₀, hU₀, hy, x₀, hx₀, C, m, xc, hxc⟩ := GlobalTheory.ShFam.EigSpread.exists_affine_chart TF.Y.t (𝟙 TF.Y.X) y
  let lam : Γ(TF.Y.X, U₀) →+* (X₀ TF.Y Z).presheaf.stalk x := (TF.Y.X.presheaf.germ U₀ y hy ≫ (barComp TF.Y Z).ι.stalkMap x).hom
  letI : Algebra Γ(TF.Y.X, U₀) ((X₀ TF.Y Z).presheaf.stalk x) := lam.toAlgebra
  letI : Algebra Γ(TF.Y.X, U₀) (TF.Y.X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨y, hy⟩
  have hloc0 := hU₀.isLocalization_stalk ⟨y, hy⟩
  have hloc : IsLocalization (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl ((X₀ TF.Y Z).presheaf.stalk x) := by
    let e := (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact IsLocalization.isLocalization_of_algEquiv (S := TF.Y.X.presheaf.stalk y) _ { e with commutes' := fun r => rfl }
  have hpt : (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι = spMap lam ≫ x₀ := by
    rw [hx₀, Category.comp_id, ← Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [show TF.Y.X.fromSpecStalk ((barComp TF.Y Z).ι x) = TF.Y.X.fromSpecStalk y from rfl, ← hU₀.fromSpecStalk_eq_fromSpecStalk hy]
    simp only [lam, spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, IsAffineOpen.fromSpecStalk]
  let φ₀ : c.F →+* Γ(TF.Y.X, U₀) := (Spec.preimage (x₀ ≫ TF.Y.s)).hom
  have hφ₀ : spMap φ₀ = x₀ ≫ TF.Y.s := Spec.map_preimage _
  have hφl : φ = lam.comp φ₀ := spMap_inj (by
    rw [← hφ, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, hφ₀, ← Category.assoc, hpt, Category.assoc])
  subst hφl
  have vec_bc_of_chart {S : Type} [CommRing S] {X : Scheme.{0}} {t : SAB H X} {x : Sp S ⟶ X} {n : ℕ}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G}
      (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart ((Over.pullback x).obj t.G)) (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc)
      {S' : Type} [CommRing S'] (ψ : S →+* S') {x' : Sp S' ⟶ X} (h : x' = spMap ψ ≫ x) :
      ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶ (Over.pullback x').obj t.G),
        ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc' ∧ ∀ cc : Fin n → S, vec t x' xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec t x xc cc := by
    subst h
    letI : Algebra S S' := ψ.toAlgebra
    obtain ⟨x₁, hx₁, hcomp⟩ := LieChart.univChart_baseChange_of_chart (R := S) (R' := S') _ C n xc hx
    have h₁ := IsGrpPullback.comp
      (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
      (isGrpPullback_pullback t.G x)
    obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
      (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
    refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
    have key : (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
        (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  obtain ⟨xL, hxL, hvL⟩ := vec_bc_of_chart C hxc lam hpt
  choose B hB using fun τ i => vec_exists hxL _ (f.tan τ i)
  have exists_projectors {L : Type} [CommRing L] (φ : c.F →+* L) {x : Sp L ⟶ TF.Y.X} {n : ℕ}
      {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj TF.Y.t.G}
      (hx : IsUnivChart _ n xc) :
      ∃ P : (E →+* ℂ) → Matrix (Fin n) (Fin n) L, ∀ {k : Type} [CommRing k] (ψ : L →+* k) {x' : Sp k ⟶ TF.Y.X}
        {xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback x').obj TF.Y.t.G}
        (hx' : IsUnivChart _ n xc'), (∀ cc : Fin n → L, vec TF.Y.t x' xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec TF.Y.t x xc cc) → ∀ τ v, Matrix.mulVec ((P τ).map ψ) v ∈ eig c (ψ.comp φ) hx' τ ∧
          (v ∈ eig c (ψ.comp φ) hx' τ → Matrix.mulVec ((P τ).map ψ) v = v) := by
    classical
    have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
    obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
      exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
    letI : Algebra c.F L := φ.toAlgebra
    refine ⟨fun τ => LinearMap.toMatrix' (proj (rho hx) (embK c) α τ), fun {k} _ ψ {x' xc'} hx' hv τ => ?_⟩
    letI : Algebra c.F k := (ψ.comp φ).toAlgebra
    have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) (proj (rho hx') (embK c) α τ m) := fun m =>
      eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
    have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) m → proj (rho hx') (embK c) α τ m = m := fun m hm => by
      have := proj_sum_eig (rho hx') (embK c) α hinj (Pi.single τ m) (fun τ' => by
        by_cases h : τ' = τ
        · subst h; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
      rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
    have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (ψ ∘ cc) = ψ ∘ rho hx a cc :=
      fun a cc => vec_inj hx' (by
        show vec TF.Y.t _ xc' (tmap hx' _ _) = vec TF.Y.t _ xc' (_ ∘ tmap hx _ _)
        rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
    have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (ψ ∘ cc) = ψ ∘ (rho hx α ^ j) cc := fun j => by
      induction j with
      | zero => exact fun _ => rfl
      | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
    have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (ψ ∘ cc) =
        ψ ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
      induction Q using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
        funext j; simp
      | monomial j a =>
        rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
          Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        funext i
        exact (map_mul ψ _ _).symm
    have hP : (LinearMap.toMatrix' (proj (rho hx) (embK c) α τ)).map ψ =
        LinearMap.toMatrix' (proj (rho hx') (embK c) α τ) := by
      ext i j
      have s : (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 := funext fun r => by
        by_cases hj : r = j <;> simp [hj, Pi.single_apply]
      rw [Matrix.map_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, s]
      exact (congrFun (pr _ _) i).symm
    intro v
    rw [hP, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff,
      ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    exact ⟨e₁ v, e₂ v⟩
  obtain ⟨P, hP⟩ := exists_projectors φ₀ hxc
  have hPL := hP lam hxL hvL
  have hBe : ∀ τ i, B τ i ∈ eig c (lam.comp φ₀) hxL τ := fun τ i =>
    (vec_eig_iff hxL _ _).1 fun a => by rw [← hB]; exact f.eig τ i a
  have hBu : ∀ τ w, w ∈ eig c (lam.comp φ₀) hxL τ → ∃! a : Fin (Dw.mult τ) → (X₀ TF.Y Z).presheaf.stalk x,
      w = ∑ i, a i • B τ i := fun τ w hw => by
    have := f.basis τ _ (vec_tan hxL w) ((vec_eig_iff hxL _ _).2 hw)
    rw [show f.v τ = fun i => vec TF.Y.t _ xL (B τ i) from funext (hB τ)] at this
    simpa only [comb_iff hxL] using this
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨fp, hf, hfs⟩, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F)
    c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have hbasK : ∀ v : Fin m → (X₀ TF.Y Z).presheaf.stalk x,
      ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (X₀ TF.Y Z).presheaf.stalk x, v = ∑ j, a j • B j.1 j.2 := by
    letI : Algebra c.F ((X₀ TF.Y Z).presheaf.stalk x) := (lam.comp φ₀).toAlgebra
    exact
    SpreadFrame.basis_of_split (fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hxL) (embK c) α τ)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj _ _ _ hinj) (fun τ => eig c (lam.comp φ₀) hxL τ)
      (fun τ m' => by
        rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
        exact ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha (rho hxL) (embK c) α hN τ
          (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha (rho hxL) (embK c) α hinj fp hf hfs τ m'))
      (fun mm hmm τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig (rho hxL) (embK c) α hinj mm
        (fun σ => by have h := hmm σ; rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff] at h; exact h) τ) B hBe hBu
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  let Bf : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → Fin m → (X₀ TF.Y Z).presheaf.stalk x :=
    fun j => B (e.symm j).1 (e.symm j).2
  have hsum : ∀ a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → (X₀ TF.Y Z).presheaf.stalk x,
      ∑ j, a (e.symm j) • Bf j = ∑ k, a k • B k.1 k.2 := fun a =>
    Fintype.sum_equiv e.symm _ (fun k => a k • B k.1 k.2) (fun j => rfl)
  have hbasF : ∀ v, ∃! a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → (X₀ TF.Y Z).presheaf.stalk x,
      v = ∑ j, a j • Bf j := by
    intro v
    obtain ⟨a, ha, hau⟩ := hbasK v
    refine ⟨fun j => a (e.symm j), by show v = _; rw [hsum]; exact ha, fun a' ha' => funext fun j => ?_⟩
    replace ha' : v = _ := ha'
    have h1 : v = ∑ k, (fun k => a' (e k)) k • B k.1 k.2 := by
      rw [ha', ← hsum]; simp only [Equiv.apply_symm_apply]
    have := congrFun (hau _ h1) (e.symm j)
    simpa using this
  obtain ⟨g, hg, s, B₀, hB₀, hsp⟩ := SpreadFrame.spread_exact (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl Bf hbasF
    (fun j => P (e.symm j).1) (fun j => (hPL _ _).2 (hBe _ _))
  have hlg : IsUnit (lam g) := IsLocalization.map_units (M := (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
    ((X₀ TF.Y Z).presheaf.stalk x) ⟨g, hg⟩
  have hls : IsUnit (lam s) := (hsp _ lam hlg).1
  obtain ⟨g', hg'le, hyg'⟩ := hU₀.exists_basicOpen_le (V := barComp TF.Y Z) ⟨y, hyb⟩ hy
  have hU := hU₀.basicOpen (g' * g)
  let U : TF.Y.X.affineOpens := ⟨TF.Y.X.basicOpen (g' * g), hU⟩
  let ψ : Γ(TF.Y.X, U₀) →+* Γ(TF.Y.X, U.1) :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le (g' * g))).op).hom
  have hψg₀ : IsUnit (ψ (g' * g)) := TF.Y.X.toRingedSpace.isUnit_res_basicOpen (g' * g)
  have hψg : IsUnit (ψ g) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hψg₀)
  have hchart : LogKS.chart U = spMap ψ ≫ x₀ := by
    rw [hx₀, Category.comp_id]; exact (hU₀.map_fromSpec hU _).symm
  obtain ⟨xU, hxU, hvU⟩ := vec_bc_of_chart C hxc ψ hchart
  have hPU := hP ψ hxU hvU
  obtain ⟨hsU, hPψ, hbasψ⟩ := hsp _ ψ hψg
  have hyU : y ∈ U.1 := by
    show y ∈ TF.Y.X.basicOpen (g' * g)
    rw [Scheme.basicOpen_mul]
    refine ⟨hyg', (Scheme.mem_basicOpen _ _ _ hy).2 ?_⟩
    exact IsLocalization.map_units (M := (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
      (TF.Y.X.presheaf.stalk y) ⟨g, hg⟩
  have hκ : IsUnit (lam (g' * g)) := ((Scheme.mem_basicOpen _ _ _ hy).1 hyU).map ((barComp TF.Y Z).ι.stalkMap x).hom
  let θ : (X₀ TF.Y Z).presheaf.stalk x →+* (X₀ TF.Y Z).functionField := algebraMap _ _
  letI : Algebra Γ(TF.Y.X, U₀) Γ(TF.Y.X, U.1) := ψ.toAlgebra
  haveI : IsLocalization.Away (g' * g) Γ(TF.Y.X, U.1) := hU₀.isLocalization_basicOpen (g' * g)
  let ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField := IsLocalization.Away.lift (g' * g) (g := θ.comp lam) (hκ.map θ)
  have hρψ : ρ.comp ψ = θ.comp lam := IsLocalization.lift_comp _
  let w : Γ(TF.Y.X, U.1) := ↑hsU.unit⁻¹
  let cv : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → Fin m → Γ(TF.Y.X, U.1) := fun j => w • (ψ ∘ B₀ j)
  refine ⟨U, le_trans (show TF.Y.X.basicOpen (g' * g) ≤ _ by rw [Scheme.basicOpen_mul]; exact inf_le_left) hg'le, hyU, ρ, _, e,
    fun j => vec TF.Y.t (LogKS.chart U) xU (cv j), ψ.comp φ₀, ?_, fun j => vec_tan hxU _, ?_, ?_, ?_⟩
  · rw [hchart, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, hρψ, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap,
      Category.assoc, ← hpt, ← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes trivial)
  · intro w' hw'
    obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    obtain ⟨a, ha, hau⟩ := hbasψ cc
    refine ⟨fun j => a j * ψ s, ?_, fun a' ha' => funext fun j => ?_⟩
    · show cc = _
      rw [ha]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = _ • ((↑hsU.unit⁻¹ : Γ(TF.Y.X, U.1)) • _)
      rw [smul_smul, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    · replace ha' : cc = _ := ha'
      have h1 : cc = ∑ j, (fun j => a' j * w) j • (ψ ∘ B₀ j) := by
        rw [ha']; exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
      have := congrFun (hau _ h1) j
      rw [← this, _root_.mul_assoc, show w * ψ s = 1 from hsU.val_inv_mul, _root_.mul_one]
  · intro a τ i
    have hmem : cv (e ⟨τ, i⟩) ∈ eig c (ψ.comp φ₀) hxU τ := by
      have h1 := (hPU (e.symm (e ⟨τ, i⟩)).1 (ψ ∘ B₀ (e ⟨τ, i⟩))).1
      rw [hPψ] at h1
      simp only [Equiv.symm_apply_apply] at h1
      exact Submodule.smul_mem _ w h1
    have he := (vec_eig_iff hxU _ _).2 hmem a
    rw [← vec_smul hxU] at he
    rw [he, comb_iff hxU, Fintype.sum_eq_single (e ⟨τ, i⟩) (fun k hk => by rw [Pi.single_eq_of_ne hk, zero_smul]),
      Pi.single_eq_same]
  · intro τ i
    have hBj : Bf (e ⟨τ, i⟩) = B τ i := by
      show B (e.symm (e ⟨τ, i⟩)).1 (e.symm (e ⟨τ, i⟩)).2 = B τ i
      rw [Equiv.symm_apply_apply]
    have eL : spMap (epsMul (lam s)) ≫ f.v τ i =
        spMap (dualMap lam) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩)) := by
      rw [hB, ← vec_smul hxL, ← hvL]
      congr 1
      funext k
      have := hB₀ (e ⟨τ, i⟩) k
      rw [hBj] at this
      exact this.symm
    have eU : spMap (epsMul (ψ s)) ≫ vec TF.Y.t (LogKS.chart U) xU (cv (e ⟨τ, i⟩)) =
        spMap (dualMap ψ) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩)) := by
      rw [← vec_smul hxU, ← hvU]
      congr 1
      simp only [cv, w, smul_smul, IsUnit.mul_val_inv, one_smul]
    have hθ : θ (lam s) = ρ (ψ s) := by
      show (θ.comp lam) s = (ρ.comp ψ) s
      rw [hρψ]
    have L1 : spMap (epsMul (θ (lam s))) ≫ spMap (dualMap θ) ≫ f.v τ i =
        spMap (dualMap (θ.comp lam)) ≫ vec TF.Y.t x₀ xc (B₀ (e ⟨τ, i⟩)) := by
      rw [← Category.assoc, SpreadFrame.eps_dual, Category.assoc, eL, ← Category.assoc, SpreadFrame.dual_dual]
    refine SpreadFrame.cancel_eps (hls.map θ) (L1.trans ?_)
    rw [hθ, ← Category.assoc, SpreadFrame.eps_dual, Category.assoc, eU, ← Category.assoc, SpreadFrame.dual_dual, hρψ]

end Spread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadEigenFrameLieAlgebraToroidalComponenStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_eigenFrame_lieAlgebra_toroidalComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (_ : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (φU : c.F →+* Γ(TF.Y.X, U.1)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v (Pi.single (e ⟨τ, i⟩) (φU (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)) ∧ (∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) := by
  first | exact @GlobalTheory.LogKSDiv.exists_spread_eigFrame | exact GlobalTheory.LogKSDiv.exists_spread_eigFrame | (intros; apply GlobalTheory.LogKSDiv.exists_spread_eigFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatio
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

theorem exists_derivation_extend {k A K : Type} [CommRing k] [CommRing A] [CommRing K] [Algebra k A] [Algebra k K]
    [Algebra A K] [IsScalarTower k A K] [Algebra.FormallyEtale A K] (D : Derivation k A A) :
    ∃ D' : Derivation k K K, ∀ a, D' (algebraMap A K a) = algebraMap A K (D a) := by
  let d : Derivation k A K := (Algebra.linearMap A K).compDer D
  let f : Ω[A⁄k] →ₗ[A] K := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale k A K
  let g : Ω[K⁄k] →ₗ[K] K := hb.lift f
  refine ⟨g.compDer (KaehlerDifferential.D k K), fun a => ?_⟩
  change g (KaehlerDifferential.D k K (algebraMap A K a)) = _
  rw [← KaehlerDifferential.map_D k k A K]
  erw [hb.lift_eq]
  simp [f, d]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

theorem germ_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (V : Y.Opens) (U' : X.Opens) (e : U' ≤ f ⁻¹ᵁ V) (x : X)
    (hx : x ∈ U') (hfx : f x ∈ V) (y : Γ(Y, V)) :
    X.presheaf.germ U' x hx (f.appLE V U' e y) = f.stalkMap x (Y.presheaf.germ V (f x) hfx y) := by
  rw [Scheme.Hom.germ_stalkMap_apply f V x hfx y, Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

def derivOfConst {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (D : Derivation ℤ A A)
    (hD : ∀ a, D (φ a) = 0) : (letI := φ.toAlgebra; Derivation k A A) :=
  letI := φ.toAlgebra
  { toFun := D
    map_add' := D.map_add
    map_smul' := fun a x => by
      rw [Algebra.smul_def, D.leibniz, RingHom.algebraMap_toAlgebra, hD, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := D.map_one_eq_zero
    leibniz' := D.leibniz }

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

theorem exists_genDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U hU ρ hρ N Dl
  set W := barComp TF.Y Z with hW
  set η₀ := genericPoint (X₀ TF.Y Z) with hη₀
  have hη : W.ι η₀ ∈ U.1 := by
    have e := congrArg (fun f : Sp (X₀ TF.Y Z).functionField ⟶ TF.Y.X => f (IsLocalRing.closedPoint _)) hρ
    simp only [Scheme.Hom.comp_apply] at e
    show W.ι η₀ ∈ (U.1 : Set TF.Y.X)
    rw [← U.2.range_fromSpec]
    refine ⟨_, e.trans ?_⟩
    exact congrArg W.ι Scheme.fromSpecStalk_closedPoint
  have hmono : Mono (LogKS.chart U) := by
    haveI := U.2.isOpenImmersion_fromSpec
    unfold LogKS.chart; infer_instance
  have hρ' : ρ = (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom := by
    have e : CommRingCat.ofHom ρ = TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀ := by
      apply Spec.map_injective
      rw [← cancel_mono (LogKS.chart U)]
      refine hρ.trans ?_
      have e1 := U.2.fromSpecStalk_eq_fromSpecStalk hη
      rw [Spec.map_comp, Category.assoc, LogKS.chart]
      show (X₀ TF.Y Z).fromSpecStalk η₀ ≫ W.ι = _
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← e1]
      rfl
    exact congrArg CommRingCat.Hom.hom e
  subst hρ'
  have hiso : IsIso (W.ι.stalkMap η₀) := inferInstance
  letI iA : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra
  letI iK : Algebra c.F (X₀ TF.Y Z).functionField := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI iAK : Algebra Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ U.1 (W.ι η₀) hη ≫ W.ι.stalkMap η₀).hom.toAlgebra
  have htow : IsScalarTower c.F Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, GlobalTheory.Cartier.constFn, GlobalTheory.Cartier.fnOf,
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, CommRingCat.hom_comp]
    refine (germ_appLE_apply (s₀ TF.Y Z) ⊤ ⊤ _ (genericPoint (X₀ TF.Y Z)) trivial trivial _).trans ?_
    refine Eq.trans ?_ (congrArg (W.ι.stalkMap η₀).hom
      (germ_appLE_apply TF.Y.s ⊤ U.1 _ (W.ι η₀) hη trivial _)).symm
    rw [show s₀ TF.Y Z = W.ι ≫ TF.Y.s from rfl, Scheme.Hom.stalkMap_comp]
    rfl
  letI iS : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk (W.ι η₀)) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (U := U.1) ⟨W.ι η₀, hη⟩
  have hloc := U.2.isLocalization_stalk ⟨W.ι η₀, hη⟩
  let eK : TF.Y.X.presheaf.stalk (W.ι η₀) ≃ₐ[Γ(TF.Y.X, U.1)] (X₀ TF.Y Z).functionField :=
    AlgEquiv.ofRingEquiv (f := (asIso (W.ι.stalkMap η₀)).commRingCatIsoToRingEquiv) fun _ => rfl
  haveI := IsLocalization.isLocalization_of_algEquiv (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl eK
  haveI : Algebra.FormallyEtale Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField :=
    Algebra.FormallyEtale.of_isLocalization (U.2.primeIdealOf ⟨W.ι η₀, hη⟩).asIdeal.primeCompl
  choose D hD using fun j => exists_derivation_extend (k := c.F) (K := (X₀ TF.Y Z).functionField)
    (derivOfConst (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1) (Dl j).1 (Dl j).2.1)
  exact ⟨D, fun j r => hD j r⟩

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatioStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  first | exact @GlobalTheory.LogKSDiv.exists_genDer_extend | exact GlobalTheory.LogKSDiv.exists_genDer_extend | (intros; apply GlobalTheory.LogKSDiv.exists_genDer_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerLocalEigenFrame
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

theorem exists_genKS_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z (fun τ k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) D ∧ ∀ (U : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U), TopForm.IsFrame ω → ∀ hx : x ∈ U, RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ x φ f hφ
  obtain ⟨U, hU, hxU, ρ, n, e, v, φU, hρ, htan, hbas, heig, hw⟩ := GlobalTheory.T.exists_spread_eigenFrame_lieAlgebra_toroidalComponent E H Dw l Xo c TF Z x φ f hφ
  obtain ⟨ε, b, hKS⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v φU htan hbas heig
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation E H Dw l Xo c TF Z U hU ρ hρ (fun j => b j)
  exact ⟨D, ⟨U, hU, ρ, n, e, v, ε, fun j => b j, hρ, htan, hbas, fun τ i => hw τ i, hKS, hD⟩,
    fun U' ω hω hx => GlobalTheory.T.exists_logVectorField_topForm_pairing_regular_at_point E H Dw l Xo c TF Z x U hU hxU ρ hρ b D hD U' ω hω hx⟩

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerLocalEigenFrameStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logKodairaSpencer_local_eigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z (fun τ k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) D ∧ ∀ (U : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U), TopForm.IsFrame ω → ∀ hx : x ∈ U, RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  first | exact @GlobalTheory.LogKSDiv.exists_genKS_local | exact GlobalTheory.LogKSDiv.exists_genKS_local | (intros; apply GlobalTheory.LogKSDiv.exists_genKS_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponent
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

theorem exists_logKS_div : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim) (D' : CartierDiv (X₀ TF.Y Z)) (r : K.bundle.ι → (X₀ TF.Y Z).functionFieldˣ), Presents D' K.bundle r → ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∀ D : CartierDiv (X₀ TF.Y Z), (∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)))) → ∃ h : (X₀ TF.Y Z).functionField, ∀ x : X₀ TF.Y Z, ∃ g g' : (X₀ TF.Y Z).functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧ RegAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ∧ (UnitAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hfn _ _ K D' r hr φ₀ f₀ hφ₀ D hD
  obtain ⟨D₀, hD₀⟩ := GlobalTheory.T.exists_logKodairaSpencer_genericEigenFrame E H Dw l Xo c TF Z hpq hfn φ₀ f₀ hφ₀
  obtain ⟨i₀, hi₀⟩ := exists_chart K.isLB (genericPoint (X₀ TF.Y Z))
  set T₀ := GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D₀ with hT₀
  refine ⟨(r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)), fun x => ?_⟩
  obtain ⟨φ, f, A, d, hφ, hd, hA, hDx⟩ := hD x
  obtain ⟨Dx, hDxKS, hloc⟩ := GlobalTheory.T.exists_logKodairaSpencer_local_eigenFrame E H Dw l Xo c TF Z hpq hfn x φ f hφ
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.logKodairaSpencer_wedge_frameChange E H Dw l Xo c TF Z hpq hfn _ _ D₀ Dx A d hD₀ hDxKS hA hd
  obtain ⟨i, hi⟩ := exists_chart K.isLB x
  refine ⟨_, r i, hDx, hr.isEqn i x hi, ?_⟩
  have hgi : genericPoint (X₀ TF.Y Z) ∈ K.bundle.U i := gen_mem hi
  have key : (r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)) =
      r i * T₀ (formOf _ hgi (K.om i)) := by
    have e1 := formOf_eq_ratio_smul hi₀ hgi (K.isFrame i₀) (K.isFrame i)
    have e2 := hr.isRatSec i₀ i (GlobalTheory.Cartier.memInf hi₀ hgi)
    rw [K.g_eq_ratio] at e2
    rw [e1, map_smul, smul_eq_mul, e2]
    ring
  have e : (r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)) *
      ((∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)) : (X₀ TF.Y Z).functionFieldˣ) :
        (X₀ TF.Y Z).functionField) / (r i : (X₀ TF.Y Z).functionField) =
      u * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) Dx (formOf _ hgi (K.om i)) := by
    rw [key, hu']
    have h1 : ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) :
        (X₀ TF.Y Z).functionField) * ((∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)) :
          (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]
      simp [← zpow_add]
    have h2 := (r i).ne_zero
    have h3 : ∀ (ri P Q a b : (X₀ TF.Y Z).functionField), ri ≠ 0 → P * Q = 1 →
        ri * (a * P * b) * Q / ri = a * b := fun ri P Q a b hri hPQ => by
      calc ri * (a * P * b) * Q / ri = (a * b * (P * Q)) * (ri / ri) := by ring
        _ = a * b := by rw [hPQ, div_self hri]; ring
    exact h3 _ _ _ _ _ h2 h1
  obtain ⟨hreg, hunit⟩ := hloc (K.bundle.U i) (K.om i) (K.isFrame i) hi
  have hu1 : UnitAt x u := by
    rcases hu with rfl | rfl
    · exact unitAt_one x
    · exact ⟨-1, isUnit_one.neg, by simp⟩
  rw [e]
  refine ⟨hu1.regAt.mul hreg, ⟨fun h => hunit.1 ?_, fun h => hu1.mul (hunit.2 h)⟩⟩
  have := hu1.inv.mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hu1.ne_zero, one_mul] at this

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponentStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim) (D' : CartierDiv (X₀ TF.Y Z)) (r : K.bundle.ι → (X₀ TF.Y Z).functionFieldˣ), Presents D' K.bundle r → ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∀ D : CartierDiv (X₀ TF.Y Z), (∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)))) → ∃ h : (X₀ TF.Y Z).functionField, ∀ x : X₀ TF.Y Z, ∃ g g' : (X₀ TF.Y Z).functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧ RegAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ∧ (UnitAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  first | exact @GlobalTheory.LogKSDiv.exists_logKS_div | exact GlobalTheory.LogKSDiv.exists_logKS_div | (intros; apply GlobalTheory.LogKSDiv.exists_logKS_div <;> assumption)
end
