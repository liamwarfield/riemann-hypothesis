module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinety
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitaryContraction

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_zpow (x : Lˣ) (k : ℤ) : ordL ((x ^ k : Lˣ) : L) = k * ordL (x : L) := by
  have h0 : Valued.v (x : L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hk : Valued.v ((x ^ k : Lˣ) : L) = ((a ^ k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, WithZero.coe_zpow]
  rw [UnitaryCorrection.ordL_of_eq hk, UnitaryCorrection.ordL_of_eq ha.symm, toAdd_zpow]
  simp

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem diagT_mem_iwGL (w : Pl E) (n : ℕ) (s : Fin n → (w.adicCompletion E)ˣ)
    (hs : ∀ i, Valued.v (s i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w := by
  have hle : ∀ t : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (t i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) t).val i j) ≤ 1 := by
    intro t ht i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, ht]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le_one
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1]
  refine ⟨hle s hs, ?_, ?_⟩
  · rw [← map_inv]
    refine hle _ fun i => ?_
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, fU n w b ϖ l γ ≠ 0 → ∃ m ∈ iwU n w b, ∃ u : Fin n → (w.adicCompletion E)ˣ, (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (m⁻¹ * γ * m).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ hγ
  obtain ⟨-, hcc, hcv, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨hW1, hW2, -, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  obtain ⟨hanti, hrev⟩ := GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl
  have hγ' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b,
      γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra h
    exact hγ (if_neg h)
  obtain ⟨x, hx, z, hz, e⟩ := hγ'
  obtain ⟨δ, hδ⟩ : ∃ δ : GLw n w, δ = b⁻¹ * γ.1 * b := ⟨_, rfl⟩
  have hγδ : γ.1 = b * δ * b⁻¹ := by rw [hδ]; group
  have hδd : dcos n w (tdiag ϖ (wexp n l)) δ ≠ 0 := by
    have h : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ (wexp n l) * z :=
      ⟨_, (hW2 x).1 hx, _, (hW2 z).1 hz, by rw [hδ, e]; group⟩
    simp only [dcos, if_pos h]
    exact one_ne_zero
  have hδU : δ ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) :=
    (hW1 δ).1 (by rw [← hγδ]; exact γ.2)
  obtain ⟨m0, hm0, τ, ⟨hτ0, hτ1⟩, hmτ⟩ := hyp (wexp n l) hanti δ hδd
  have hne : ∀ i, τ.val i i ≠ 0 := fun i h => by
    have := hτ1 i
    rw [h, map_zero] at this
    exact zero_ne_one this
  obtain ⟨v, hv⟩ : ∃ v : Fin n → (w.adicCompletion E)ˣ, ∀ i, (v i : w.adicCompletion E) = τ.val i i :=
    ⟨fun i => Units.mk0 _ (hne i), fun i => rfl⟩
  have hτv : τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
    apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hv]
    · rw [Matrix.diagonal_apply_ne _ h, hτ0 i j h]
  obtain ⟨u, hu⟩ : ∃ u : Fin n → (w.adicCompletion E)ˣ, u = fun i => ϖ ^ wexp n l i * v i := ⟨_, rfl⟩
  have htu : tdiag ϖ (wexp n l) * τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [hτv, hu, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (u i : w.adicCompletion E) = wexp n l i := by
    intro i
    rw [hu]
    simp only [Units.val_mul]
    rw [UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _), ordL_zpow, hϖ.1,
      UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, hτ1, map_one]),
      UnitaryCorrection.ordL_one]
    simp
  have hm0e := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n m0).1.1 hm0
  have hδe : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * m0⁻¹ = δ := by
    rw [← htu, ← hmτ]
    group
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.UnitaryCorrection.main (w.adicCompletion E) (cj w) hcc hcv
    (GlobalTheory.T.norm_one_unit_hilbert_ninety E hU w hw) n (wexp n l) hanti.injective hrev u hord m0 hm0e.1 hm0e.2.1
    (by rw [hδe]; exact hδU)
  have hm1 : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w :=
    mul_mem hm0 (diagT_mem_iwGL w n s hs1)
  have hcomm : (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ *
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp [mul_comm]
  refine ⟨⟨b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹, (hW1 _).2 hs2⟩,
    (hW2 _).2 ?_, u, hord, ?_⟩
  · have : b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b =
        m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by group
    change b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b ∈ iwGL n w
    rw [this]
    exact hm1
  · change (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹)⁻¹ * γ.1 *
      (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) = _
    rw [hγδ]
    have hd : m0⁻¹ * δ * m0 = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by rw [hmτ, htu]
    calc _ = b * ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ * (m0⁻¹ * δ * m0) *
          GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹ := by group
      _ = _ := by rw [hd, hcomm]

end GlobalTheory.CompanionTheory.UnitaryContraction
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Onto

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)

section Coord

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_comp_ringHom {L Ω : Type} [Field L] [Field Ω] (j : L →+* Ω) (w : (Σ k, ι k) → L) :
    Geo.mCoordIdeal (fun p => j (w p)) = Geo.mCoordIdeal w := by
  have key : ∀ f : Geo.MRing ι, Geo.mConeMap (fun p => j (w p)) f = MvPolynomial.map j (Geo.mConeMap w f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Geo.mConeMap]
  ext f
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective j j.injective)

theorem mCoordIdeal_blockScale {Ω : Type} [Field Ω] (c : K → Ω) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → Ω) :
    Geo.mCoordIdeal (fun p : Σ k, ι k => c p.1 * z p) = Geo.mCoordIdeal z := by
  let φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k) * X k
  let φ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k)⁻¹ * X k
  have hinv : φ'.comp φ = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [φ, φ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hinj : Function.Injective φ := fun a b h => by
    have := congrArg φ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv] at this
  have hcomp : ∀ g, Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) g = φ (Geo.mConeMap z g) := by
    intro g
    have : Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) = (φ.restrictScalars ℤ).comp (Geo.mConeMap z) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp only [Geo.mConeMap, aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, φ, map_mul, aeval_C,
        algebraMap_eq]
      ring
    rw [this]; rfl
  ext g
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, hcomp, map_eq_zero_iff φ hinj]

theorem mCoordIdeal_of_ker {Ω : Type} [Field Ω] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (φ : Geo.MRing ι →+* Ω) (hφ : RingHom.ker φ = P) : Geo.mCoordIdeal (fun p => φ (X p)) = P := by
  have hev : ∀ f, aeval (fun p => φ (X p)) f = φ f := by
    intro f
    have : ((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω) = φ :=
      MvPolynomial.ringHom_ext
        (fun r => RingHom.congr_fun (Subsingleton.elim
          (((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω).comp C) (φ.comp C)) r)
        (fun p => by simp)
    exact congrArg (fun ψ => ψ f) this
  apply le_antisymm
  · intro f hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf
    have e : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp
        (Geo.mConeMap (fun p => φ (X p))) = aeval (fun p => φ (X p)) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp [Geo.mConeMap]
    have := congrArg (fun ψ => ψ f) e
    simp only [AlgHom.comp_apply, hf, map_zero, hev] at this
    rw [← hφ, RingHom.mem_ker]
    exact this.symm
  · have hP' := hP
    obtain ⟨S, hS, hPS⟩ := hP'
    rw [hPS, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h0 : φ f = 0 := by
      rw [← RingHom.mem_ker, hφ, hPS]
      exact Ideal.subset_span hf
    rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, hev, h0, C_0, mul_zero]

end Coord

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem exists_ptIdeal_eq_mCoordIdeal {F : Type} [Field F] (v : (Σ k, Bk n k) → F)
    (hv : ∀ k, ∃ i, v ⟨k, i⟩ ≠ 0) : ∃ x : MP ℤ m n, ptIdeal x = Geo.mCoordIdeal v := by
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => v ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hv k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp F ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
  have ha : ∀ k, a k ≫ ProjSpace.toSpecBase ℤ (n k) = spMap (Int.castRingHom F) := by
    intro k
    dsimp only [a]
    rw [GlobalTheory.ProjSpace.pt, ProjSpace.toSpecBase, ProjPoint.ofHom_toSpecZero_assoc,
      ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C _ _ r
  let g : Sp F ⟶ MP ℤ m n := ProjSpace.lift m n (spMap (Int.castRingHom F)) a ha
  have hg : ∀ k, g ≫ prB n k = a k := fun k => ProjSpace.lift_pr m n _ a ha k
  let p : Sp F := IsLocalRing.closedPoint F
  let x : MP ℤ m n := g p
  let θ : F →+* (Sp F).residueField p :=
    ((Sp F).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp F).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (v ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (v ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp F).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : F, ((Sp F).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp F).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (v ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  refine ⟨x, ?_⟩
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ v,
    ← mCoordIdeal_blockScale (fun k => θ (v ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_ptIdeal_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Geo.MRing (Bk n)))
    (hP : Geo.IsMultiProjPrime P) : ∃ x : MP ℤ m n, ptIdeal x = P := by
  obtain ⟨hp, hh, hr⟩ := hP
  let φ : Geo.MRing (Bk n) →+* FractionRing (Geo.MRing (Bk n) ⧸ P) :=
    (algebraMap (Geo.MRing (Bk n) ⧸ P) _).comp (Ideal.Quotient.mk P)
  have hφ : RingHom.ker φ = P := by
    ext f
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff (algebraMap (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
      (IsFractionRing.injective (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
  have hv : ∀ k, ∃ i, φ (X ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [← hφ, RingHom.mem_ker]
    exact h0
  obtain ⟨x, hx⟩ := exists_ptIdeal_eq_mCoordIdeal (fun p => φ (X p)) hv
  exact ⟨x, hx.trans (mCoordIdeal_of_ker P hh φ hφ)⟩

end GlobalTheory.CompanionTheory.MPDict.Onto
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquiv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WordProd.OneBlockProd

theorem exists_equiv_tensor {α : Type} [Fintype α] [DecidableEq α] (X : α → Type) [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (i₀ : α) (hx : ∀ i, i ≠ i₀ → ∃ v : X i, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w) :
    ∃ (x : ∀ i, X i) (ι : X i₀ ≃ₗ[ℂ] ⨂[ℂ] i, X i),
      ∀ v, ι v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := by
  have hx' : ∀ i, ∃ (x : X i) (c : Module.Dual ℂ (X i)), i ≠ i₀ → c x = 1 ∧ ∀ w, c w • x = w := by
    intro i
    by_cases hi : i = i₀
    · exact ⟨0, 0, fun h => absurd hi h⟩
    · obtain ⟨v, hv, hs⟩ := hx i hi
      obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (X i), f v ≠ 0 := by
        by_contra h
        push Not at h
        exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
      refine ⟨v, (f v)⁻¹ • f, fun _ => ⟨by simp [hf], fun w => ?_⟩⟩
      obtain ⟨a, rfl⟩ := hs w
      simp [hf, mul_comm]
  choose x c hc using hx'
  let T : X i₀ →ₗ[ℂ] ⨂[ℂ] i, X i := (PiTensorProduct.tprod ℂ).toLinearMap x i₀
  have hT : ∀ v, T v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := fun v => rfl
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun v hv => ?_
    refine (Module.forall_dual_apply_eq_zero_iff ℂ v).1 fun l => ?_
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap
      (Function.update c i₀ l))) hv
    rw [hT, PiTensorProduct.lift.tprod, map_zero] at h1
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
    rw [Finset.prod_eq_single_of_mem i₀ (Finset.mem_univ _) (fun i _ hi => by
      rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact (hc i hi).1)] at h1
    simpa using h1
  have hsurj : Function.Surjective T := by
    intro y
    refine PiTensorProduct.induction_on y (fun r f => ?_) (fun y z hy hz => ?_)
    · let d : α → ℂ := fun i => if h : i = i₀ then 1 else c i (f i)
      have e1 : f = fun i => d i • Function.update x i₀ (f i₀) i := by
        funext i
        by_cases h : i₀ = i
        · subst h
          simp [d]
        · have h' : i ≠ i₀ := fun e => h e.symm
          simp only [d, dif_neg h', Function.update_of_ne h']
          exact ((hc i h').2 (f i)).symm
      have e2 : PiTensorProduct.tprod ℂ f =
          (∏ i, d i) • PiTensorProduct.tprod ℂ (Function.update x i₀ (f i₀)) := by
        calc
          _ = PiTensorProduct.tprod ℂ (fun i => d i • Function.update x i₀ (f i₀) i) := congrArg _ e1
          _ = _ := by simpa using (PiTensorProduct.tprod ℂ).map_smul_univ d (Function.update x i₀ (f i₀))
      exact ⟨r • (∏ i, d i) • f i₀, by rw [map_smul, map_smul, hT, e2]⟩
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hz
      exact ⟨u + v, map_add _ _ _⟩
  exact ⟨x, LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible) : ∃ v : V, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w := by
  have hg : ∀ g : G, g = 1 := fun g => Subsingleton.elim _ _
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  refine ⟨v, hv, fun w => ?_⟩
  have : w ∈ S := by rw [hS]; trivial
  exact Submodule.mem_span_singleton.1 this

theorem exists_conj_perm {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (e : n ≃ n) :
    ∃ w : GL n R, ∀ y : GL n R,
      ((w * y * w⁻¹ : GL n R) : Matrix n n R) = (y : Matrix n n R).submatrix e e := by
  let P : Matrix n n R := (1 : Matrix n n R).submatrix e (Equiv.refl n)
  let Q : Matrix n n R := (1 : Matrix n n R).submatrix (Equiv.refl n) e
  have hP : ∀ y : Matrix n n R, P * y = y.submatrix e (Equiv.refl n) := fun y => by
    ext s t
    simp [P, Matrix.mul_apply, Matrix.one_apply]
  have hQ : ∀ y : Matrix n n R, y * Q = y.submatrix (Equiv.refl n) e := fun y => by
    ext s t
    simp [Q, Matrix.mul_apply, Matrix.one_apply]
  have h1 : P * Q = 1 := by
    rw [hQ]
    ext s t
    simp [P, Matrix.one_apply]
  have h2 : Q * P = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨P, Q, h1, h2⟩, fun y => ?_⟩
  show P * (y : Matrix n n R) * Q = _
  rw [hQ, hP]
  rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_parInd {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W}
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hP : ∀ g : GL n k, g ∈ parab k e)
    (hd : ∀ z, deltaHalf k m z = 1) (L : V ≃ₗ[ℂ] W)
    (law0 : ∀ (p : parab k e) v, ρ (leviProj k e p) (L v) = L (π p v)) :
    Nonempty (π.Equiv (parInd e ρ)) := by
  have law : ∀ (p : parab k e) v, GlobalTheory.SmGL.twist ρ (deltaHalf k m) (leviProj k e p) (L v) = L (π p v) := fun p v => by
    simp only [twist_apply, hd, Units.val_one, one_smul, law0]
  let f : π.IntertwiningMap (parInd e ρ) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          refine Eq.trans ?_ (law p _).symm
          simp⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          simp [hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        simp)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩⟩
  · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) h
    simpa using h1
  · have h1 := φ.1.2 ⟨x, hP x⟩ 1
    rw [mul_one] at h1
    refine (law ⟨x, hP x⟩ _).symm.trans ?_
    rw [L.apply_symm_apply]
    exact h1.symm

theorem multiProd_single {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k))
    (g : (Σ i, Fin (b i)) ≃ Fin (b i₀)) :
    Nonempty ((multiProd g fun i => (σ i).ρ).Equiv (σ i₀).ρ) := by
  have hP : ∀ x : GL (Fin (b i₀)) k, x ∈ parab k g := fun x =>
    OneBlockCell.mem_parab_of_single g i₀ h0 x
  have hsub : ∀ i, i ≠ i₀ → Subsingleton (GL (Fin (b i)) k) := by
    intro i hi
    haveI : IsEmpty (Fin (b i)) := by rw [h0 i hi]; infer_instance
    exact ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨x, ι, hι⟩ := exists_equiv_tensor (fun i => (σ i).V) i₀ (fun i hi =>
    haveI := hsub i hi
    exists_line (σ i).ρ (σ i).irr)
  let E : Fin (b i₀) ≃ Fin (b i₀) := (OneBlockCell.valEquiv i₀ rfl h0).symm.trans g
  obtain ⟨w, hw⟩ := exists_conj_perm (R := k) E
  have hwp : ∀ p : parab k g, leviProj k g p i₀ = w * (p : GL (Fin (b i₀)) k) * w⁻¹ := fun p =>
    Units.ext (Matrix.ext fun s t => by
      rw [hw]
      rfl)
  let A : (σ i₀).V ≃ₗ[ℂ] (σ i₀).V := LinearEquiv.ofLinear ((σ i₀).ρ w) ((σ i₀).ρ w⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  obtain ⟨φ⟩ := nonempty_equiv_parInd (ρ := piTensor fun i => (σ i).ρ) (π := (σ i₀).ρ) g (σ i₀).smooth hP
    (OneBlockCell.deltaHalf_eq_one_of_single i₀ h0) (A.trans ι) (fun p v => by
      show (piTensor fun i => (σ i).ρ) (leviProj k g p) (ι ((σ i₀).ρ w v)) = ι ((σ i₀).ρ w ((σ i₀).ρ p v))
      rw [hι, hι, piTensor_tprod]
      refine congrArg _ (funext fun i => ?_)
      rw [Function.apply_update (fun i u => (σ i).ρ (leviProj k g p i) u)]
      by_cases h : i₀ = i
      · subst h
        rw [Function.update_self, Function.update_self, hwp, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel_right, map_mul, Module.End.mul_apply]
      · have h' : i ≠ i₀ := fun e => h e.symm
        haveI := hsub i h'
        rw [Function.update_of_ne h', Function.update_of_ne h',
          Subsingleton.elim (leviProj k g p i) 1, map_one]
        rfl)
  exact ⟨φ.symm⟩

theorem multiProd_clOf_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL (k := k)) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  intro k _ _ _ _ a α _ _ b i₀ hb h0 g
  obtain ⟨N, c⟩ := a
  dsimp only at hb g ⊢
  subst hb
  obtain ⟨φ⟩ := multiProd_single b i₀ h0 (fun i => (clOf ⟨b i₀, c⟩ (b i)).rep) g
  have key : ∀ d : IrrCl (GL (Fin (b i₀)) k), d = c → Nonempty (d.rep.ρ.Equiv c.rep.ρ) := by
    rintro _ rfl
    exact ⟨.refl _⟩
  obtain ⟨ψ⟩ := key _ (clOf_self ⟨b i₀, c⟩)
  exact ⟨φ.trans ψ⟩

end GlobalTheory.CompanionTheory.WordProd.OneBlockProd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquivStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multi_product_single_factor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL (k := k)) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single | exact GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single | (intros; apply GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRest
theorem UpperTheory.Reformulated.B.DYha2.main :
    ∀ {X Y : Type} [inst : AddCommGroup X] [inst_1 : _root_.Module ℂ X] [inst_2 : AddCommGroup Y]
      [inst_3 : _root_.Module ℂ Y] {x : X} {y : Y}, x ≠ (0 : X) → y ≠ (0 : Y) → x ⊗ₜ[ℂ] y ≠ (0 : TensorProduct ℂ X Y) := by
  intro X Y _ _ _ _ x y hx hy h
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℂ hy
  have key := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ f g)) h
  simp only [TensorProduct.lift.tmul, map_zero, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at key
  exact (mul_ne_zero hf hg) key
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.JacquetLeft

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tmul_ne_zero' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DYha2.main hx hy

theorem isCuspidal_of_jacquet_min_left {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [Nontrivial W']
    (π : Representation ℂ (GL (Fin n) k) V) (h : a + b = n)
    (hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < a →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))))
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W') (hσ : IsSmooth σ)
    (φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ)) (hφ : Function.Surjective φ) :
    IsCuspidal σ := by
  refine (isCuspidal_iff_maximal k a W σ).2 ⟨hσ, fun r t h' hr ht => ?_⟩
  have hcd : r + (t + b) = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin r (t + b) hcd hr (by omega))
  set K' := twKer σ (unipRad k (two (stdSum h'))) 1 with hK'
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  let T : W ⊗[ℂ] W' →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := LinearMap.rTensor W' K'.mkQ
  let Φ : V →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := T ∘ₗ φ.toLinearMap ∘ₗ Kab.mkQ
  have hΦ : ∀ v, Φ v = T (φ (Submodule.Quotient.mk v)) := fun v => rfl

  have hA : ∀ u' ∈ unipRad k (two (stdSum h')), ∀ y : W ⊗[ℂ] W',
      T (extTensor σ ρ (u', 1) y) = T y := by
    intro u' hu' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w w' =>
      rw [extTensor_tmul]
      simp only [T, LinearMap.rTensor_tmul, map_one, Module.End.one_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq K').2 (Submodule.subset_span ⟨⟨u', hu'⟩, w, by simp⟩)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, GeneralLinearGroup.det g.1 = 1 → g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show GlobalTheory.SmGL.jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)
  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V, Φ (π u v) = Φ v := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg2 : g.2 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg1 : g.1 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.1 = 1 := det_eq_one_of_mem_unipRad k hg1
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    rw [hu_eq, map_mul, Module.End.mul_apply, hΦ, ← hB g hdet hg2, φ.isIntertwining,
      show g = (g.1, 1) from Prod.ext rfl hg2, hA _ hg1, hN _ hn', ← hΦ]

  have hΦ0 : ∀ v, Φ v = 0 := by
    intro v
    have hv : v ∈ twKer π (unipRad k (two (stdSum hcd))) 1 := hJ ▸ Submodule.mem_top
    have : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, w, rfl⟩
      simp [hC u u.2 w]
    exact this hv
  have hsurj : Function.Surjective Φ :=
    (LinearMap.rTensor_surjective W' (Submodule.mkQ_surjective K')).comp
      (hφ.comp (Submodule.mkQ_surjective Kab))

  show Subsingleton (W ⧸ K')
  refine ⟨fun x y => ?_⟩
  rw [← sub_eq_zero]
  by_contra hq
  obtain ⟨w, hw⟩ := exists_ne (0 : W')
  obtain ⟨v, hv⟩ := hsurj ((x - y) ⊗ₜ w)
  exact tmul_ne_zero' hq hw (hv.symm.trans (hΦ0 v))

theorem nontrivial_jacquet_top {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hπ : π.IsIrreducible) (h : n + 0 = n) :
    Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = false := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · rfl
    · exact Fin.elim0 y
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  haveI : Nontrivial V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible hπ
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

theorem bernsteinZelevinsky (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness := fun k _ _ _ _ =>
  ⟨GlobalTheory.BZBridge.irreducibleAdmissible hA k, GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k, GlobalTheory.SmGL.IndDual.inductionContragredient k⟩

theorem exists_quotient_jac₂ (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k)),
      0 < a ∧ IsCuspidal s.ρ ∧
        ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor s.ρ t.ρ), Function.Surjective φ := by
  classical
  let P : ℕ → Prop := fun d => 0 < d ∧ ∃ (t : ℕ) (h : d + t = n),
    Nontrivial (Jacquet π (unipRad k (two (stdSum h))))
  have hP : ∃ d, P d := ⟨n, hn, 0, rfl, nontrivial_jacquet_top π hi _⟩
  obtain ⟨ha, b, h, hJ⟩ := Nat.find_spec hP
  have hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < Nat.find hP →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))) := fun c d h' hc hca => by
    by_contra hns
    exact Nat.find_min hP hca ⟨hc, d, h', not_subsingleton_iff_nontrivial.1 hns⟩
  generalize Nat.find hP = a at ha h hJ hmin
  have hBZ := bernsteinZelevinsky hA
  have hfl : HasFiniteLength (GlobalTheory.SmGL.jac (two (stdSum h)) π) :=
    (hBZ k).2.1 _ _ _ (two (stdSum h)) V π hs (hasFiniteLength_of_isIrreducible hi)
  obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ :=
    IrrQuot.exists_irreducible_smooth_quotient _ (isSmooth_jac (two (stdSum h)) hs) hfl hJ
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k Bool (Two (Fin a) (Fin b))
    (⟨Y, τ, hτs, hτi⟩ : IrrRep _)
  let F : ∀ j : Bool, Representation ℂ (GL (Two (Fin a) (Fin b) j) k) (s j).V := fun j => (s j).ρ
  let B := GlobalTheory.JacFactor.piTensorBoolEquiv F
  let φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor (F false) (F true)) :=
    ⟨B.toLinearEquiv.toLinearMap ∘ₗ E.toLinearEquiv.toLinearMap ∘ₗ q.toLinearMap, fun g =>
      LinearMap.ext fun v => by
        show B (E (q (GlobalTheory.SmGL.jac (two (stdSum h)) π (leviTwo k _ _ g) v))) =
          extTensor (F false) (F true) g (B (E (q v)))
        have e1 : E (τ (leviTwo k _ _ g) (q v)) = piTensor F (leviTwo k _ _ g) (E (q v)) :=
          E.toIntertwiningMap.isIntertwining _ _ _ _
        have e2 := B.toIntertwiningMap.isIntertwining _ _ g (E (q v))
        rw [q.isIntertwining]
        exact (congrArg B e1).trans e2⟩
  have hφ : Function.Surjective φ :=
    B.toLinearEquiv.surjective.comp (E.toLinearEquiv.surjective.comp hq)
  haveI : Nontrivial (s true).V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible (s true).irr
  exact ⟨a, b, h, s false, s true, ha,
    isCuspidal_of_jacquet_min_left π h hmin (s false).ρ (s true).ρ (s false).smooth φ hφ, φ, hφ⟩

theorem exists_injective_comp {G A B C : Type} [Group G] [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
    [AddCommMonoid C] [Module ℂ C] {ρ₁ : Representation ℂ G A} {ρ₂ : Representation ℂ G B}
    {ρ₃ : Representation ℂ G C} (ψ : ρ₁.IntertwiningMap ρ₂) (hψ : Function.Injective ψ) (E : ρ₂.Equiv ρ₃) :
    ∃ f : ρ₁.IntertwiningMap ρ₃, Function.Injective f :=
  ⟨E.toIntertwiningMap.comp ψ, E.toLinearEquiv.injective.comp hψ⟩


set_option maxHeartbeats 4000000 in
theorem exists_embedding_of_prod₂ {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k))
    (ha : 0 < a) (hc : IsCuspidal s.ρ) (ψ : π.IntertwiningMap (prod₂ s.ρ t.ρ)) (hψ : Function.Injective ψ) :
    ∃ (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = a + b), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  have hd : ∑ i, (![IrrGL.of s.ρ s.smooth s.irr, IrrGL.of t.ρ t.smooth t.irr] i).1 = a + b :=
    Fin.sum_univ_two _
  obtain ⟨E⟩ := nonempty_prod₂_equiv_prodIrr s.ρ s.smooth s.irr t.ρ t.smooth t.irr hd
  obtain ⟨f, hf⟩ := exists_injective_comp ψ hψ E
  exact ⟨_, hd, IrrGL.isCusp_of.2 ⟨ha, hc⟩, f, hf⟩

theorem exists_embedding {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = n), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  obtain ⟨a, b, rfl, s, t, ha, hc, φ, hφ⟩ := exists_quotient_jac₂ hA π hs hi hn
  haveI : Nontrivial s.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible s.irr
  haveI : Nontrivial t.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible t.irr
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw⟩ := exists_ne (0 : s.V)
    obtain ⟨w', hw'⟩ := exists_ne (0 : t.V)
    obtain ⟨v, hv⟩ := hφ (w ⊗ₜ w')
    exact tmul_ne_zero' hw hw' hv.symm
  exact (GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V s.V t.V π s.ρ t.ρ hs hi φ hφ0).elim fun ψ hψ =>
    exists_embedding_of_prod₂ π s t ha hc ψ hψ

theorem jacquetSubLeft : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k :=
  fun hA x hx => exists_embedding hA x.rep x.2.rep.smooth x.2.rep.irr hx

end GlobalTheory.CompanionTheory.JacquetLeft

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_sub_left_of_admissible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | exact GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | (intros; apply GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProducts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProducts
noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.ProdLen

theorem prodFinLen : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], ProdFinLen F ι := by
  intro F _ _ _ _ ι _ _ α _ _ m _ _ e X _ _ σ hs hi
  have hirr : (piTensor σ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur σ hi fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible (GL (m a) F) (KO F (m a)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (X a) (σ a) (hi a)
        (GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible F (m a) (X a) (σ a) (hs a) (hi a)) φ hφ
  exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength F α ι m e _ (piTensor σ) (isSmooth_piTensor hs)
    (hasFiniteLength_of_isIrreducible hirr)

end GlobalTheory.CompanionTheory.ProdLen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_of_products : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], ProdFinLen F ι := by
  first | exact @GlobalTheory.CompanionTheory.ProdLen.prodFinLen | exact GlobalTheory.CompanionTheory.ProdLen.prodFinLen | (intros; apply GlobalTheory.CompanionTheory.ProdLen.prodFinLen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianO1PullbackFubiniStudyMetric
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Inhab

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem val_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) =
      pullRatio (prB n k) W i (h.trans ((prB n k).preimage_mono inf_le_left)) j := by
  rw [← appLE_ratioOn (φ := prB n k) (W := W) (U := chart ℤ (n k) i ⊓ chart ℤ (n k) j)
    (i := i) (j := j) inf_le_left h]
  rfl

theorem blockUnit_mul {k : Fin (m + 1)} (i j l : Bk n k) {W : (MP ℤ m n).Opens}
    (h₁ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (h₂ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) j ⊓ chart ℤ (n k) l))
    (h₃ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) l)) :
    blockUnit i j h₁ * blockUnit j l h₂ = blockUnit i l h₃ := by
  refine Units.ext ?_
  rw [Units.val_mul, val_blockUnit, val_blockUnit, val_blockUnit]
  exact pullRatio_mul_pullRatio

theorem prod_blockUnit_single {W : (MP ℤ m n).Opens} (k : Fin (m + 1)) (c c' : ∀ k, Bk n k)
    (h : ∀ k', W ≤ prB n k' ⁻¹ᵁ (chart ℤ (n k') (c k') ⊓ chart ℤ (n k') (c' k'))) :
    (∏ k', blockUnit (c k') (c' k') (h k') ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') =
      blockUnit (c k) (c' k) (h k) := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

end GlobalTheory.CompanionTheory.MPDict.Inhab
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMeasurableSetPrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

theorem eventually_measurableSet_primV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, MeasurableSet (primV σ J b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  exact Filter.Eventually.of_forall fun v => measurableSet_primV F E σ hσ M J hJ d b v

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas
end
