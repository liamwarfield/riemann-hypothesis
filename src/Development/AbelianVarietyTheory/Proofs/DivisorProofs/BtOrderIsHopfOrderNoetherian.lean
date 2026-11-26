module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PolyArch

theorem roots_eig_any (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C) (w : ℂ)
    (hw : (minpoly G.F γ).eval₂ v.embedding w = 0) : ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v γ *ᵥ x = w • x := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ (γ ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ (γ ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF (γ ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) γ)
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F γ).natDegree => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hd0 : 0 < (minpoly G.F γ).natDegree := minpoly.natDegree_pos hint
  have hpm : (minpoly G.F γ).Monic := minpoly.monic hint
  set Q := (minpoly G.F γ).map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = (minpoly G.F γ).natDegree := by rw [hQ, hpm.natDegree_map]
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF γ) (minpoly G.F γ) = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = (minpoly G.F γ).natDegree - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F γ).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel hd0]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum
    ⟨(minpoly G.F γ).natDegree - 1, by omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKCx.PolyArch

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDeg

theorem etale_morphismRestrict_of_goodCover {k : Type} [CommRing k] {X Y : Scheme.{0}}
    (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (U : X.Opens) (hG : GoodCover p π D δ U) :
    Etale (π ∣_ U) := by
  obtain ⟨hU, hπU, -, hét, -⟩ := hG
  haveI : IsAffine U := hU
  haveI : IsAffine (π ⁻¹ᵁ U) := hπU
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  refine (Scheme.Hom.appLE_congr π _ (Scheme.Opens.ι_image_top U) (V' := π ⁻¹ᵁ U) ?_
    (fun φ => RingHom.Etale φ.hom)).2 ?_
  · rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  · rw [← Scheme.Hom.app_eq_appLE]; exact hét

theorem etale_map_basicOpen {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (O : X.Opens) (hO : O = X.basicOpen g) (hle : O ≤ W) :
    (X.presheaf.map (homOfLE hle).op).hom.Etale := by
  subst hO
  have := hW.isLocalization_basicOpen g
  exact Algebra.Etale.of_isLocalizationAway g

theorem algX_comp {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X)
    (W : X.Opens) (V : Y.Opens) (h : V ≤ π ⁻¹ᵁ W) :
    ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) V =
      (π.appLE W V h).hom.comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) := by
  have e : (π ≫ p).appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) =
      p.appLE ⊤ W (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ π.appLE W V h := by
    first
      | rw [Scheme.Hom.appLE_comp_appLE]
      | (rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE])
      | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc, Scheme.Hom.naturality_assoc]; rfl)
  ext r
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, RingHom.comp_apply]
  rw [e, CommRingCat.comp_apply]

theorem etale_pullback_coords : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  intro k _ X Y p q π hπ D δ U hG W x hW hx z hzU hzW
  subst hπ
  have hE := etale_morphismRestrict_of_goodCover p π D δ U hG
  obtain ⟨hU, hπU, -⟩ := hG
  obtain ⟨f, g, hfg, hz⟩ := exists_basicOpen_le_affine_inter hU hW (π z) ⟨hzU, hzW⟩
  have hW'U : X.basicOpen f ≤ U := X.basicOpen_le f
  have hW'W : X.basicOpen f ≤ W := hfg ▸ X.basicOpen_le g
  have hW' : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hV : IsAffineOpen (π ⁻¹ᵁ X.basicOpen f) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact hπU.basicOpen _
  have hVU : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ U := fun y hy => hW'U hy
  have h : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ W := fun y hy => hW'W hy
  refine ⟨π ⁻¹ᵁ X.basicOpen f, hV, hz, h, ?_⟩

  have e1 : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) (π ⁻¹ᵁ X.basicOpen f))
      (fun a => (π.appLE W _ h).hom (x a)) =
      (π.appLE W _ h).hom.comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x) := by
    rw [MvPolynomial.comp_eval₂Hom, algX_comp p π W _ h]
  rw [e1]
  refine RingHom.Etale.stableUnderComposition _ _ hx ?_

  have e2 : π.appLE W (π ⁻¹ᵁ X.basicOpen f) h =
      X.presheaf.map (homOfLE hW'W).op ≫ π.appLE (X.basicOpen f) (π ⁻¹ᵁ X.basicOpen f) le_rfl := by
    rw [Scheme.Hom.map_appLE]
  rw [e2, CommRingCat.hom_comp]
  refine RingHom.Etale.stableUnderComposition _ _ (etale_map_basicOpen hW g _ hfg hW'W) ?_

  have ha : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen f) :=
    hW'.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'U)
  have hb : IsAffineOpen ((π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f)) :=
    hV.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hVU)
  have e3 : (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f) ≤ (π ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ X.basicOpen f) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have := HasRingHomProperty.appLE @Etale (π ∣_ U) hE ⟨_, ha⟩ ⟨_, hb⟩ e3
  rw [morphismRestrict_appLE] at this
  refine (Scheme.Hom.appLE_congr π _ ?_ ?_ (fun φ => RingHom.Etale φ.hom)).1 this
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hW'U
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hVU

end GlobalTheory.CoverDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCoverStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_etale_pullback_coordinates_goodCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  first | exact @GlobalTheory.CoverDeg.etale_pullback_coords | exact GlobalTheory.CoverDeg.etale_pullback_coords | (intros; apply GlobalTheory.CoverDeg.etale_pullback_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjModelExt
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjExt

open GlobalTheory.ConjDS GlobalTheory.LowTypeDetermined

section Gen

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realMap (T : H ≃ₗᵢ⋆[ℂ] H') : H →L[ℝ] H' where
  toFun := T
  map_add' := map_add T
  map_smul' r x := by
    rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
  cont := T.continuous

theorem smoothVec_map (T : H ≃ₗᵢ⋆[ℂ] H') (h : ∀ g v, T (σ g v) = σ' g (T v)) {L : Set (Matrix (Fin n) (Fin n) ℂ)}
    {w : H} (hw : SmoothVec L σ w) : SmoothVec L σ' (T w) := by
  intro k Xs hX
  simp only [← h]
  exact (realMap T).contDiff.comp (hw k Xs hX)

theorem lowKSub_stab {lam : Fin n → ℝ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) {w : H}
    (hw : w ∈ lowKSub ε lam σ) : σ g w ∈ lowKSub ε lam σ := by
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => (le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS) (hS.2.1 g hg x hx)
  exact this hw

theorem lowKSub_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    {lam : Fin n → ℝ} {w : H} (hw : w ∈ lowKSub ε lam σ) : T.symm w ∈ lowKSub ε' (nr lam) σ' := by
  have : lowKSub ε lam σ ≤ (lowKSub ε' (nr lam) σ').comap (T.symm.toLinearEquiv : H →ₗ⋆[ℂ] H') := by
    refine sSup_le fun S hS x hx => ?_
    have h1 := ktype_transfer (sg_symm he) T.symm (symm_inter T h) hS
    rw [← lowK_rev he] at h1
    refine (le_sSup (s := {S | IsKTypeOf ε' σ' (Formalism.QuantumDeterminants.lowK ε' (nr lam)) S}) h1) ?_
    show T (T.symm x) ∈ S
    simpa using hx
  exact this hw

def prm (ε ε' : Fin n → Bool) : Equiv.Perm (Fin n) :=
  ((Fin.revPerm.trans (revNeg ε')).trans Fin.revPerm).trans (revNeg ε).symm

theorem revNeg_prm (a : Fin n) : revNeg ε (prm ε ε' a) = (revNeg ε' a.rev).rev := by
  simp [prm]

theorem eps_prm (he : ∀ a, ε' a = ε a.rev) (a : Fin n) : ε (prm ε ε' a) = ε a := by
  rw [← eps_revNeg ε (prm ε ε' a), revNeg_prm, ← he (revNeg ε' a.rev), eps_revNeg ε' a.rev, he, Fin.rev_rev]

theorem ext_transfer (he : ∀ a, ε' a = ε a.rev) (T : H' ≃ₗᵢ⋆[ℂ] H) (h : ∀ g v, T (σ' g v) = σ (rv g) (T v))
    (hU : IsURepOn (UJset ε) σ) {lam : Fin n → ℝ} {w : H}
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w) :
    IsWtOn (Formalism.REAL.Kset ε') σ' (fun a => Formalism.QuantumDeterminants.lowK ε' (nr lam) (revNeg ε' a))
      (T.symm (σ (pM (prm ε ε')) w)) := by
  have h1 := wt_transfer (sg_symm he) T.symm (symm_inter T h) (isWtOn_perm hU (prm ε ε') (eps_prm he) hw)
  convert h1 using 1
  funext a
  rw [lowK_rev he]
  simp [nr, revNeg_prm]

end Gen

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem conj_rep (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : (conjModel M).H τ) :
    cj (M.H τ) ((conjModel M).rep τ g w) = M.rep τ g (cj (M.H τ) w) := by
  have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
    rw [inv_submatrix_equiv]
    have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (M.fr τ * g * (M.fr τ)⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  show M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
      ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj _ w) = M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj _ w)
  rw [e]

theorem smooth_translate (M : DSModel V S) (τ : D.what₂.Tau) (u : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : SmoothVec (lieAt V τ) (M.rep τ) (M.σ τ g u) := by
  obtain ⟨_, -, hσ, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  have hu' : (u : M.H τ) ∈ smooth (gramAt D V τ) (M.rep τ) := hs ▸ u.2
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact translate_mem (isUnit_gram hP h) (isURepOn_conj hσ hP h) (conj_inv_mem hP h hg) hu'

theorem exists_conjModel_ext : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v : M.Vec), IsExtVec M v → ∃ (M' : DSModel V (fun τ => dualPar (S τ))) (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (v' : M'.Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, c τ (M'.rep τ g y) = M.rep τ g (c τ y)) ∧ IsExtVec M' v' := by
  intro D V S M v hv
  have he : ∀ τ a, (conjModel M).ε τ a = M.ε τ a.rev := fun _ _ => rfl
  have hK := fun τ => pM_mem (prm (M.ε τ) ((conjModel M).ε τ)) (eps_prm (he τ))
  have hU : ∀ τ, IsURepOn (UJset (M.ε τ)) (M.σ τ) := fun τ => (M.ds τ).2.2.1
  let c : ∀ τ, (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := fun τ => cj (M.H τ)
  have hc : ∀ τ g y, c τ ((conjModel M).σ τ g y) = M.σ τ (rv g) (c τ y) := fun _ _ _ => rfl
  have hr : ∀ τ g y, (c τ).symm (M.rep τ g y) = (conjModel M).rep τ g ((c τ).symm y) := fun τ g y => by
    apply (c τ).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (conj_rep M τ g _).symm
  refine ⟨conjModel M, c, fun τ => ⟨(c τ).symm (M.σ τ (pM (prm (M.ε τ) ((conjModel M).ε τ))) (v τ)),
    Submodule.subset_span (smoothVec_map (c τ).symm (hr τ) (smooth_translate M τ (v τ) (kset_uj (hK τ))))⟩,
    fun τ g _ y => conj_rep M τ g y, fun τ => ⟨?_, ?_, ?_⟩⟩
  · rw [LinearIsometryEquiv.norm_map, (hU τ).2.1 _ (kset_uj (hK τ)), (hv τ).1]
  · exact lowKSub_transfer (he τ) (c τ) (hc τ) (lowKSub_stab (hK τ) (hv τ).2.1)
  · exact ext_transfer (he τ) (c τ) (hc τ) (hU τ) (hv τ).2.2

end GlobalTheory.ConjExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalCoordsEqPosMulAdeleHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalCoordsEqPosMulAdeleHaar
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagFormGlue

open GlobalTheory.DiagForm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  change (eI F κ).symm (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i))) = p.1
  simp only [RingEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem glue_shiftOf (x : κ → AdeleRing (𝓞 F) F) : glue (shiftOf x) = x := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ ((eI F κ).symm _) i) = (x i).1
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact RingEquiv.symm_apply_apply _ _

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  conv_lhs => rw [← shiftOf_glue q]
  exact glue_add_shiftOf p (glue q)

theorem ringEquiv_symm_eq :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace F).symm := by
  funext z
  apply (GroundTheory.Global.homeomorphMixedSpace F).injective
  rw [Homeomorph.apply_symm_apply, GroundTheory.Global.homeomorphMixedSpace_apply, RingEquiv.apply_symm_apply]

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) := by
  refine continuous_pi fun i => ?_
  show Continuous fun p : Vi F κ × Vf F κ =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i), p.2 i) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [ringEquiv_symm_eq]
  exact ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp
    ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AdeleRing (𝓞 F) F) → Vi F κ × Vf F κ) := by
  refine Continuous.prodMk ((eI F κ).symm.continuous.comp (continuous_pi fun i => ?_))
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  show Continuous fun x : κ → AdeleRing (𝓞 F) F => GroundTheory.Global.homeomorphMixedSpace F (x i).1
  exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))


variable (F κ) in
def glueEquiv : (Vi F κ × Vf F κ) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := glue_add

theorem exists_glue_measure :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    ∃ c : NNReal, 0 < c ∧ (mu F κ).map glue = c • (adeleMeasurePi F (ι := κ)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance
  haveI : ((mu F κ).map (glueEquiv F κ)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map _ (glueEquiv F κ) continuous_glue continuous_shiftOf
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueEquiv F κ)) (adeleMeasurePi F (ι := κ))
  refine ⟨_, ?_, h⟩
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_smul] at h
  exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := (mu F κ).map (glueEquiv F κ))).open_pos
    Set.univ isOpen_univ Set.univ_nonempty (by rw [h]; rfl)


variable (F κ) in
def glueMEquiv :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    (Vi F κ × Vf F κ) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  (Homeomorph.mk (glueEquiv F κ).toEquiv continuous_glue continuous_shiftOf).toMeasurableEquiv

end GlobalTheory.DiagFormGlue

namespace GlobalTheory

theorem diagForm_glue_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ H : (κ → AF F) → ℂ, (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔
      Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := by
  intro F _ _ κ _
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  obtain ⟨c, hc, hmap⟩ := DiagFormGlue.exists_glue_measure (F := F) (κ := κ)
  have hmap' : (GlobalTheory.DiagForm.mu F κ).map (DiagFormGlue.glueMEquiv F κ) = c • adeleMeasurePi F (ι := κ) := hmap
  refine ⟨c, hc, fun H => ⟨?_, ?_⟩⟩
  · rw [← (integrable_smul_measure (f := H) (μ := adeleMeasurePi F (ι := κ)) (c := (c : ENNReal))
      (by exact_mod_cast hc.ne') ENNReal.coe_ne_top)]
    have e2 : (c : ENNReal) • adeleMeasurePi F (ι := κ) = c • adeleMeasurePi F (ι := κ) := rfl
    rw [e2, ← hmap', integrable_map_equiv]
    rfl
  · have h1 := integral_map_equiv (μ := GlobalTheory.DiagForm.mu F κ) (DiagFormGlue.glueMEquiv F κ) H
    rw [hmap', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h1
    exact h1.symm
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalCoordsEqPosMulAdeleHaarStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_diagonalCoords_eq_pos_mul_adeleHaar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ H : (κ → AF F) → ℂ, (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧ ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := by
  first | exact @GlobalTheory.diagForm_glue_integral | exact GlobalTheory.diagForm_glue_integral | (intros; apply GlobalTheory.diagForm_glue_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharacterTrivialOnPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharacterTrivialOnPrincipalLevel
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MuLevel

theorem det_cong_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : N ≠ 0) (k : GA D V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ w ∈ intAE D, (finHom V k).1.det - 1 = N • w := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  rw [hL] at hk
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F L hfg hsp N hN _ hk


set_option maxHeartbeats 1000000 in
theorem exists_root_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : Odd N) (k : GA D V) (hf : k ∈ GfC V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ x : (AE D)ˣ, IsDetRoot V k x ∧ FinUnit x ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y := by
  obtain ⟨w, hw, hwe⟩ := det_cong_of_level V N hN.pos.ne' k hk
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.OddRoot.exists_root_odd D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ?_, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, p, hp, hY2 ▸ hpe⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have h1 : infHom V k = 1 := hf
  have hs : infPart D (sigR (AF D.host.F) D.sp.cm.sig (Y : AE D)) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (Y : AE D)) := GlobalTheory.DetRootCong.map_sigR _ _ _
  refine e.injective (Prod.ext ?_ ?_)
  · rw [he1, he1, RingHom.map_mul, hs, ← hdet', h1, hY1, RingHom.map_one, mul_one]
    exact Matrix.det_one.symm
  · have hs' := GlobalTheory.DetRootCong.finPart_sigR D (Y : AE D)
    rw [hY2] at hs'
    rw [hdet, ← hs', ← RingHom.map_mul] at hroot
    exact (he2 _).trans ((hY2.trans hroot).trans (he2 _).symm)

theorem exists_ext {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : K →+* ℂ) :
    ∃ τ : L →+* ℂ, τ.comp (algebraMap K L) = σ := by
  letI : Algebra K ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩


set_option maxHeartbeats 1000000 in
theorem mu_eq_one_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k ∈ T.Kf ((i : ℕ) + 1) σ, T.mu ((i : ℕ) + 1) σ k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL h _ i σ hσ _ k hk
  have hj := inR i
  obtain ⟨τ, rfl⟩ := exists_ext (L := D.what₂.LL) σ
  obtain ⟨hf, hk'⟩ := (h.laws.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := h.laws.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨x, hx, hu, hc⟩ := exists_root_of_level _ _ hodd k hf hk'
  have hm := R.C.isMu0 i
  have h1 : R.mu0 ((i : ℕ) + 1) x = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hL.mu0 i) hm.tame _ (fun P hP => hm.unr P fun a ha => hP ?_) x hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  obtain ⟨y, hy1, hy2⟩ := (h.chiR i τ hσ).2.2.2.1 x hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL y = 1 :=
    D.what₂.embLL.injective (by rw [← hy1, h1, map_one, Circle.coe_one])
  rw [(h.laws.muVal _ hj _ hσ).2 k x hx, hy2, h2, map_one]

end GlobalTheory.MuLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharacterTrivialOnPrincipalLevelStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_character_trivial_on_principal_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k ∈ T.Kf ((i : ℕ) + 1) σ, T.mu ((i : ℕ) + 1) σ k = 1 := by
  first | exact @GlobalTheory.MuLevel.mu_eq_one_of_mem_level | exact GlobalTheory.MuLevel.mu_eq_one_of_mem_level | (intros; apply GlobalTheory.MuLevel.mu_eq_one_of_mem_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwin
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.SmoothMultilinear

theorem conj_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Mt V.rank} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 := M.fr_gram τ
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
        rw [h1, hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2]; simp

theorem rep_one {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem rep_mul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {a b : Mt V.rank} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (a * b) = M.rep τ a * M.rep τ b := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  unfold DSModel.rep
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹) := by
    calc _ = M.fr τ * a * ((M.fr τ)⁻¹ * M.fr τ) * b * (M.fr τ)⁻¹ := by
          rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)

theorem prod_mem {n : ℕ} (H : Mt n) (l : List (Mt n)) (hl : ∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH H) :
    l.prod ∈ Formalism.QuantumDeterminants.UH H := by
  induction l with
  | nil => show (1 : Mt n)ᴴ * H * 1 = H; simp
  | cons a l ih =>
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul _ _ _ (hl a (by simp)) (ih fun g hg => hl g (by simp [hg]))

theorem exp_mem {n : ℕ} (H X : Mt n) (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  apply CCRuleCW.exp_mem_UH
  have := CCRuleCW.lie_smul H X hX t
  rwa [Complex.coe_smul] at this

theorem smooth_of_span {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : v ∈ Submodule.span ℂ {w | SmoothVec L σ w}) :
    SmoothVec L σ v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro k Xs _; simp only [map_zero]; exact contDiff_const
  | add x y _ _ hx hy => intro k Xs h; simp only [map_add (f := _)]; exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx => intro k Xs h; simp only [map_smul]; exact (hx k Xs h).const_smul c

theorem hasDerivAt_of_smooth {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : SmoothVec L σ v) (X : Mt n) (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h := hv 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := h.comp h2
  have h4 : ContDiff ℝ ∞ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) := by
    convert h3 using 2
    simp
  exact (h4.differentiable (by simp) 0).hasDerivAt

theorem act_list {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y))
    (y : ∀ τ, M.H τ) (l : List (D.what₂.Tau × Mt V.rank))
    (hl : ∀ p ∈ l, p.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V p.1)) :
    ρ (l.map fun p => atTau θ V p.1 p.2).prod (Φ y) =
      Φ fun τ => M.rep τ (l.map fun p => if p.1 = τ then p.2 else 1).prod (y τ) := by
  induction l with
  | nil => simp [rep_one]
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1) := fun q hq => hl q (by simp [hq])
    rw [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl',
      ← h p.1 p.2 (hl p (by simp))]
    congr 1
    funext τ
    rw [List.map_cons, List.prod_cons]
    by_cases e : p.1 = τ
    · subst e
      rw [Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]
      apply prod_mem
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      split_ifs with e
      · exact e ▸ hl' q hq
      · exact prod_mem _ [] (by simp)
    · rw [Function.update_of_ne (Ne.symm e), if_neg e, one_mul]

theorem smooth_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  intro D θ V _ S M K _ _ ρ Φ h v
  have hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) := fun τ => smooth_of_span _ _ _ (v τ).2
  refine ⟨?_, ?_⟩
  · intro k τs Xs hX
    have e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (Φ fun τ => (v τ : M.H τ))) =
        fun t : Fin k → ℝ => Φ fun τ => M.rep τ
          (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ) := by
      funext t
      have := act_list θ M ρ Φ h (fun τ => (v τ : M.H τ))
        (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by
          intro p hp
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
          exact exp_mem _ _ (hX i) _)
      simp only [List.map_ofFn] at this
      refine this.trans ?_
      congr 1
      funext τ
      congr 4
      funext i
      dsimp only [Function.comp_apply, Prod.fst, Prod.snd]
      split_ifs <;> simp
    rw [e]
    have hΦ : ContDiff ℝ ∞ (Φ : (∀ τ, M.H τ) → K) := (Φ.contDiff (n := ∞)).restrict_scalars ℝ
    refine hΦ.comp (contDiff_pi.2 fun τ => ?_)
    refine hs τ k _ fun i => ?_
    split_ifs with e
    · exact e ▸ hX i
    · simp [lieAt]
  · intro τ X hX
    have e : (fun t : ℝ => ρ (oneP θ V τ X t) (Φ fun τ => (v τ : M.H τ))) =
        fun t : ℝ => (Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ)
          (M.rep τ (NormedSpace.exp (t • X)) (v τ)) := by
      funext t
      exact (h τ _ (exp_mem _ _ hX t) _).symm
    unfold dL2
    simp only
    rw [e]
    have h1 := hasDerivAt_of_smooth _ _ _ (hs τ) X hX
    exact (((Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1).deriv

end GlobalTheory.SmoothMultilinear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwinStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  first | exact @GlobalTheory.SmoothMultilinear.smooth_map | exact GlobalTheory.SmoothMultilinear.smooth_map | (intros; apply GlobalTheory.SmoothMultilinear.smooth_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointInjectiveOnPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjPart

theorem adjoint_injective_on_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks), (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R hP hB p w hw h0
  have h2 := hB A3.A.μ0 p w hw
  rw [LinearMap.comp_apply, h0, map_zero, Formalism.IndefR.Links.RealDat3.prod_lamN] at h2
  have hpos : 0 < R.kap * ∏ j : Fin D.R.m, R.lam3 j A3.A.μ0 p A3.A.v0 :=
    mul_pos hP.1 (Finset.prod_pos fun j _ => hP.2 j A3.A.μ0 p)
  have hne : ((R.kap * ∏ j : Fin D.R.m, R.lam3 j A3.A.μ0 p A3.A.v0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact (smul_eq_zero.1 h2.symm).resolve_left hne

end GlobalTheory.AdjPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqIteratePrimeCharP
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem derivation_iterate_leibniz {R : Type} [CommRing R] (D : Derivation ℤ R R) (a b : R) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : R) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : (n.choose ij.2 : R) = (n.choose ij.1 : R) := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFormsEqBotOfLtCard
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem _root_.GlobalTheory.LogDR.spanForms_eq_bot_of_lt_card : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ)
    (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ), _root_.GlobalTheory.LogDR.IsCoord x → n < a →
    _root_.GlobalTheory.LogDR.spanForms M H a = ⊥ := by
  intro K _ n x M H a hx hlt
  obtain ⟨hli, hsp⟩ := hx
  let b := Module.Basis.mk hli hsp.ge
  haveI : FiniteDimensional K Ω[K⁄ℤ] := Module.Finite.of_basis b
  have hr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  unfold _root_.GlobalTheory.LogDR.spanForms
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro η ⟨c, -, v, -, rfl⟩
  have hdep : ¬ LinearIndependent K v := fun hv => by
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, hr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ _ hdep, smul_zero]
  rfl

end GlobalTheory.LogDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

variable (ι : Type) [Fintype ι] (P Q R S : ℕ)

def degLE (k : ℕ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {T | ∃ f : ι → Formalism.BasicNotions.TH.Pol P Q R S, ∑ w, (f w).totalDegree ≤ k ∧ T = PiTensorProduct.tprod ℂ f}

def chiPart [DecidableEq ι] (x : ι → ℚ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ w : ι, ⨅ X : {X : Mat P Q // IsKC X},
    LinearMap.ker (atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X.1) - ((x w : ℂ) * X.1.trace) • 1)

variable {ι P Q R S}

theorem mem_chiPart [DecidableEq ι] (x : ι → ℚ) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :
    T ∈ chiPart ι P Q R S x ↔ ∀ w (X : Mat P Q), IsKC X →
      atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X) T = ((x w : ℂ) * X.trace) • T := by
  simp only [chiPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

theorem degLE_mono : Monotone (degLE ι P Q R S) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨f, hf, e⟩ => ⟨f, hf.trans h, e⟩

theorem tprod_mem_degLE (f : ι → Formalism.BasicNotions.TH.Pol P Q R S) {k : ℕ} (h : ∑ w, (f w).totalDegree ≤ k) :
    PiTensorProduct.tprod ℂ f ∈ degLE ι P Q R S k :=
  Submodule.subset_span ⟨f, h, rfl⟩

end GlobalTheory.KFixIrr

end
end
