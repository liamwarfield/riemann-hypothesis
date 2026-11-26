module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem isHolFam_pullback_lift : ∀ (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (N : ℕ) (e₁ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₂)) (u : Sp ℂ ⟶ X) (h₁ : ∀ z, e₁ z ≫ p₁ = u) (h₂ : ∀ z, e₂ z ≫ p₂ = u), IsHolFam e₁ → IsHolFam e₂ → IsHolFam (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm)) := by
  intro X Y₁ Y₂ p₁ p₂ N e₁ e₂ u h₁ h₂ hol₁ hol₂
  have ea : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) = e₁ :=
    funext fun z => pullback.lift_fst _ _ _
  have eb : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) = e₂ :=
    funext fun z => pullback.lift_snd _ _ _
  have ha : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) := by
    rw [ea]
    intro U f
    simpa using hol₁ U f
  have hb : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) := by
    rw [eb]
    intro U f
    simpa using hol₂ U f
  have hc := GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback p₁ p₂) ha hb
  intro U f
  simpa using hc U f

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolFam_pullback_lift_of_common_base : ∀ (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (N : ℕ) (e₁ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₂)) (u : Sp ℂ ⟶ X) (h₁ : ∀ z, e₁ z ≫ p₁ = u) (h₂ : ∀ z, e₂ z ≫ p₂ = u), IsHolFam e₁ → IsHolFam e₂ → IsHolFam (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm)) := by
  first | exact @GlobalTheory.AnVal.isHolFam_pullback_lift | exact GlobalTheory.AnVal.isHolFam_pullback_lift | (intros; apply GlobalTheory.AnVal.isHolFam_pullback_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetLinSub

theorem tay_coord {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).contDiff.contDiffAt
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_tay, TM.mD_zero]
    simp
  · obtain ⟨⟨a, j⟩, hp⟩ : ∃ p, n p ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + Finsupp.single ((0 : Fin 1), j) 1 :=
      ⟨n - Finsupp.single ((0 : Fin 1), j) 1, (tsub_add_cancel_of_le
        (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hp))).symm⟩
    have h1 := TM.pderiv_tay hθ j
    have h2 : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j 1 : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      exact congrArg (fun T : (Fin N → ℂ) →L[ℂ] ℂ => T (Pi.single j 1)) this
    rw [h2, TM.tay_const] at h1
    have h3 : MvPowerSeries.pderiv (R := ℂ) ((0 : Fin 1), j) (MvPowerSeries.X ((0 : Fin 1), k) :
        MvPowerSeries (Fin 1 × Fin N) ℂ) = MvPowerSeries.C ((Pi.single j 1 : Fin N → ℂ) k) := by
      rw [MvPowerSeries.pderiv_X]
      by_cases h : k = j
      · subst h; simp
      · simp [Prod.ext_iff, h]
    have h4 := congrArg (MvPowerSeries.coeff n') (h1.trans h3.symm)
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv] at h4
    exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero _) h4

theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetOf_coord {N : ℕ} (m : ℕ) (k : Fin N) :
    jetOf m (fun v : Fin N → ℂ => v k) = Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k)) := by
  rw [jetOf, tay_coord, psJet_X]

def flatL {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) :
    (Fin (n' * g) → ℂ) →L[ℂ] (Fin (n * g) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v k => B (colsOf n' g v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      map_add' := fun v w => by
        funext k
        have : colsOf n' g (v + w) = colsOf n' g v + colsOf n' g w := rfl
        rw [this, map_add (f := _)]; rfl
      map_smul' := fun c v => by
        funext k
        have : colsOf n' g (c • v) = c • colsOf n' g v := rfl
        rw [this, map_smul]; rfl }

theorem flatL_apply {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (v : Fin (n' * g) → ℂ)
    (k : Fin (n * g)) :
    flatL B v k = B (colsOf n' g v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

theorem colsOf_flatL {n n' g : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (v : Fin (n' * g) → ℂ) :
    colsOf n g (flatL B v) = B (colsOf n' g v) := by
  funext i j
  show flatL B v (finProdFinEquiv (i, j)) = _
  rw [flatL_apply, Equiv.symm_apply_apply]

theorem subst_renN {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (a : Jet ℂ (Fin 1 × Fin (n * g)) m) :
    σ (renN n g m a) = renN n' g m (jetMap (anLin (flatL B)) (anLin_mem _) a) := by
  have key : (σ.comp (renN n g m)).comp (Ideal.Quotient.mkₐ ℂ _) =
      ((renN n' g m).comp (jetMap (m := m) (anLin (flatL B)) (anLin_mem _))).comp (Ideal.Quotient.mkₐ ℂ _) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, k⟩
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have e1 : renN n g m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k))) =
        psJet m (MvPowerSeries.X (finProdFinEquiv.symm k)) := by
      rw [psJet_X]
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
      rw [MvPolynomial.aeval_X]
    have hθ : ContDiffAt ℂ ω (fun v : Fin (n * g) → ℂ => v k) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) k).contDiff.contDiffAt
    have e2 := jetOf_comp_anLin m hθ (flatL B)
    rw [jetOf_coord] at e2
    show σ (renN n g m (Ideal.Quotient.mk _ _)) =
      renN n' g m (jetMap (m := m) (anLin (flatL B)) (anLin_mem _) (Ideal.Quotient.mk _ _))
    rw [e1, hσ, ← e2]
    rfl
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact DFunLike.congr_fun key p

theorem subst_jetN {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (f : (Fin n → Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0) :
    σ (jetN m f) = jetN m (fun w => f (B w)) := by
  rw [jetN, subst_renN B σ hσ, ← jetOf_comp_anLin m hf (flatL B), jetN]
  congr 2
  funext v
  rw [Function.comp_apply, colsOf_flatL]

theorem isHolFam_clm {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) : IsHolFam (fun v => e (T v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage T.continuous, h2.comp T.differentiable.differentiableOn fun _ hv => hv⟩

theorem jetPt_clm {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) (e' : (Fin N' → ℂ) → (Sp ℂ ⟶ Y)) (hol' : IsHolFam e')
    (he : ∀ v, e' v = e (T v)) (m : ℕ) :
    spMap ((jetMap (anLin T) (anLin_mem T) : Jet ℂ (Fin 1 × Fin N) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin N') m) :
      Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ (Fin 1 × Fin N') m) ≫ jetPt e hol m = jetPt e' hol' m := by
  obtain rfl : e' = fun v => e (T v) := funext he
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin T) (anLin_mem T)
  refine jetPt_precompD _ _ hol hol' (by show e (T 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) T).symm

set_option backward.isDefEq.respectTransparency false in
theorem spMap_closedPoint {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R')
    (hf : IsLocalHom f) : spMap f (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
  IsLocalRing.comap_closedPoint f

theorem appTop_toΓ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    ((spMap f).appTop).hom (toΓ R a) = toΓ R' (f a) := by
  simp only [toΓ, spMap]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem res_pull {Y Z : Scheme.{0}} (s : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : ⊤ ≤ W) (h' : ⊤ ≤ W')
    (le : W' ≤ s ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (Z.presheaf.map (homOfLE h').op).hom ((Z.presheaf.map (homOfLE le).op).hom ((s.app W).hom x)) =
      s.appTop.hom ((Y.presheaf.map (homOfLE h).op).hom x) := by
  obtain rfl : W = ⊤ := top_le_iff.1 h
  obtain rfl : W' = ⊤ := top_le_iff.1 h'
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  have e1 : Y.presheaf.map (homOfLE h).op = 𝟙 _ := Y.presheaf.map_id _
  have e2 : Z.presheaf.map ((homOfLE le).op ≫ (homOfLE h').op) = 𝟙 _ := Z.presheaf.map_id _
  rw [e1, e2]
  rfl

section Main

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem jetMap_sub {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetMap m ψ Λ) :
    Φ.JetMap m (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ ψ) (Λ ∘ₗ B) := by
  obtain ⟨hol, rfl⟩ := h
  have he : ∀ v : Fin (n' * g) → ℂ, (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left =
      (Φ.e (Λ (colsOf n g (flatL B v)))).left := fun v => by rw [colsOf_flatL]; rfl
  have hol' : IsHolFam (fun v : Fin (n' * g) → ℂ => (Φ.e ((Λ ∘ₗ B) (colsOf n' g v))).left) := by
    rw [funext he]
    exact isHolFam_clm _ hol (flatL B)
  refine ⟨hol', ?_⟩
  rw [← jetPt_clm _ hol (flatL B) _ hol' he m, ← Category.assoc, ← Category.assoc, ← anSpMap_comp, ← anSpMap_comp]
  congr 2
  exact RingHom.ext fun a => subst_renN B σ hσ a

theorem jetMap_closedPoint {n m : ℕ} (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : Φ.JetMap m ψ Λ) :
    ψ (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = (Φ.e 0).left PullbackSections.cpt := by
  obtain ⟨hol, rfl⟩ := h
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  refine (congrArg _ (spMap_closedPoint _ (isLocalHom_jetMap _ _))).trans ?_
  refine (jetPt_closedPoint _ hol m).trans ?_
  have : Λ (colsOf n g 0) = 0 := map_zero Λ
  simp only [this]

theorem contDiffAt_fr {n : ℕ} (j : L.L.ι) (hj : (Φ.e 0).left PullbackSections.cpt ∈ L.L.U j) (a : ℤ)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    ContDiffAt ℂ ω (fun v : Fin (n * g) → ℂ => Φ.fr j (Λ (colsOf n g v)) ^ a) 0 := by
  have h0 := top_le_of_mem hj
  have h1 : AnalyticAt ℂ (Φ.fr j) 0 :=
    ReciprocityTheory.AnForm.Osgood.osgood g _ _ (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) 0 h0
  have h2 : AnalyticAt ℂ (fun z => Φ.fr j z ^ a) 0 := h1.fun_zpow (Φ.fr_ne j 0 h0)
  let T : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap
    (Λ ∘ₗ { toFun := colsOf n g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
  have h3 : AnalyticAt ℂ (fun z => Φ.fr j z ^ a) (T 0) := by rw [map_zero]; exact h2
  exact (h3.comp (T.analyticAt 0)).contDiffAt

theorem jetRd_sub {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    {K : Type} [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetRd m φ ε τ Λ) :
    Φ.JetRd m (fun k => spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε
      (LB.pullGen L.L φ ε τ (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m)))
      (fun k => Λ k ∘ₗ B) := by
  obtain ⟨h1, h2⟩ := h
  have h1' := fun k => jetMap_sub Φ B σ hσ (φ k) (Λ k) (h1 k)
  refine ⟨h1', fun j hj => ?_⟩
  have hU : ∀ k, (Φ.e 0).left PullbackSections.cpt ∈ L.L.U (j k) := fun k => by
    rw [← jetMap_closedPoint Φ _ _ (h1' k)]
    exact (hj.trans (LB.wchart_le _ _ j k)) (Set.mem_univ _)
  have hj0 : ⊤ ≤ LB.wchart L.L φ j := by
    intro y _
    refine Set.mem_iInter.2 fun k => ?_
    have hk : φ k (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) ∈ L.L.U (j k) := by
      rw [jetMap_closedPoint Φ _ _ (h1 k)]; exact hU k
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (Jet ℂ (Fin n × Fin g) m)) (φ k) hk).ge
      (Set.mem_univ y)
  refine (res_pull _ _ _ hj0 hj _ (τ.s j).val).trans ?_
  rw [h2 j hj0, appTop_toΓ]
  congr 1
  exact subst_jetN B σ hσ _ (contDiffAt_prod fun k _ => contDiffAt_fr Φ (j k) (hU k) (ε k) (Λ k))

end Main

theorem jetRd_linSubst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n n' m : ℕ) (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ), (∀ p, (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2)) → ∀ (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m (fun k => spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε (LB.pullGen L.L φ ε τ (spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m))) (fun k => Λ k ∘ₗ B) := by
  intro S A _ _ L x0 g Φ n n' m B sb hsb K _ φ ε τ Λ h
  exact jetRd_sub Φ B (jetSubstP m sb) hsb φ ε τ Λ h

end GlobalTheory.JetLinSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetReading_linearSubstitution_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n n' m : ℕ) (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ), (∀ p, (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2)) → ∀ (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m (fun k => spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε (LB.pullGen L.L φ ε τ (spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m))) (fun k => Λ k ∘ₗ B) := by
  first | exact @GlobalTheory.JetLinSub.jetRd_linSubst | exact GlobalTheory.JetLinSub.jetRd_linSubst | (intros; apply GlobalTheory.JetLinSub.jetRd_linSubst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppLESpMapJetPt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnValJetGlob


set_option backward.isDefEq.respectTransparency false in
theorem appLE_spMap_jetPt {N m : ℕ} {I : Type} {Z : Scheme.{0}} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q)
    (χ : Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ I m) [IsLocalHom χ] (U : Z.Opens)
    (h : ⊤ ≤ (spMap χ ≫ jetPt q hq m) ⁻¹ᵁ U) :
    q 0 cpt ∈ U ∧ ∀ f : Γ(Z, U), (spMap χ ≫ jetPt q hq m).appLE U ⊤ h f =
      toΓ _ (χ (jetOf m fun v => valAt' (q v) U f)) := by
  have hU : q 0 cpt ∈ U := by
    have : (spMap χ ≫ jetPt q hq m) (IsLocalRing.closedPoint _) ∈ U :=
      h (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [Scheme.Hom.comp_apply, spMap, Spec_closedPoint, jetPt_closedPoint] at this
  refine ⟨hU, fun f => ?_⟩
  have hp : ⊤ ≤ jetPt q hq m ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (jetPt q hq m) (by rw [jetPt_closedPoint]; exact hU)).ge
  have k := specMap_comp_appLE (CommRingCat.ofHom χ) (jetPt q hq m) U h hp
  rw [jetPt_appLE q hq m U hU hp, Category.assoc, Iso.inv_hom_id_assoc, ← Iso.eq_comp_inv] at k
  have k' := ConcreteCategory.congr_hom k f
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, jetψ_apply] at k'
  exact k'


set_option backward.isDefEq.respectTransparency false in
theorem jetRd_pullGen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (q : (Fin (n * g) → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q), (∀ v, Φ.GenRd φ ε t (q v) (fun k => Λ k (colsOf n g v)) 1) → Φ.JetRd m (fun k => (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m) ≫ φ k) ε (LB.pullGen L.L φ ε t (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m)) Λ := by
  intro S A _ _ L x0 g Φ n m Z K _ φ ε t Λ q hq H
  refine ⟨fun k => ?_, fun j h => ?_⟩
  · have he : ∀ v, q v ≫ φ k = (Φ.e (Λ k (colsOf n g v))).left := fun v => (H v).1 k
    have hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ k (colsOf n g v))).left) := by
      have h := isHolFam_comp q hq (φ k)
      rwa [show (fun v => q v ≫ φ k) = fun v => (Φ.e (Λ k (colsOf n g v))).left from funext he] at h
    refine ⟨hol, ?_⟩
    beta_reduce
    rw [Category.assoc, jetPt_comp q hq (φ k) _ hol he]
  · have : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) :=
      isLocalHom_jetMap (K := ℂ) (m := m) _ _
    have h' : ⊤ ≤ (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt q hq m) ⁻¹ᵁ LB.wchart L.L φ j := by
      intro x hx
      have hx' := h hx
      simp only [LB.wchart] at hx' ⊢
      exact Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx' k
        simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using this
    obtain ⟨hU, hf⟩ := appLE_spMap_jetPt q hq _ _ h'
    have hj : jetOf m (fun v => valAt' (q v) (LB.wchart L.L φ j) (t.s j).val) =
        jetOf m (fun v => ∏ k, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) := by
      refine jetOf_congr m ((eventually_mem q hq hU).mono fun v hv => ?_)
      have := (H v).2 j hv
      rw [_root_.one_mul] at this
      exact this
    have hf' := hf (t.s j).val
    rw [hj] at hf'
    refine Eq.trans ?_ hf'
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    show ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom
      (((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE _).op).hom _) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.AnValJetGlob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingPullbackPeriodRigid
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingPullbackPeriodRigid
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.genMove_e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).2 Φ.lat.zero_mem

theorem AnFr.genMove_e_zero_left : (Φ.e 0).left = x0 ≫ eSec A := by
  rw [Φ.genMove_e_zero]
  show (toUnit (Over.mk x0) ≫ η[A]).left = _
  rw [Over.comp_left]
  rfl

theorem AnFr.genMove_e_per (z a : Fin g → ℂ) (ha : a ∈ Φ.lat) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

theorem genMove_chart {X Z : Scheme.{0}} (M : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z)
    (j : K → M.ι) (h : ⊤ ≤ q ⁻¹ᵁ LB.wchart M φ j) (k : K) : ⊤ ≤ (q ≫ φ k) ⁻¹ᵁ M.U (j k) :=
  fun _ hy => LB.wchart_le M φ j k (h hy)

theorem AnFr.genRd_pullGen_iff {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) {Z' : Scheme.{0}} (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ) :
    Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v := by
  have hc : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) ↔
      ⊤ ≤ (q ≫ h) ⁻¹ᵁ LB.wchart L.L φ j := fun j =>
    ⟨fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k,
      fun H _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (H hy) k⟩
  have hv : ∀ j : K → L.L.ι, (⊤ ≤ q ⁻¹ᵁ LB.wchart L.L (fun k => h ≫ φ k) j) →
      valAt' q (LB.wchart L.L (fun k => h ≫ φ k) j) ((LB.pullGen L.L φ ε t h).s j).val =
        valAt' (q ≫ h) (LB.wchart L.L φ j) (t.s j).val := fun j hp =>
    (vtf_val_res q _ hp _).trans (vtf_val_pullU _ _ _ _)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [Category.assoc]; exact h1 k, fun j hj => ?_⟩
    exact (hv j ((hc j).2 hj)).symm.trans (h2 j ((hc j).2 hj))
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => by rw [← h1 k, Category.assoc], fun j hj => ?_⟩
    exact (hv j hj).trans (h2 j ((hc j).1 hj))

theorem AnFr.genRd_period {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ) (ha : ∀ k, a k ∈ Φ.lat)
    (H : Φ.GenRd φ ε t q p v) :
    Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k) := by
  obtain ⟨h1, h2⟩ := H
  refine ⟨fun k => by rw [Φ.genMove_e_per _ _ (ha k)]; exact h1 k, fun j hj => ?_⟩
  rw [h2 j hj, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk := genMove_chart L.L φ q j hj k
  rw [h1 k] at hk
  rw [Φ.fr_per (a k) (ha k) (j k) (p k) hk, mul_zpow]
  rfl

theorem AnFr.genRd_rigPow (k : ℤ) :
    Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  refine ⟨fun _ => Φ.genMove_e_zero_left.symm, fun j hj => ?_⟩
  have hk := genMove_chart L.L (K := PUnit) (fun _ => eSec A) x0 j hj PUnit.unit
  rw [← Φ.genMove_e_zero_left] at hk
  rw [_root_.one_mul, Fintype.prod_unique]
  have e := Φ.fr_0 (j PUnit.unit) hk
  show _ = Φ.fr (j PUnit.unit) 0 ^ k
  rw [e]
  exact vtf_valU x0 hj (L.rig.s j) k

end

theorem genRd_pull_period_rig : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), (∀ (Z' : Scheme.{0}) (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ), Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v) ∧ (∀ (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ), (∀ k, a k ∈ Φ.lat) → Φ.GenRd φ ε t q p v → Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k)) ∧ ∀ k : ℤ, Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 :=
  fun _ _ _ _ _ _ _ Φ _ _ _ φ ε t =>
    ⟨fun _ h q p v => Φ.genRd_pullGen_iff φ ε t h q p v,
      fun q p a v ha H => Φ.genRd_period φ ε t q p a v ha H, fun k => Φ.genRd_rigPow k⟩

end GlobalTheory.AnVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingPullbackPeriodRigidStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generatorReading_pullback_period_rigid : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), (∀ (Z' : Scheme.{0}) (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ), Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v) ∧ (∀ (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ), (∀ k, a k ∈ Φ.lat) → Φ.GenRd φ ε t q p v → Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k)) ∧ ∀ k : ℤ, Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  first | exact @GlobalTheory.AnVal.genRd_pull_period_rig | exact GlobalTheory.AnVal.genRd_pull_period_rig | (intros; apply GlobalTheory.AnVal.genRd_pull_period_rig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem semichar_herm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  simp [hermForm]

theorem semichar_herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem semichar_herm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem semichar_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply]
  ring

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.exists_chart_lat : ∃ j, ∀ a ∈ Φ.lat, ⊤ ≤ (Φ.e a).left ⁻¹ᵁ L.L.U j := by
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  obtain ⟨j, hj⟩ : ∃ j, (Φ.e 0).left pt ∈ L.L.U j :=
    TopologicalSpace.Opens.mem_iSup.1 (L.isLB.cover.ge (Set.mem_univ _))
  have hj0 : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j := fun z _ => by
    have hz : z = pt := Subsingleton.elim (α := PrimeSpectrum ℂ) z pt
    rw [hz]
    exact hj
  refine ⟨j, fun a ha => ?_⟩
  rw [(Φ.e_ker a).2 ha, ← (Φ.e_ker 0).2 Φ.lat.zero_mem]
  exact hj0

theorem AnFr.χ_add {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
  obtain ⟨j, hj⟩ := Φ.exists_chart_lat
  have hab := Φ.lat.add_mem ha hb
  have h1 := Φ.fr_per a ha j 0 (hj 0 Φ.lat.zero_mem)
  have h2 := Φ.fr_per b hb j a (hj a ha)
  have h3 := Φ.fr_per (a + b) hab j 0 (hj 0 Φ.lat.zero_mem)
  have hne : Φ.fr j (a + b) ≠ 0 := Φ.fr_ne j _ (hj _ hab)
  rw [zero_add, h2] at h1
  rw [zero_add] at h3
  simp only [semichar_herm_zero_left, mul_zero, zero_add] at h1 h3
  have key : Φ.χ (a + b) * Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) =
      Φ.χ a * Φ.χ b * (Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
        Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b)) := by
    have := h3.symm.trans h1
    apply mul_right_cancel₀ hne
    linear_combination this
  have hexp : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
      Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b) =
      Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) *
        Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [semichar_herm_add_left, semichar_herm_add_right, semichar_herm_add_right, semichar_herm_swap Φ.herm a b]
    have hsc : hermForm Φ.Hm a b - star (hermForm Φ.Hm a b) =
        2 * ((hermForm Φ.Hm a b).im : ℂ) * Complex.I := by
      rw [show star (hermForm Φ.Hm a b) = (starRingEnd ℂ) (hermForm Φ.Hm a b) from rfl, Complex.sub_conj]
      push_cast; ring
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  rw [hexp] at key
  have hE : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hE
  linear_combination key

theorem AnFr.χ_ne_zero {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ a ≠ 0 := fun h => by
  have := Φ.χ_norm a ha
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem AnFr.herm_im_swap (a b : Fin g → ℂ) : (hermForm Φ.Hm b a).im = -(hermForm Φ.Hm a b).im := by
  rw [semichar_herm_swap Φ.herm a b]
  simp

theorem AnFr.herm_im_int {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    ∃ k : ℤ, (hermForm Φ.Hm a b).im = k := by
  have h1 := Φ.χ_add ha hb
  have h2 := Φ.χ_add hb ha
  rw [add_comm b a, h1, Φ.herm_im_swap a b, mul_comm (Φ.χ b)] at h2
  have h3 := mul_left_cancel₀ (mul_ne_zero (Φ.χ_ne_zero ha) (Φ.χ_ne_zero hb)) h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
  refine ⟨n, ?_⟩
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (((hermForm Φ.Hm a b).im : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hπ
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

theorem AnFr.herm_im_self (a : Fin g → ℂ) : (hermForm Φ.Hm a a).im = 0 := by
  have := Φ.herm_im_swap a a
  linarith

theorem AnFr.χ_add_self {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ (a + a) = Φ.χ a ^ 2 := by
  rw [Φ.χ_add ha ha, Φ.herm_im_self]
  simp [sq]

theorem AnFr.χ_zero : Φ.χ 0 = 1 := by
  have h := Φ.χ_add_self Φ.lat.zero_mem
  rw [add_zero] at h
  apply mul_left_cancel₀ (Φ.χ_ne_zero Φ.lat.zero_mem)
  linear_combination -h

end

theorem anFr_semichar : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, ∀ b ∈ Φ.lat, (∃ k : ℤ, (hermForm Φ.Hm a b).im = k) ∧ Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ))) ∧ Φ.χ 0 = 1 ∧ ((∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ a ∈ Φ.lat, Φ.χ ((2 : ℂ) • a) = 1) := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun a ha b hb => ⟨Φ.herm_im_int ha hb, Φ.χ_add ha hb⟩, Φ.χ_zero, fun h a ha => ?_⟩
  rw [two_smul, Φ.χ_add_self ha, h a ha]

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbert_frame_semicharacter : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, ∀ b ∈ Φ.lat, (∃ k : ℤ, (hermForm Φ.Hm a b).im = k) ∧ Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ))) ∧ Φ.χ 0 = 1 ∧ ((∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ a ∈ Φ.lat, Φ.χ ((2 : ℂ) • a) = 1) := by
  first | exact @GlobalTheory.AnVal.anFr_semichar | exact GlobalTheory.AnVal.anFr_semichar | (intros; apply GlobalTheory.AnVal.anFr_semichar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingCorrMulInv
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingCorrMulInv
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValGenCorr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_iff {X Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Z ⟶ X)) (j : K → L.ι)
    (x : Sp ℂ ⟶ Z) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  constructor
  · intro h k p _
    have hp := h (Set.mem_univ p)
    exact Set.mem_iInter.1 hp k
  · intro h p _
    exact Set.mem_iInter.2 fun k => h k (Set.mem_univ p)

theorem exists_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (x : Sp ℂ ⟶ X) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  have h : x cpt ∈ (⨆ i, L.U i : X.Opens) := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i, ReciprocityTheory.ChartRestriction.G.PullbackSections.top_le_of_mem hi⟩

theorem corr_val {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (hc : LB.Gen.Corr L φ ε φ' ε' t t')
    (J : (Y ⟶ X) → L.ι) (p : Sp ℂ ⟶ Y) (hJ : ∀ ψ, ⊤ ≤ (p ≫ ψ) ⁻¹ᵁ L.U (J ψ)) :
    valAt' p (LB.wchart L φ fun k => J (φ k)) (t.s fun k => J (φ k)).val =
      valAt' p (LB.wchart L φ' fun k => J (φ' k)) (t'.s fun k => J (φ' k)).val := by
  have h1 := (chart_iff L φ (fun k => J (φ k)) p).2 fun k => hJ _
  have h2 := (chart_iff L φ' (fun k => J (φ' k)) p).2 fun k => hJ _
  have h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k)) :=
    fun z hz => ⟨h1 hz, h2 hz⟩
  have e0 := hc (fun k => J (φ k)) (fun k => J (φ' k)) (fun _ _ e => congrArg J e) (fun _ _ e => congrArg J e)
    (fun _ _ e => congrArg J e)
  have e := congrArg (fun u : Γ(Y, LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k))ˣ =>
    valAt' p _ u.val) e0
  exact (vtf_val_res p _ h _).symm.trans (e.trans (vtf_val_res p _ h _))

theorem val_inv {Z : Scheme.{0}} (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) :
    valAt' p V (u⁻¹).val = (valAt' p V u.val)⁻¹ := by
  have e := vtf_valU p h u (-1)
  rwa [zpow_neg_one, zpow_neg_one] at e

open scoped Classical in
theorem prod_fibre {T K : Type} [Fintype K] (φ : K → T) (ε : K → ℤ) (f : T → ℂ) (s : Finset T)
    (hs : ∀ k, φ k ∈ s) (hf : ∀ ψ ∈ s, f ψ ≠ 0) :
    ∏ k, f (φ k) ^ ε k = ∏ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) := by
  have key : ∀ ψ ∈ s, f ψ ^ (∑ k, if φ k = ψ then ε k else 0) =
      ∏ k, if φ k = ψ then f (φ k) ^ ε k else 1 := by
    intro ψ hψ
    have h : ∀ u : Finset K, f ψ ^ (∑ k ∈ u, if φ k = ψ then ε k else 0) =
        ∏ k ∈ u, if φ k = ψ then f (φ k) ^ ε k else 1 := by
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | insert a u ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (hf ψ hψ), ih]
        congr 1
        split_ifs with h
        · rw [h]
        · simp
    exact h _
  rw [Finset.prod_congr rfl key, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_ite_eq, if_pos (hs k)]

theorem genRd_corr_mul_inv : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  classical
  intro S A _ _ L x0 g Φ Z K K' _ _ φ ε φ' ε' t t' q p p' v v' h h'
  have hA : LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι,
      (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧
      v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k := by
    intro hc
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart L.L L.isLB (q ≫ ψ)
    refine ⟨J, hJ, ?_⟩
    have e := corr_val L.L φ ε φ' ε' t t' hc J q hJ
    have e1 := h.2 (fun k => J (φ k)) ((chart_iff L.L φ _ q).2 fun k => hJ _)
    have e2 := h'.2 (fun k => J (φ' k)) ((chart_iff L.L φ' _ q).2 fun k => hJ _)
    exact e1.symm.trans (e.trans e2)
  refine ⟨hA, ?_, ⟨?_, ?_⟩, ⟨h.1, ?_⟩⟩
  · rintro hc hs ⟨π, hπ, hπ'⟩
    obtain ⟨J, hJ, e⟩ := hA hc
    have n1 : ∀ k, Φ.fr (J (φ k)) (π (φ k)) ≠ 0 := fun k => by
      rw [← hπ k]; apply Φ.fr_ne; rw [← h.1 k]; exact hJ _
    have n2 : ∀ k, Φ.fr (J (φ' k)) (π (φ' k)) ≠ 0 := fun k => by
      rw [← hπ' k]; apply Φ.fr_ne; rw [← h'.1 k]; exact hJ _
    let s : Finset (Z ⟶ A.left) := Finset.univ.image φ ∪ Finset.univ.image φ'
    have hf : ∀ ψ ∈ s, Φ.fr (J ψ) (π ψ) ≠ 0 := by
      intro ψ hψ
      rcases Finset.mem_union.1 hψ with hψ | hψ
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n1 k
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hψ
        exact n2 k
    have p1 := prod_fibre φ ε (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p2 := prod_fibre φ' ε' (fun ψ => Φ.fr (J ψ) (π ψ)) s
      (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) hf
    have p3 : ∏ k, Φ.fr (J (φ k)) (π (φ k)) ^ ε k = ∏ k, Φ.fr (J (φ' k)) (π (φ' k)) ^ ε' k := by
      refine p1.trans (Eq.trans ?_ p2.symm)
      refine Finset.prod_congr rfl fun ψ _ => ?_
      congr 1
      exact hs ψ
    simp only [hπ, hπ'] at e
    rw [p3] at e
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n2 k)) e
  · rintro (k | k)
    · exact h.1 k
    · exact h'.1 k
  · intro j hj
    have hj0 := (chart_iff L.L _ j q).1 hj
    have e1 := h.2 (j ∘ Sum.inl) ((chart_iff L.L φ _ q).2 fun k => hj0 (Sum.inl k))
    have e2 := h'.2 (j ∘ Sum.inr) ((chart_iff L.L φ' _ q).2 fun k => hj0 (Sum.inr k))
    refine (ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul q _ _ _).trans ?_
    refine (congrArg₂ (· * ·) ((vtf_val_res q _ hj _).trans e1) ((vtf_val_res q _ hj _).trans e2)).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  · intro j hj
    have e1 := h.2 j hj
    have e2 := val_inv q hj (t.s j)
    refine e2.trans ?_
    refine (congrArg (·⁻¹) e1).trans ?_
    simp only [mul_inv, zpow_neg, Finset.prod_inv_distrib]

end GlobalTheory.AnValGenCorr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingCorrMulInvStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generatorReading_corr_mul_inv : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  first | exact @GlobalTheory.AnValGenCorr.genRd_corr_mul_inv | exact GlobalTheory.AnValGenCorr.genRd_corr_mul_inv | (intros; apply GlobalTheory.AnValGenCorr.genRd_corr_mul_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem AnFr.rd_twistPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  intro S A _ _ L x0 g Φ ψ m hm a b α s s' θ p v hψ ht hs hα j' z pt h1 h2 hj'
  obtain ⟨hmz, j, hj, hv⟩ := hα z
  change (vtfQ A (Φ.e z)).left ≫ m.left = _ at hmz
  change ⊤ ≤ (vtfQ A (Φ.e z)).left ⁻¹ᵁ _ at hj
  change valAt' (vtfQ A (Φ.e z)).left _ _ = _ at hv
  have h0 : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (j 0) := by
    rw [← vtfQ_snd A (Φ.e z)]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 0 (hj hq)
  have h1' : ⊤ ≤ (Φ.e (p z)).left ⁻¹ᵁ L.L.U (j 1) := by
    rw [← hmz]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 1 (hj hq)
  have e1 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (snd (Over.mk x0) A).left = (Φ.e (p z)).left := by
    rw [Category.assoc, ← Over.comp_left, hm, hmz]
  have e2 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (fst (Over.mk x0) A).left = 𝟙 (Sp ℂ) := by
    rw [Category.assoc, ← Over.comp_left, hψ]
    exact vtfQ_fst A (Φ.e z)
  have hr := hs (j 1) (p z) _ e1 e2 h1'
  have tw := vtf_twist A L.L ht (vtfQ A (Φ.e z)).left j hj
  have hne := Φ.fr_ne (j 1) (p z) h1'
  rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
  refine vtf_read A L.L s' (Φ.e z) (fun i => Φ.fr i z) (fun i i' h => Φ.fr_g i i' z h) (j 0) j' h0 hj' _ ?_
  refine tw.trans ?_
  refine (congrArg₂ (· * ·) hv hr).trans ?_
  have hz : Φ.fr (j 1) (p z) ^ b ≠ 0 := zpow_ne_zero _ hne
  rw [zpow_neg]
  field_simp

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reading_twisted_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  first | exact @GlobalTheory.AnVal.AnFr.rd_twistPull | exact GlobalTheory.AnVal.AnFr.rd_twistPull | (intros; apply GlobalTheory.AnVal.AnFr.rd_twistPull <;> assumption)
end
end
