module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSpMapComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.ExpCoord

theorem val_spMap_comp {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {X : Scheme.{0}} (y : Sp S ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ y) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom (((spMap φ ≫ y).appLE U ⊤ h').hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((y.appLE U ⊤ h).hom f)) := by
  have e : (spMap φ ≫ y).appLE U ⊤ h' = y.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) y U ⊤ ⊤ h le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [e]
  exact e2

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h1 : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dite_eq_left h, dite_eq_left h1]
    unfold valAt
    rw [← Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
    rfl
  · have h1 : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dite_eq_right h, dite_eq_right h1]

theorem deriv_scale {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) {v : Sp (DualNumber ℂ) ⟶ X}
    {w : Fin g → ℂ} (h : IsDerivAt0 e w v) (s : ℂ) : IsDerivAt0 e (s • w) (spMap (epsScaleR s) ≫ v) := by
  have hsub : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := GlobalTheory.UnifDifferential.subsingleton_primeSpectrum ℂ ℂ
  refine ⟨?_, fun U h' f => ?_⟩
  · have hc : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsScaleR s) = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
      refine RingHom.ext fun x => ?_
      show (TrivSqZeroExt.map _ x).fst = x.fst
      exact TrivSqZeroExt.fst_map _ _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    exact h.1
  · have hv : ⊤ ≤ v ⁻¹ᵁ U := by
      intro x _
      have := h' (Set.mem_univ x)
      have hx : (spMap (epsScaleR s)) x = x := Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
      change v ((spMap (epsScaleR s)) x) ∈ U at this
      rwa [hx] at this
    rw [val_spMap_comp (epsScaleR s) v U hv h' f, map_smul, ← h.2 U hv f]
    simp [epsScaleR]

theorem deriv_comp {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
    (φ : X ⟶ Y) (Rho : Matrix (Fin g) (Fin g) ℂ) (hol : IsHolTo Set.univ e') (hc : ∀ z, e' (Rho *ᵥ z) = e z ≫ φ)
    {v : Sp (DualNumber ℂ) ⟶ X} {w : Fin g → ℂ} (h : IsDerivAt0 e w v) : IsDerivAt0 e' (Rho *ᵥ w) (v ≫ φ) := by
  have h0 : e' 0 = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ φ := by
    rw [← Category.assoc, h.1, ← hc, Matrix.mulVec_zero]
  refine ⟨h0.symm, fun U hU f => ?_⟩
  have h1 : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := hU
  rw [← Scheme.Hom.appLE_comp_appLE v φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
  refine (h.2 (φ ⁻¹ᵁ U) h1 ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)).trans ?_
  set G : (Fin g → ℂ) → ℂ := fun z => valAt' (e' z) U f with hG
  have hfun : (fun z => valAt' (e z) (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)) = fun z => G (Rho *ᵥ z) := by
    funext z
    rw [hG]
    dsimp only
    rw [hc, valAt'_comp]
  rw [hfun]
  have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e' b ⁻¹ᵁ U} := by
    refine ⟨Set.mem_univ _, fun x _ => ?_⟩
    rw [h0]
    exact hU (Set.mem_univ _)
  have hd : DifferentiableAt ℂ G 0 :=
    ((hol U f).2 0 hmem).differentiableAt ((hol U f).1.mem_nhds hmem)
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin Rho)
  have hL0 : L 0 = 0 := map_zero L
  have hG' : HasFDerivAt G (fderiv ℂ G 0) (L 0) := by rw [hL0]; exact hd.hasFDerivAt
  have := hG'.comp (0 : Fin g → ℂ) L.hasFDerivAt
  show (fderiv ℂ (G ∘ ⇑L) 0) w = _
  rw [this.fderiv]
  rfl

def toSp {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A :=
  Over.homMk v.left (by simpa using Over.w v)

theorem toSp_eq {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp v = (Over.homMk (𝟙 _) (by simp) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ epsPt (𝟙 (Sp ℂ))) ≫ v := by
  apply Over.OverMorphism.ext
  simp [toSp]

theorem toSp_mul {A : Over (Sp ℂ)} [GrpObj A] (v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp (v * v') = toSp v * toSp v' := by
  rw [toSp_eq, toSp_eq, toSp_eq, MonObj.comp_mul]

theorem one_left {A : Over (Sp ℂ)} [GrpObj A] : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left = η[A].left := by
  have h1 : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A) = toUnit _ ≫ η[A] := rfl
  have h2 : (toUnit (Over.mk (𝟙 (Sp ℂ))) : Over.mk (𝟙 (Sp ℂ)) ⟶ 𝟙_ (Over (Sp ℂ))) = 𝟙 (Over.mk (𝟙 (Sp ℂ))) := toUnit_unique _ _
  rw [h1, h2, Category.id_comp]

theorem pullFn_congr {A : Over (Sp ℂ)} {y y' : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A} (e : y = y') (U : A.left.Opens)
    (h : ⊤ ≤ y.left ⁻¹ᵁ U) (h' : ⊤ ≤ y'.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    GlobalTheory.UnifDifferential.pullFn y U h f = GlobalTheory.UnifDifferential.pullFn y' U h' f := by
  subst e; rfl

theorem deriv_mul {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (he : e 0 = 1) {v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A} {w w' : Fin g → ℂ}
    (h : IsDerivAt0 (fun z => (e z).left) w v.left) (h' : IsDerivAt0 (fun z => (e z).left) w' v'.left) :
    IsDerivAt0 (fun z => (e z).left) (w + w') (v * v').left := by
  have ht : ∀ {x : epsPt (𝟙 (Sp ℂ)) ⟶ A},
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x.left = (e 0).left → Chart.IsTan (toSp x) := by
    intro x hx
    rw [Chart.isTan_iff]
    show spMap _ ≫ x.left = η[A].left
    rw [hx, he, one_left]
  have hv := ht h.1
  have hv' := ht h'.1
  have hm : Chart.IsTan (toSp (v * v')) := by rw [toSp_mul]; exact Chart.isTan_mul hv hv'
  refine ⟨?_, fun U hU f => ?_⟩
  · have := (Chart.isTan_iff _).1 hm
    show spMap _ ≫ (v * v').left = (e 0).left
    rw [he, one_left]
    exact this
  · have hU' : ⊤ ≤ (toSp v * toSp v').left ⁻¹ᵁ U := by rw [← toSp_mul]; exact hU
    obtain ⟨h₁, h₂, hs⟩ := GlobalTheory.UnifDifferential.snd_pullFn_mul hv hv' U hU'
    show (GlobalTheory.UnifDifferential.pullFn (toSp (v * v')) U hU f).snd = _
    rw [pullFn_congr (toSp_mul v v') U hU hU' f, hs, map_add (f := _)]
    exact congrArg₂ (· + ·) (h.2 U h₁ f) (h'.2 U h₂ f)

theorem expCoord : ∀ (g n : ℕ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (x : Sp ℂ ⟶ Sp ℂ) (T : (Fin n → ℂ) → (epsPtR x ⟶ A)), x = 𝟙 _ → IsExp (𝟙 (Sp ℂ)) e → Function.Injective T → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : ℂ) c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin n → ℂ), ∀ (u : A ⟶ A), IsMonHom u → ∀ (Mu : Matrix (Fin n) (Fin n) ℂ) (Rho : Matrix (Fin g) (Fin g) ℂ), (∀ c, T c ≫ u = T (Mu *ᵥ c)) → (∀ z, e (Rho *ᵥ z) = e z ≫ u) → ∀ w, L (Rho *ᵥ w) = Mu *ᵥ L w := by
  intro g n A _ _ e x T hx hE hT hR hM hS
  subst hx
  obtain ⟨hadd, -, hhol, hd, hu⟩ := hE
  have he0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  choose Φ hΦ hΦu using hd
  have tanΦ : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left := by
    intro w
    rw [(hΦ w).1]
    show (e 0).left = _
    rw [he0]
  choose Ψ hΨ using fun w => (hR (Φ w)).1 (tanΦ w)
  have key : ∀ w c, IsDerivAt0 (fun z => (e z).left) w (T c).left → Ψ w = c := by
    intro w c h
    apply hT
    rw [hΨ w]
    exact (hΦu w (T c) h).symm
  have inj : Function.Injective Ψ := by
    intro w w' h
    have e1 : Φ w = Φ w' := by rw [← hΨ w, ← hΨ w', h]
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (e 0).left := (hΦ w).1
    obtain ⟨w'', -, hw''⟩ := hu (Φ w) ht
    have a1 := hw'' w (hΦ w)
    have a2 := hw'' w' (by rw [e1]; exact hΦ w')
    rw [a1, a2]
  have surj : Function.Surjective Ψ := by
    intro c
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T c).left = (e 0).left := by
      rw [he0]; exact (hR (T c)).2 ⟨c, rfl⟩
    obtain ⟨w, hw, -⟩ := hu (T c) ht
    exact ⟨w, key w c hw⟩
  let Lin : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := Ψ
      map_add' := fun w w' => key (w + w') (Ψ w + Ψ w') (by
        rw [hM, hΨ, hΨ]
        exact deriv_mul e he0 (hΦ w) (hΦ w'))
      map_smul' := fun s w => key (s • w) (s • Ψ w) (by
        rw [hS, hΨ]
        exact deriv_scale _ (hΦ w) s) }
  refine ⟨LinearEquiv.ofBijective Lin ⟨inj, surj⟩, ?_⟩
  intro u _ Mu Rho hTu hRho w
  show Ψ (Rho *ᵥ w) = Mu *ᵥ Ψ w
  apply key
  rw [← hTu, Over.comp_left, hΨ]
  exact deriv_comp _ _ u.left Rho hhol (fun z => by rw [hRho, Over.comp_left]) (hΦ w)

end GlobalTheory.ExpCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypeCharacterConjugateInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharacterCoxeterTorusInvEqAtInverseStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharacterCoxeterTorusInvEqAtInverse
open Polynomial

noncomputable section

namespace GlobalTheory.CuspInv

open GlobalTheory.IndefiniteRowSideFullHecke

def mirrorEquiv (k : Type) [Field k] : k[X] ≃* k[X] where
  toFun := mirror
  invFun := mirror
  left_inv := fun f => mirror_mirror f
  right_inv := fun f => mirror_mirror f
  map_mul' := fun f g => mirror_mul_of_domain f g

theorem powIrr_of_inv {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι] (h h' : Matrix ι ι k)
    (hh : h * h' = 1) (H : ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n) :
    ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h'.charpoly = φ ^ n := by
  classical
  obtain ⟨φ, n, hφ, hn⟩ := H
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (Matrix.isUnit_det_of_right_inverse hh)
  have hinv : h' = h⁻¹ := (Matrix.inv_eq_right_inv hh).symm
  have hdet : h.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hh).ne_zero
  have h0 : h.charpoly.coeff 0 ≠ 0 := by
    intro h0
    exact hdet (by rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero])
  have hm : h.charpoly.mirror = h.charpolyRev := by
    rw [mirror, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (p := h.charpoly) h0, pow_zero, mul_one,
      Matrix.reverse_charpoly]
  have hψ : Irreducible (mirrorEquiv k φ) := (MulEquiv.irreducible_iff (mirrorEquiv k)).2 hφ
  have h1 : h.charpolyRev = (mirrorEquiv k φ) ^ n := by
    rw [← map_pow, ← hn, ← hm]; rfl
  have hass : Associated h'.charpoly ((normalize (mirrorEquiv k φ)) ^ n) := by
    refine Associated.trans ?_ ((associated_normalize _).pow_pow)
    rw [hinv, Matrix.charpoly_inv h hu, h1]
    refine associated_unit_mul_left _ _ ?_
    refine IsUnit.mul (IsUnit.pow _ isUnit_one.neg) ?_
    rw [isUnit_C, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
    exact inv_ne_zero hdet
  refine ⟨normalize (mirrorEquiv k φ), n, (associated_normalize _).irreducible hψ, ?_⟩
  exact eq_of_monic_of_associated h'.charpoly_monic ((monic_normalize hψ.ne_zero).pow n) hass

theorem eigenspace_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : g * f = 1) (z : L) : f.eigenspace z ≤ g.eigenspace z⁻¹ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : g (f v) = v := by rw [← Module.End.mul_apply, hfg]; rfl
  rw [hv, map_smul] at h1
  by_cases hz : z = 0
  · subst hz
    rw [zero_smul] at h1
    rw [← h1]; simp
  · conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]

theorem eigenspace_inv {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : f * g = 1) (hgf : g * f = 1) (z : L) : g.eigenspace z⁻¹ = f.eigenspace z := by
  refine le_antisymm ?_ (eigenspace_le f g hgf z)
  simpa using eigenspace_le g f hfg z⁻¹

theorem mem_aroots_iff {k L ι : Type} [Field k] [Field L] [Algebra k L] [Fintype ι] [DecidableEq ι]
    (h : Matrix ι ι k) (z : L) :
    z ∈ h.charpoly.aroots L ↔
      Module.End.eigenspace (Matrix.toLin' (h.map (algebraMap k L))) z ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_toLin', Matrix.charpoly_map, mem_aroots, IsRoot, eval_map_algebraMap]
  simp [h.charpoly_monic.ne_zero]

theorem torVal_inv {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {d : ℕ} (θ : LevelCuspCharacters.Tor p d →* Kˣ)
    (z : LevelCuspCharacters.Fbar p) : LevelCuspCharacters.torVal θ⁻¹ z = LevelCuspCharacters.torVal θ z⁻¹ := by
  have hinj : Function.Injective
      (fun u : LevelCuspCharacters.Tor p d => ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p)) :=
    fun a b hab => Subtype.ext (Units.ext hab)
  unfold LevelCuspCharacters.torVal
  by_cases hz : ∃ u : LevelCuspCharacters.Tor p d, ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) = z
  · obtain ⟨u, rfl⟩ := hz
    have h2 : (((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p))⁻¹ =
        (((u⁻¹ : LevelCuspCharacters.Tor p d) : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) := by simp
    rw [h2, hinj.extend_apply, hinj.extend_apply]
    simp
  · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply']
    · rfl
    · rintro ⟨u, hu⟩
      exact hz ⟨u⁻¹, by simp [hu]⟩

theorem cuspChar_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)),
    h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  intro p _ K _ ι _ _ θ h h' hh
  classical
  have hh' : h' * h = 1 := mul_eq_one_comm.1 hh
  have key : ∀ (a b : Matrix ι ι (ZMod p)), a * b = 1 →
      Matrix.toLin' (a.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) *
        Matrix.toLin' (b.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) = 1 := by
    intro a b hab
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  have heig := eigenspace_inv _ _ (key h h' hh) (key h' h hh')
  have hmem : ∀ z : LevelCuspCharacters.Fbar p, z ∈ (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset ↔
      z⁻¹ ∈ (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset := by
    intro z
    rw [Multiset.mem_toFinset, Multiset.mem_toFinset, mem_aroots_iff, mem_aroots_iff, heig]
  have hcard : (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card =
      (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card :=
    Finset.card_bijective _ inv_involutive.bijective hmem
  unfold LevelCuspCharacters.cuspChar
  by_cases H : ∃ (φ : (ZMod p)[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n
  · rw [if_pos H, if_pos (powIrr_of_inv h h' hh H)]
    congr 1
    refine Finset.sum_bijective _ inv_involutive.bijective (by convert hmem) ?_
    intro z _
    rw [torVal_inv, heig]
    congr 2
    funext i
    congr 3
  · rw [if_neg H, if_neg (fun H' => H (powIrr_of_inv h' h hh' H'))]

end GlobalTheory.CuspInv
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenCuspidalCharacterCoxeterTorus_inv_eq_at_inverse : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)), h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  first | exact @GlobalTheory.CuspInv.cuspChar_inv | exact GlobalTheory.CuspInv.cuspChar_inv | (intros; apply GlobalTheory.CuspInv.cuspChar_inv <;> assumption)
end

open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.TypeCharacterConjugateInverse

theorem toSquareBlock_mul_of_blockTriangular {r : ℕ} {k : Type} [Field k] {A B : Matrix (Fin r) (Fin r) k}
    {b : Fin r → Fin r} (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] :
    A.toSquareBlock b c * B.toSquareBlock b c = (A * B).toSquareBlock b c := by
  classical
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.mul_apply, Matrix.of_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l => b l = c) (p := fun l => b l = c) (by simp)
    (fun l => A i.1 l * B l j.1)]
  refine Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_
  have hl' : b l ≠ c := by simpa using hl
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hA (show b l < b i.1 by rw [i.2]; exact h), zero_mul]
  · rw [hB (show b j.1 < b l by rw [j.2]; exact h), mul_zero]

theorem blockTriangular_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) :
    ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular b := by
  letI := z.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hz

theorem toSquareBlock_mul_inv {r : ℕ} {k : Type} [Field k] {b : Fin r → Fin r} (z : GL (Fin r) k)
    (hz : (z : Matrix (Fin r) (Fin r) k).BlockTriangular b) (c : Fin r)
    [Fintype {i : Fin r // b i = c}] [DecidableEq {i : Fin r // b i = c}] :
    (z : Matrix (Fin r) (Fin r) k).toSquareBlock b c *
      ((z⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).toSquareBlock b c = 1 := by
  rw [toSquareBlock_mul_of_blockTriangular hz (blockTriangular_inv z hz), ← Units.val_mul, mul_inv_cancel,
    Units.val_one]
  ext i j
  simp [Matrix.toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]

theorem typeChar_conj_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (r : ℕ) (s : LevelCuspCharacters.SSParam p K r),
    (∀ x y : GL (Fin r) (ZMod p), IsConj x y → LevelCuspCharacters.typeChar s x = LevelCuspCharacters.typeChar s y) ∧
    ∀ x : GL (Fin r) (ZMod p),
      LevelCuspCharacters.typeChar (⟨s.1, fun c => (s.2 c)⁻¹⟩ : LevelCuspCharacters.SSParam p K r) x = LevelCuspCharacters.typeChar s x⁻¹ := by
  intro p _ K _ r s
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    unfold LevelCuspCharacters.typeChar
    congr 1
    letI := Fintype.ofFinite (GL (Fin r) (ZMod p))
    refine Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun y => ?_
    have h : (Equiv.mulLeft c y)⁻¹ * (c * x * c⁻¹) * (Equiv.mulLeft c y) = y⁻¹ * x * y := by
      simp only [Equiv.coe_mulLeft]
      group
    rw [h]
  · unfold LevelCuspCharacters.typeChar
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    have h : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    rw [h]
    generalize y⁻¹ * x * y = z
    by_cases hz : (z : Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1
    · rw [if_pos hz, if_pos (blockTriangular_inv z hz)]
      refine Finset.prod_congr rfl fun c _ => ?_
      exact GlobalTheory.T.greenCuspidalCharacterCoxeterTorus_inv_eq_at_inverse p K _ (s.2 c) _ _ (toSquareBlock_mul_inv z hz c.1)
    · rw [if_neg hz, if_neg fun h' => hz (by simpa using blockTriangular_inv z⁻¹ h')]

end GlobalTheory.TypeCharacterConjugateInverse
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links
  GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameFinitePart

theorem exists_chrEq_val (D : D7) (χ : HChar D.host.E) (hχ : χ.IsUnitary) :
    ∃ c, ChrEq c χ ∧ ∀ x, ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c', ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩, fun x => ⟨u x, rfl⟩⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
  · refine (hcoe _).trans ?_
    have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
      (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
    exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
  · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
    change Θ (x : Formalism.L2.Theta.AE D) = _
    rw [hx, hloc P e he]

theorem exists_lift (D : D7) (y : (AfE D)ˣ) : ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) = y ∧
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
  obtain ⟨a, a1, a2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 (y : AfE D)
  obtain ⟨b, b1, b2⟩ := GlobalTheory.PlaceIdem.parts_surj D 1 ((y⁻¹ : (AfE D)ˣ) : AfE D)
  have h : a * b = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, a1, b1, RingHom.map_one, mul_one])
    (by rw [RingHom.map_mul, a2, b2, RingHom.map_one, Units.mul_inv])
  exact ⟨⟨a, b, h, (mul_comm b a).trans h⟩, a1, a2, b2⟩

theorem exists_unit_ne_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (ht : χ.TameAt P) (hr : ¬ χ.UnrAt P) : ∃ k : Lˣ, P.valuation L (k : L) = 1 ∧ χ.locK P k ≠ 1 := by
  by_contra hn
  refine hr fun x hx => ?_
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-1 : ℤ)).preimage (continuous_sub_left (x : P.adicCompletion L))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L) P).exists_mem_open h1 ⟨x, by simp⟩
  have hk' : Valued.v ((x : P.adicCompletion L) - algebraMap L _ k) ≤ WithZero.exp (-1 : ℤ) := hk
  have hx' : Valued.v (x : P.adicCompletion L) = 1 := hx
  have hv : Valued.v (algebraMap L (P.adicCompletion L) k) = 1 := by
    rw [← hx']
    refine (Valuation.map_eq_of_sub_lt _ ?_)
    rw [Valuation.map_sub_swap, hx']
    refine hk'.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hv' : P.valuation L k = 1 := (GlobalTheory.BaseIdeleTriv.val_algebraMap P k).symm.trans hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv'
  have h2 : χ.loc P (atFin P (Units.mk0 k hk0)) = 1 := by
    by_contra h
    exact hn ⟨Units.mk0 k hk0, hv', h⟩
  have e : ((x * (atFin P (Units.mk0 k hk0))⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
      x * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have h0 : algebraMap L (P.adicCompletion L) k ≠ 0 := by simpa using hk0
  have h3 := ht (x * (atFin P (Units.mk0 k hk0))⁻¹) (by
    unfold IsUnitAt
    rw [e, map_mul, map_inv₀, hx', hv]; simp) (by
    have : (x : P.adicCompletion L) * (algebraMap L (P.adicCompletion L) k)⁻¹ - 1 =
        ((x : P.adicCompletion L) - algebraMap L _ k) * (algebraMap L (P.adicCompletion L) k)⁻¹ := by
      field_simp
    rw [e, this, map_mul, map_inv₀, hv, inv_one, mul_one]
    simpa using hk')
  rwa [map_mul, map_inv, h2, inv_one, mul_one] at h3

theorem loc_sub_one {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) (N : ℕ)
    (hN : (N : E) ≠ 0) : f (1 + e * (i k - 1)) - 1 = N • f (e * i ((k - 1) / N)) := by
  rw [← map_nsmul, ← mul_smul_comm, ← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hN, map_add (f := _), map_one, map_sub, map_one,
    add_sub_cancel_left]

theorem loc_eq {E A B : Type} [Field E] [CommRing A] [CommRing B] (i : E →+* A) (f : A →+* B) (e : A) (k : E) :
    f (1 + e * (i k - 1)) = 1 + f (e * i (k - 1)) := by
  rw [map_add (f := _), map_one, map_sub, map_one]

theorem loc_mul_inv {E A : Type} [Field E] [CommRing A] (i : E →+* A) (e : A) (he : e * e = e) (k : Eˣ) :
    (1 + e * (i k - 1)) * (1 + e * (i ((k⁻¹ : Eˣ) : E) - 1)) = 1 := by
  have hkk : i (k : E) * i ((k⁻¹ : Eˣ) : E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination (i (k : E) - 1) * (i ((k⁻¹ : Eˣ) : E) - 1) * he + e * hkk


set_option maxHeartbeats 800000 in
theorem exists_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (k : D.host.Eˣ)
    (hk : P.valuation D.host.E (k : D.host.E) = 1) (N : ℕ) (hN : (N : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ (e : AE D) (x : (AE D)ˣ), IsPlIdem D e P ∧ (x : AE D) = locE D e (k : D.host.E) ∧
      IntUnit (Units.map (finPart D).toMonoidHom x) ∧ CongOne N (Units.map (finPart D).toMonoidHom x) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -, e1, e2⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hee : e * e = e := he.1
  have hint : ∀ t : D.host.E, P.valuation D.host.E t ≤ 1 → finPart D (e * incA D t) ∈ intAE D := fun t ht => by
    have h4 : finPart D (incA D t) = (1 : Af D.host.F) ⊗ₜ[D.host.F] t := rfl
    rw [h2, RingHom.map_mul, map_mul, h4, h1]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_mul_apply]
    by_cases hQ : Q = P
    · subst hQ
      rw [e1, one_mul, GlobalTheory.BaseIdeleTriv.adele_algebraMap_apply, GlobalTheory.BaseIdeleTriv.val_algebraMap]
      exact ht
    · rw [e2 Q hQ, zero_mul, map_zero]
      exact zero_le
  have hone : (1 : AfE D) ∈ intAE D := by
    rw [h2, map_one]
    intro Q
    rw [GlobalTheory.BaseIdeleTriv.adele_one_apply, map_one]
  have hloc : ∀ t : D.host.E, P.valuation D.host.E t = 1 → finPart D (locE D e t) ∈ intAE D := fun t ht => by
    rw [show finPart D (locE D e t) = _ from loc_eq (incA D) (finPart D) e t]
    exact add_mem hone (hint _ (Valuation.map_sub_le _ ht.le (map_one _).le))
  have hm : locE D e (k : D.host.E) * locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) = 1 := loc_mul_inv (incA D) e hee k
  have hN1 : P.valuation D.host.E (N : D.host.E) = 1 := by
    have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) P (r := (N : 𝓞 D.host.E))).2 hN
    simpa using this
  have hN0 : (N : D.host.E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hN1
    exact zero_ne_one hN1
  refine ⟨e, ⟨_, _, hm, (mul_comm _ _).trans hm⟩, he, rfl, ⟨hloc _ hk, hloc _ ?_⟩,
    finPart D (e * incA D (((k : D.host.E) - 1) / N)), hint _ ?_, ?_⟩
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hk, inv_one]
  · rw [map_div₀, hN1, div_one]
    exact Valuation.map_sub_le _ hk.le (map_one _).le
  · exact loc_sub_one (incA D) (finPart D) e k N hN0


set_option maxHeartbeats 1000000 in
theorem exists_xiRec : ∀ (D : D7) (p : ℕ) (δ : Formalism.L2.Host.HChar D.host.E), (p = D.host.pde ∨ p = D.host.pde') → Formalism.L2.Host.IsDelta (H := D.host) p δ → (∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D) → ∃ (χ : (AE D)ˣ →* Circle) (de : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ), ChrEq χ δ ∧ XiRec D p de ∧ ∀ (x : (AE D)ˣ) (y : (GlobalTheory.FinalJoin.AfE D)ˣ), Formalism.L2.Theta.finPart D (x : AE D) = (y : GlobalTheory.FinalJoin.AfE D) → ((de y : ℂˣ) : ℂ) = ((χ x : Circle) : ℂ) := by
  intro D p χ hp hδ hval
  obtain ⟨n, hn, ho⟩ := hδ.fin
  obtain ⟨c, h, hcv⟩ := exists_chrEq_val D χ fun x => by
    have h1 : χ.1 x ^ n = 1 := by
      have := DFunLike.congr_fun (congrArg Subtype.val ho) x
      simpa [MonoidHom.pow_apply] using this
    have h2 : ((χ.1 x : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'
  have h1 : ∀ x, c x ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  have h2 : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1 := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
    rw [map_pow, h1]
  have h3 : ∀ a, c (idF D a) = 1 := fun a => by
    let b : (AF D.host.F)ˣ := Units.map ((MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))) a
    let b' : (AF D.host.F)ˣ := Units.map ((MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))) a
    have e : a = b' * b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e, map_mul, map_mul, h2 (idF D b') rfl, GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ h hδ.triv b rfl, one_mul]
  obtain ⟨d, hd⟩ := GlobalTheory.DetRootChar.circle_hom_factor (Units.map (finPart D).toMonoidHom) c
    fun x hx => h2 x (congrArg Units.val hx)
  have hd' : ∀ (x : (AE D)ˣ) (y : (AfE D)ˣ), finPart D (x : AE D) = (y : AfE D) → d y = c x := fun x y hxy => by
    rw [← hd x]
    exact congrArg d (Units.ext hxy.symm)
  have hone : ∀ y, d y = 1 → (Circle.toUnits.comp d) y = 1 := fun y hy => by
    rw [MonoidHom.comp_apply, hy, map_one]
  have hcoe : ∀ y, (((Circle.toUnits.comp d) y : ℂˣ) : ℂ) = ((d y : Circle) : ℂ) := fun y => by simp
  have hpp : p.Prime ∧ ∀ i, p ≠ D.host.g i := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, fun i => (D.host.pde_ne_g i).2⟩
  refine ⟨c, Circle.toUnits.comp d, h, ⟨fun y a hy => hone y ?_, fun y a hy => hone y ?_, fun y hy hc => hone y ?_, ?_,
    ⟨n, hn, fun y => ?_⟩, fun y => ?_⟩, fun x y hxy => by rw [hcoe, hd' x y hxy]⟩
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨b, z, hz, hxz⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x (by
      rw [hx, hy]
      change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
      rw [map_one])
    rw [hd' x y hx, hxz, map_mul, h3, h2 z hz, mul_one]
  · have ha : a ≠ 0 := by
      rintro rfl
      obtain ⟨ι, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
      obtain ⟨P, -⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
      have e := congrArg (fun z => ι z P) y.mul_inv
      rw [hy, TensorProduct.tmul_zero, zero_mul, map_zero, map_one] at e
      exact zero_ne_one (α := P.adicCompletion D.host.E) e
    rw [hd' (Units.map (incA D).toMonoidHom (Units.mk0 a ha)) y hy.symm, h.1.2]
  · obtain ⟨x, hx0, hx, hx'⟩ := exists_lift D y
    rw [hd' x y hx]
    exact GlobalTheory.tame_heckeChar_eq_one_of_finUnit D c χ h hδ.tame p hδ.unr x ⟨hx0, hx ▸ hy.1, hx' ▸ hy.2⟩ (hx ▸ hc)
  · obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E hpp.1
    obtain ⟨k, hk, hk1⟩ := exists_unit_ne_one χ P (hδ.tame P) fun hu => by
      have := (hδ.ine P hP 1).1 fun x hx => by rw [hu x hx, one_pow]
      omega
    have hcop : Nat.Coprime p (D.host.g 0 * D.host.g 1) :=
      ((Nat.coprime_primes hpp.1 (D.host.g_prime 0)).2 (hpp.2 0)).mul_right
        ((Nat.coprime_primes hpp.1 (D.host.g_prime 1)).2 (hpp.2 1))
    obtain ⟨e, x, he, hx, i1, i2⟩ := exists_local D P k hk (D.host.g 0 * D.host.g 1) fun hm => by
      obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.E) hcop)
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hm)))
    refine ⟨_, i1, i2, fun hh => hk1 (Units.ext ?_)⟩
    rw [← h.2 P e he k x hx, ← hd x, ← hcoe, hh]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    rw [MonoidHom.comp_apply, ← map_pow, hd' x y hx, h1, map_one]
  · obtain ⟨x, -, hx, -⟩ := exists_lift D y
    obtain ⟨z, hz⟩ := hcv x
    rw [hcoe, hd' x y hx, hz]
    exact hval z

end GlobalTheory.TameFinitePart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestriction
section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsObUNeZero
section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsOb1NeZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.Model

section General

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

include hI in
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI] at this
  simpa using this

variable {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]



include hI hs in
theorem exists_isSig (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (semi : SemiHom π p) (surj : Function.Surjective p)
    (ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) : ∃ σ, α.IsSig p σ := by
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have h0 : b - b' ∈ I.map (algebraMap R B) := (ker _).1 (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← smul_sub, Algebra.smul_def]
    exact mul_eq_zero_of_mem (map_sq hI B) (Ideal.mem_map_of_mem _ (α.mem y)) h0
  have e := Function.surjInv_eq surj
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b ↦ α.k y • Function.surjInv surj b)
    fun b b' ↦ by rw [← smul_add]; exact key _ _ _ (by rw [map_add (f := _), e, e, e])) fun y y' ↦ by
      ext b; simp [add_smul]
  refine ⟨TensorProduct.liftAddHom f fun r y b ↦ ?_, fun y b ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := hs r
    change α.k (π r • y) • Function.surjInv surj b = α.k y • Function.surjInv surj (π r • b)
    rw [α.smul, mul_comm, mul_smul]
    exact key _ _ _ (by rw [semi, e, e])
  · exact key _ _ _ (e _)

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}



end General

section Unique

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

end Unique

section Line

open Polynomial

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)



variable {C : Type} [Category.{0} C]




end Line

end GlobalTheory.Obs.Model
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.Obs.Model

namespace GlobalTheory.LBObs.Model

section Alg

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀}

variable (hI : I ^ 2 = 0)




end Alg

section Example

end Example

section Geo

variable {X : Scheme.{0}} {C : Type} [Category.{0} C]

theorem isCoc_of_isFrame {L : LB X} (hL : L.IsLB) {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
    {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ} (h : IsFrame L V hV u) : IsCoc V hV u := by
  obtain ⟨τ, -, h⟩ := h
  intro T T' T'' a b
  have k : ∀ m, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res inf_le_left (res (hV b) (u T T' a) * u T' T'' b) := fun m ↦ by
    have e1 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (h T T' a m)
    rw [map_mul, h T' T'' b m, LB.res_res, LB.res_res, h T T'' (a ≫ b) m, ← mul_assoc] at e1
    rw [map_mul, LB.res_res]
    exact mul_right_cancel e1
  refine Units.ext (X.sheaf.eq_of_locally_eq' (fun m ↦ V T'' ⊓ L.U m) _ (fun m ↦ homOfLE inf_le_left) ?_ _ _
    fun m ↦ congrArg Units.val (k m))
  rw [← inf_iSup_eq, hL.cover, inf_top_eq]

def Ch (L : LB X) : Type := {p : X.affineOpens × L.ι // p.1.1 ≤ L.U p.2}

instance (L : LB X) : Preorder (Ch L) := Preorder.lift fun p ↦ OrderDual.toDual p.1.1

def chG (L : LB X) : Ch L ⥤ AffOp X where
  obj p := Opposite.op p.1.1
  map a := (homOfLE (leOfHom a)).op

theorem isFrame_ch {L : LB X} (hL : L.IsLB) : IsFrame L (opOf (chG L)) (opOf_le (chG L))
    fun T T' a ↦ res (le_inf T'.2 ((opOf_le (chG L) a).trans T.2)) (L.g T'.1.2 T.1.2) := by
  refine ⟨fun T m ↦ res (le_inf inf_le_right (inf_le_left.trans T.2)) (L.g m T.1.2), fun T m m' ↦ ?_,
    fun T T' a m ↦ ?_⟩
  · exact ((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)
  · exact (((LB.res_res _ _ _).trans (LB.res_cocycle hL _ _ _ _ _ _).symm).trans
      (congrArg (_ * ·) (LB.res_res _ _ _).symm)).trans (mul_comm _ _)

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable {s₀ : X ⟶ Sp R₀}

end Geo

end GlobalTheory.LBObs.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestriction
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObsZero

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

def PCh (P : S.Presents s i) (L : LB X) : Type :=
  {p : X₀.affineOpens × L.ι // GlobalTheory.PresCharts.chartOpen P (Opposite.op p.1) ≤ L.U p.2}

instance (P : S.Presents s i) (L : LB X) : Preorder (PCh P L) := Preorder.lift fun p ↦ OrderDual.toDual p.1.1.1

def pG (P : S.Presents s i) (L : LB X) : PCh P L ⥤ AffOp X₀ where
  obj p := Opposite.op p.1.1
  map a := (homOfLE (leOfHom a)).op

theorem isAffineOpen_chartOpen (P : S.Presents s i) (T : AffOp X₀) :
    IsAffineOpen (GlobalTheory.PresCharts.chartOpen P T) := by
  haveI := P.isOpen T
  unfold GlobalTheory.PresCharts.chartOpen
  exact isAffineOpen_opensRange _

def pH (P : S.Presents s i) (L : LB X) : PCh P L ⥤ GlobalTheory.LBObs.Model.Ch L where
  obj p := ⟨(⟨GlobalTheory.PresCharts.chartOpen P (Opposite.op p.1.1), isAffineOpen_chartOpen P _⟩, p.1.2), p.2⟩
  map {p q} a := homOfLE (GlobalTheory.PresCharts.chartOpen_le P ((pG P L).map a))

theorem isBas_pG (hI : I ^ 2 = 0) (P : S.Presents s i) {L : LB X} (hL : L.IsLB) : IsBas (opOf (pG P L)) := by
  have k : ∀ (x : X₀) (U : X₀.Opens), x ∈ U → ∃ t : PCh P L, x ∈ opOf (pG P L) t ∧ opOf (pG P L) t ≤ U :=
    fun x U hx ↦ by
      obtain ⟨m, hm⟩ := LB.mem_of_cover hL (i x)
      obtain ⟨_, ⟨W, hW, rfl⟩, h1, h2⟩ :=
        X₀.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ ((U ⊓ i ⁻¹ᵁ L.U m : X₀.Opens) : Set X₀) from ⟨hx, hm⟩) (U ⊓ i ⁻¹ᵁ L.U m).isOpen
      refine ⟨⟨(⟨W, hW⟩, m), fun y hy ↦ ?_⟩, h1, fun y hy ↦ (h2 hy).1⟩
      obtain ⟨y₀, hy₀, rfl⟩ := GlobalTheory.PresCharts.exists_of_mem_chartOpen hI P _ y hy
      exact (h2 hy₀).2
  refine ⟨k, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t, h1, h2⟩ := k x (opOf (pG P L) t₁ ⊓ opOf (pG P L) t₂ ⊓ U) ⟨⟨h₁, h₂⟩, hx⟩
  exact ⟨t, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_left))⟩, ⟨homOfLE (h2.trans (inf_le_left.trans inf_le_right))⟩,
    h1, h2.trans inf_le_right⟩

end GlobalTheory.LBObsZero


open GlobalTheory.LBObsZero in
theorem GlobalTheory.LBObs.isObL_pull_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L : LB X), IsPullback i s₀ s (spMap π) → L.IsLB → IsObL S α (L.pull i) 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L h hL
  have hH : ∀ T : PCh P L, opOf (pG P L) T ≤ i ⁻¹ᵁ opOf (GlobalTheory.LBObs.Model.chG L) ((pH P L).obj T) :=
    fun T ↦ GlobalTheory.PresCharts.le_preimage_chartOpen P _
  let w : ∀ (T T' : GlobalTheory.LBObs.Model.Ch L) (_ : T ⟶ T'), Γ(X, opOf (GlobalTheory.LBObs.Model.chG L) T')ˣ :=
    fun T T' a ↦ res (le_inf T'.2 ((opOf_le (GlobalTheory.LBObs.Model.chG L) a).trans T.2)) (L.g T'.1.2 T.1.2)
  have hw : IsFrame L _ _ w := GlobalTheory.LBObs.Model.isFrame_ch hL
  have hfr := isFrame_pull X _ _ _ L w X₀ i (PCh P L) (opOf (pG P L)) (opOf_le (pG P L)) (pH P L) hH hw
  have hcoc := GlobalTheory.LBObs.Model.isCoc_of_isFrame hL hw
  choose σ hσ using fun (T : PCh P L) ↦ GlobalTheory.Obs.Model.exists_isSig hI hπ α (((ofSys S).restrict (pG P L)).p T)
    (Pre.semi _ T) (Pre.surj _ T) (Pre.ker _ T)
  refine ⟨PCh P L, inferInstance, inferInstance, pG P L, isBas_pG hI P hL, _, hfr, ?_⟩
  rw [map_zero]
  refine ⟨fun T T' a ↦ Units.map (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T')).hom.toMonoidHom (w _ _ ((pH P L).map a)),
    σ, 0, fun T T' a ↦ ?_, hσ, (map_zero _).symm, fun T T' T'' a b ↦ ⟨map_zero _, ?_⟩⟩
  · have := congrArg (fun f ↦ f.hom (w _ _ ((pH P L).map a)).val)
      (GlobalTheory.PresCharts.appLE_chartSec P ((pG P L).obj T') (hH T'))
    exact this.symm
  · have e0 : (0 : Z2 (ext R₁ ((pG P L) ⋙ OAff s₀))).1 T T' T'' a b = 0 := rfl
    rw [e0, map_zero, add_zero, _root_.one_mul]
    have e1 := hcoc ((pH P L).map a) ((pH P L).map b)
    rw [← Functor.map_comp] at e1
    have e2 := congrArg (fun f ↦ f.hom (w _ _ ((pH P L).map a)).val)
      (GlobalTheory.PresCharts.res_chartSec P ((pG P L).map b))
    show (mp S.F ((pG P L).map b)) ((GlobalTheory.PresCharts.chartSec P ((pG P L).obj T')).hom (w _ _ ((pH P L).map a)).val) *
        (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T'')).hom (w _ _ ((pH P L).map b)).val =
      (GlobalTheory.PresCharts.chartSec P ((pG P L).obj T'')).hom (w _ _ ((pH P L).map (a ≫ b))).val
    rw [e1, Units.val_mul]
    erw [map_mul]
    congr 1
    exact e2.symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestrictionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_obstruction_zero_of_restriction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L : LB X), IsPullback i s₀ s (spMap π) → L.IsLB → IsObL S α (L.pull i) 0 := by
  first | exact @GlobalTheory.LBObs.isObL_pull_zero | exact GlobalTheory.LBObs.isObL_pull_zero | (intros; apply GlobalTheory.LBObs.isObL_pull_zero <;> assumption)
end
end
