module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFac

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsogFiniteFlat

open GlobalTheory.UnramifiedEndFlat GlobalTheory.FiniteEndFlat

theorem apply_genericPoint_of_comp {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (g : Y ⟶ X) [LocallyQuasiFinite g]
    (h : g (f (genericPoint X)) = genericPoint X) : f (genericPoint X) = genericPoint Y := by
  have hs := strictMono_of_locallyQuasiFinite g
  have h1 : genericPoint Y ⤳ f (genericPoint X) := genericPoint_specializes _
  have h2 : g (genericPoint Y) ⤳ genericPoint X := by
    rw [← h]; exact h1.map g.continuous
  have h3 : g (genericPoint Y) = genericPoint X :=
    (h2.antisymm (genericPoint_specializes _)).eq
  by_contra hne
  have hlt : f (genericPoint X) < genericPoint Y := lt_of_le_not_ge h1 fun h' =>
    hne (h1.antisymm (show f (genericPoint X) ⤳ genericPoint Y from h')).eq.symm
  have := hs hlt
  rw [h3, h] at this
  exact lt_irrefl _ this

theorem flat_of_isFinite_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj G'] [IsIntegral G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') (φ' : G' ⟶ G)
    [IsMonHom φ] [IsMonHom φ'] [IsFinite φ.left] [IsFinite φ'.left] :
    Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  let o : G.left := η[G].left (IsLocalRing.closedPoint K)
  have hfo : (φ.left ≫ φ'.left) o = o := by
    have : η[G] ≫ (φ ≫ φ') = η[G] := IsMonHom.one_hom (φ ≫ φ')
    rw [← Over.comp_left]
    exact congr(($this).left (IsLocalRing.closedPoint K))
  have hξ0 := apply_genericPoint (φ.left ≫ φ'.left) hfo
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left :=
    apply_genericPoint_of_comp φ.left φ'.left (by simpa using hξ0)
  obtain ⟨W, hW, H⟩ := exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

end GlobalTheory.IsogFiniteFlat

namespace GlobalTheory.IsogFiniteFlat

theorem isFinite_and_flat_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A]
    [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' →
    ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c →
      ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  intro S _ A A' _ _ _ _ hA hA' ψ ψ' c hc _ _ h1 h2
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 hc
  obtain ⟨hfA, -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A hA c hc1
  obtain ⟨hfA', -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A' hA' c hc1
  have := hA.proper
  have := hA.smooth
  have := hA'.proper
  have := hA'.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp _ A.hom
  haveI : IsSeparated (ψ.left ≫ A'.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated ψ.left := IsSeparated.of_comp _ A'.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact hfA
  haveI : IsFinite (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hfA'
  have hf : IsFinite ψ.left := IsFinite.of_comp _ ψ'.left
  have hf' : IsFinite ψ'.left := IsFinite.of_comp _ ψ.left
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S A A' ψ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hB' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A' hA'
  have := hB.smooth
  have := hB'.smooth
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A).hom hB.smooth hB.geomConnected
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _
    ((Over.pullback t).obj A').hom hB'.smooth hB'.geomConnected
  have : IsIntegral ((Over.pullback t).obj A).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A).hom
  have : IsIntegral ((Over.pullback t).obj A').left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A').hom
  haveI : IsFinite ((Over.pullback t).map ψ).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ) hf
  haveI : IsFinite ((Over.pullback t).map ψ').left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t ψ') hf'
  exact flat_of_isFinite_grpHom K _ _ ((Over.pullback t).map ψ) ((Over.pullback t).map ψ')

end GlobalTheory.IsogFiniteFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverseStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_flat_abelianSchemeHom_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c → ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  first | (exact @GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (exact GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (intros; apply GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativeAdditiveCommutator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativeAdditiveCommutator
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisDerivLaws

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

noncomputable def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

lemma evI_eq (a : AF F) : evI F a = evIHom a := rfl

lemma evI_realAd' (r : ℝ) : evI F (realAd F r) = algebraMap ℝ (mixedEmbedding.mixedSpace F) r := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ r)) = _
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

noncomputable def trPair (w : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℂ where
  toFun y := ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * w i) : ℝ) : ℂ)
  map_add' a b := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _), Complex.ofReal_add]
  map_smul' c a := by
    simp [smul_mul_assoc, ← Finset.smul_sum, Complex.real_smul]

lemma trPair_apply (w y : κ → mixedEmbedding.mixedSpace F) :
    trPair w y = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * w i) : ℝ) : ℂ) := rfl

lemma trPair_add (w w' y : κ → mixedEmbedding.mixedSpace F) :
    trPair (w + w') y = trPair w y + trPair w' y := by
  simp only [trPair_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _), Complex.ofReal_add]

lemma trPair_smul (r : ℝ) (w y : κ → mixedEmbedding.mixedSpace F) :
    trPair (r • w) y = (r : ℂ) * trPair w y := by
  simp [trPair_apply, mul_smul_comm, ← Finset.smul_sum]

lemma hasFDerivAt_trPair (w x : κ → mixedEmbedding.mixedSpace F) :
    HasFDerivAt (fun y => trPair w y) (LinearMap.toContinuousLinearMap (trPair w)) x :=
  (LinearMap.toContinuousLinearMap (trPair w)).hasFDerivAt

lemma fderiv_step (f : SInf F κ) (c : ℂ) (w v' x v : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (fun y => fderiv ℝ (⇑f) y v' - c * trPair w y * f y) x v =
      fderiv ℝ (fderiv ℝ (⇑f)) x v v' - c * (trPair w x * fderiv ℝ (⇑f) x v + f x * trPair w v) := by
  have hf2 : DifferentiableAt ℝ (fderiv ℝ (⇑f)) x :=
    ((f.smooth ⊤).fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable
      one_ne_zero x
  have h1 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y v')
      ((fderiv ℝ (⇑f) x).comp 0 + (fderiv ℝ (fderiv ℝ (⇑f)) x).flip v') x :=
    hf2.hasFDerivAt.clm_apply (hasFDerivAt_const v' x)
  have h2 := ((hasFDerivAt_trPair w x).const_mul c).mul (f.differentiableAt (x := x)).hasFDerivAt
  have h3 : HasFDerivAt (fun y => fderiv ℝ (⇑f) y v' - c * trPair w y * f y) _ x := h1.sub h2
  rw [h3.fderiv]
  simp
  ring

lemma evV_add (a b : κ → AF F) :
    (fun i => evI F ((a + b) i)) = (fun i => evI F (a i)) + (fun i => evI F (b i)) := by
  funext i
  show evI F (a i + b i) = evI F (a i) + evI F (b i)
  rw [evI_eq, map_add (f := _)]; rfl

lemma evV_smul (r : ℝ) (a : κ → AF F) :
    (fun i => evI F ((realAd F r • a) i)) = r • (fun i => evI F (a i)) := by
  funext i
  show evI F (realAd F r * a i) = r • evI F (a i)
  rw [evI_eq, map_mul, ← evI_eq, ← evI_eq, evI_realAd', Algebra.smul_def]

lemma isSymm (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) : IsSymmSndFDerivAt ℝ (⇑f) x :=
  ((f.smooth ⊤).contDiffAt).isSymmSndFDerivAt (by simp)

theorem heis_deriv_laws : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    (∀ u u', At (evI F) u → At (evI F) u' → D (u + u') = D u + D u') ∧
    (∀ u (r : ℝ), At (evI F) u → D (realAd F r • u) = (r : ℂ) • D u) ∧
    (∀ u u', At (evI F) u → At (evI F) u' → ∀ f, D u (D u' f) - D u' (D u f) =
      ((-2 * Real.pi * Complex.I : ℂ) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ)) • f) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ JA JB d D hD
  have at_add : ∀ u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' h h' a ha => by rw [smul_add, h a ha, h' a ha, add_zero]
  have at_smul : ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : AF F), At (evI F) u → At (evI F) (r • u) :=
    fun u r h a ha => by rw [smul_comm, h a ha, smul_zero]
  have hD' : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ (⇑f) x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        trPair (fun i => evI F ((d.e u).2 i)) x * f x := hD
  refine ⟨fun u u' hu hu' => ?_, fun u r hu => ?_, fun u u' hu hu' f => ?_⟩
  · ext f x
    rw [ContinuousLinearMap.add_apply, SchwartzMap.add_apply, hD' _ (at_add u u' hu hu'), hD' u hu,
      hD' u' hu', map_add, Prod.fst_add, Prod.snd_add, evV_add, evV_add, map_add, trPair_add]
    ring
  · ext f x
    rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, hD' _ (at_smul u _ hu), hD' u hu,
      map_smul, Prod.smul_fst, Prod.smul_snd, evV_smul, evV_smul, map_smul, trPair_smul]
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  · have e : ⇑(D u f) = fun y => fderiv ℝ (⇑f) y (fun i => evI F ((d.e u).1 i)) -
        2 * Real.pi * Complex.I * trPair (fun i => evI F ((d.e u).2 i)) y * f y := funext (hD' u hu f)
    have e' : ⇑(D u' f) = fun y => fderiv ℝ (⇑f) y (fun i => evI F ((d.e u').1 i)) -
        2 * Real.pi * Complex.I * trPair (fun i => evI F ((d.e u').2 i)) y * f y :=
      funext (hD' u' hu' f)
    have key : ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ) =
        trPair (fun i => evI F ((d.e u').2 i)) (fun i => evI F ((d.e u).1 i)) -
        trPair (fun i => evI F ((d.e u).2 i)) (fun i => evI F ((d.e u').1 i)) := by
      rw [d.form u u', evI_eq, map_sub]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_sum, map_mul, ← evI_eq, trPair_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, Complex.ofReal_sub]
    ext x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, hD' u hu (D u' f), hD' u' hu' (D u f), e', e,
      fderiv_step, fderiv_step, (isSymm f x).eq (fun i => evI F ((d.e u').1 i)), key, smul_eq_mul]
    ring

end GlobalTheory.HeisDerivLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativeAdditiveCommutatorStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archHeisenbergDerivative_additive_commutator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    (∀ u u', At (evI F) u → At (evI F) u' → D (u + u') = D u + D u') ∧
    (∀ u (r : ℝ), At (evI F) u → D (realAd F r • u) = (r : ℂ) • D u) ∧
    (∀ u u', At (evI F) u → At (evI F) u' → ∀ f, D u (D u' f) - D u' (D u f) =
      ((-2 * Real.pi * Complex.I : ℂ) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) : ℝ) : ℂ)) • f) := by
  first | exact @GlobalTheory.HeisDerivLaws.heis_deriv_laws | exact GlobalTheory.HeisDerivLaws.heis_deriv_laws | (intros; apply GlobalTheory.HeisDerivLaws.heis_deriv_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem natCast_notMem_of_not_dvd [StarRing K] (w : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ m) : (m : 𝓞 K) ∉ w.asIdeal := by
  intro h
  apply hm
  have h1 : ((m : ℕ) : 𝓞 K ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  unfold Formalism.EigenvalueLevelCeiling.plc
  exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) m).1 h1

theorem factor_mem (w : HeightOneSpectrum (𝓞 K)) (p e n : ℕ) (ν : Fin n → ℕ)
    (hpw : ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 K) ∉ w.asIdeal) (hI : Formalism.CohomologicalDescent.LA.InclZ n n le_rfl ν p e) :
    ∀ f ∈ (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν).map (toK K (Fin n × Fin n)),
      ((p : K) ^ e) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
        ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K (Fin n × Fin n))) := by
  obtain ⟨m, hm, hmx⟩ := hI
  have hm0 : (m : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hm (dvd_zero p)
  have hval : w.valuation K ((m : K)⁻¹) ≤ 1 := by
    have h1 : w.valuation K (algebraMap (𝓞 K) K (m : 𝓞 K)) = 1 :=
      (w.valuation_eq_one_iff_notMem).2 (hpw m hm)
    rw [map_natCast] at h1
    rw [map_inv₀, h1, inv_one]
  rintro _ ⟨g, hg, rfl⟩
  rw [GlobalTheory.StdDual.dualWeyl_eq, ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))] at hg
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨b, hb, rfl⟩ := hq
    have hbD : b ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.subset_span hb
    have h1 := GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) le_rfl ν _ (hmx b hbD)
    have h2 := GlobalTheory.JetOpWeylLat.smul_mem_localizationAt_of_valuation w hval (Submodule.mem_map_of_mem (f := toK K (Fin n × Fin n)) h1)
    convert h2 using 1
    rw [GlobalTheory.JetOpWeylLat.toK_map_int, GlobalTheory.JetOpWeylLat.toK_map_int, map_zsmul, ← Int.cast_smul_eq_zsmul K,
      smul_smul]
    congr 1
    push_cast
    field_simp
  | zero => simpa using zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add (f := _), smul_add]
    exact add_mem ha hb
  | smul a g _ hg =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ a hg

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem tensor_mem (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (c : K)
    (e : ι → ℕ)
    (h : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      (c ^ e τ) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)))) :
    ∀ z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      (c ^ ∑ τ, e τ) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  classical
  have key : ∀ y ∈ nabStd K lam, (c ^ ∑ τ, e τ) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro y hy
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hy
    induction hy using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨F, hF, rfl⟩ := hP
      choose t ht hFt using fun τ => (lc_mem_locP w _ _).1 (h τ (F τ) (hF τ))
      have hnot : (∏ τ, t τ) ∉ w.asIdeal :=
        Submonoid.prod_mem w.asIdeal.primeCompl (t := Finset.univ) (f := t) (fun τ _ => ht τ)
      refine (lc_mem_locP w _ _).2 ⟨∏ τ, t τ, hnot, ?_⟩
      have hFt' : ∀ τ, (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ ∈
          (delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)) := fun τ => by
        have e1 : t τ • c ^ e τ • F τ = (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ :=
          (algebraMap_smul K (t τ) _).symm.trans (smul_smul _ _ _)
        convert hFt τ using 1
        exact e1.symm
      have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) ∈ delStd K lam :=
        Submodule.subset_span ⟨_, hFt', rfl⟩
      have e2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) =
          ((algebraMap (𝓞 K) K (∏ τ, t τ)) * c ^ ∑ τ, e τ) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ) := by
        simp only [map_smul, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod, map_mul,
          Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.rename_C]
        congr 2
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
      rw [e2] at hmem
      convert hmem using 1
      exact (algebraMap_smul K (∏ τ, t τ) _).symm.trans (smul_smul _ _ _)
    | zero => simpa using zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul a y _ hy =>
      have e3 : (c ^ ∑ τ, e τ) • a • y = a • (c ^ ∑ τ, e τ) • y := smul_comm _ _ _
      convert Submodule.smul_mem _ a hy using 1
      exact e3
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (lc_mem_locP w _ _).1 hz
  obtain ⟨t, ht, htz⟩ := (lc_mem_locP w _ _).1 (key _ hsz)
  refine (lc_mem_locP w _ _).2 ⟨t * s, lc_mul_notMem w ht hs, ?_⟩
  convert htz using 1
  exact (mul_smul t s _).trans (congrArg (t • ·) (smul_comm s _ z))

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

theorem exZ_sum_smul_mem_locP_delAtr :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ)
      (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsFullLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L,
        (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  intro E K _ _ _ _ _ ι _ n emb lam L hL w x hx
  have hM : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ L)) := fun τ =>
    du_dualFr_lattice basisAtEx _ (tauLatLattice E K ι n emb τ L hL)
  choose B hB using fun τ => basisAtEx K n _ (hM τ) w
  have hx1 : (x : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ L)) :=
    lc_le_locP w _ hx
  rw [(nabDelLoc K ι n lam _ hM w B hB).1] at hx1
  obtain ⟨z, hz, hzx⟩ := hx1
  have hfac : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      ((Formalism.EigenvalueLevelCeiling.plc w : K) ^ Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w)) • f ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n))) := fun τ =>
    factor_mem w (Formalism.EigenvalueLevelCeiling.plc w) _ n (lam τ).natW (fun m hm => natCast_notMem_of_not_dvd w hm)
      (Formalism.CohomologicalDescent.LA.exact_z_specialization n n le_rfl _ (natW_antitone _) _ (Formalism.EigenvalueLevelCeiling.plc_prime w))
  have hz' := tensor_mem w lam (Formalism.EigenvalueLevelCeiling.plc w : K) _ hfac z hz
  refine (GlobalTheory.LvT.Built.ValLat.mem_localization_delAtr emb lam w hL B hB _).2 ⟨_, hz', ?_⟩
  have e1 : (actP lam B) z = (x : Pol K ι n) := hzx
  rw [map_smul, e1]
  refine (algebraMap_smul K (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^
    (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) (x : Pol K ι n)).symm.trans ?_
  simp only [map_pow, map_natCast]

end GlobalTheory.OntoExponentsLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeft
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open Matrix
namespace GlobalTheory.AdelMatLat

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (v : Fin n → E) : ∃ d : ℤ, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by
    let _ := hL
    rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := L)]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, h₁, hx⟩ := hx
    obtain ⟨d₂, h₂, hy⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, ?_⟩
    have : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [this]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    let o : 𝓞 E := ⟨m • e, (hint e (Finset.mem_singleton_self e) :)⟩
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    have : (m * d) • (e • x) = o • (d • x) := by
      have ho : algebraMap (𝓞 E) E o = m • e := rfl
      rw [← algebraMap_smul E o (d • x), ho, smul_assoc, smul_comm e d x, mul_smul]
    rw [this]
    exact L.smul_mem o hx

theorem exists_int_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) : ∃ D : ℤ, D ≠ 0 ∧ ∀ x ∈ L, D • (N *ᵥ x) ∈ L := by
  obtain ⟨s, hs⟩ := hL.toIsLattice.fg
  choose d hd hdm using fun g : Fin n → E => exists_int_smul_mem L hL (N *ᵥ g)
  refine ⟨∏ g ∈ s, d g, Finset.prod_ne_zero_iff.2 fun g _ => hd g, ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := ((∏ g ∈ s, d g) • N.mulVecLin).restrictScalars (𝓞 E)
  have hf : ∀ x, f x = (∏ g ∈ s, d g) • (N *ᵥ x) := fun x => rfl
  have hle : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ L.comap f := by
    rw [Submodule.span_le]
    intro g hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, hf]
    classical
    rw [← Finset.mul_prod_erase s d hg, mul_comm, mul_smul]
    exact zsmul_mem (hdm g) _
  intro x hx
  rw [← hs] at hx
  have := hle hx
  rwa [Submodule.mem_comap, hf] at this

theorem incM_zsmul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m k : Type}
    (D : ℤ) (V : Matrix m k E) : incM F (D • V) = (algebraMap F (AF F) (D : F)) • incM F V := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul, algebraMap_smul, Int.cast_smul_eq_zsmul]

theorem smul_incM_mul_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (c : AF F) (N : Matrix (Fin n) (Fin n) E) (D : ℤ) (hD0 : D ≠ 0)
    (hD : ∀ x ∈ X.L, D • (N *ᵥ x) ∈ X.L) (w : Pl (F := F))
    (hw : evFin F w (c * algebraMap F (AF F) (D : F)⁻¹) ∈ w.adicCompletionIntegers F) :
    ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
    have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD0
    have heq : (c • incM F N) * (a • incM F (Matrix.vecMulVec x y)) =
        ((c * algebraMap F (AF F) (D : F)⁻¹) * a) • incM F (Matrix.vecMulVec (D • (N *ᵥ x)) y) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_vecMulVec, incM_zsmul, smul_smul,
        ← Matrix.mul_vecMulVec]
      have hm : incM F (N * Matrix.vecMulVec x y) = incM F N * incM F (Matrix.vecMulVec x y) := by
        simp only [incM, Matrix.map_mul]
      rw [hm]
      congr 1
      rw [mul_right_comm, mul_assoc c, ← map_mul, inv_mul_cancel₀ hDF, map_one, mul_one]
    rw [heq]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, hD x hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hw hint
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem finite_not_integral {F : Type} [Field F] [NumberField F] (c : AF F) :
    {w : Pl (F := F) | evFin F w c ∉ w.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.1 c.2.2

theorem finite_bad_smul_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsFullLattice E) (c : AF F) (N : Matrix (Fin n) (Fin n) E) :
    {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w}.Finite := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mulVec_mem X.L hX N
  refine (finite_not_integral (c * algebraMap F (AF F) (D : F)⁻¹)).subset ?_
  intro w hw hint
  exact hw (smul_incM_mul_stable X Y c N D hD0 hD w hint)

theorem almost_all_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), X.L.IsFullLattice E → ∀ M : Matrix (Fin n) (Fin n) (AE F E),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hX M
  let bad : Matrix (Fin n) (Fin n) (AE F E) → Set (Pl (F := F)) :=
    fun M => {w | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w}
  have hadd : ∀ M M', (bad M).Finite → (bad M').Finite → (bad (M + M')).Finite := by
    intro M M' h h'
    refine (h.union h').subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, not_or, bad, Set.mem_setOf_eq, not_not] at hc hw
    exact hw fun γ hγ => by rw [Matrix.add_mul]; exact add_mem (hc.1 γ hγ) (hc.2 γ hγ)
  have hzero : (bad 0).Finite := by
    refine Set.finite_empty.subset fun w hw => hw fun γ _ => ?_
    rw [Matrix.zero_mul]; exact zero_mem _
  have hsingle : ∀ i j (t : AE F E), (bad (Matrix.single i j t)).Finite := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a e =>
      have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
        ext k l
        simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply]
        split_ifs <;> simp [inclR, TensorProduct.smul_tmul']
      rw [h]
      exact finite_bad_smul_incM X Y hX a _
    | add t t' ht ht' => rw [Matrix.single_add]; exact hadd _ _ ht ht'
  show (bad M).Finite
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun i _ =>
    Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun j _ => hsingle i j _

end GlobalTheory.AdelMatLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeftStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → ∀ M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  exact @GlobalTheory.AdelMatLat.almost_all_stable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalCongruenceBackTriangularFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalCongruenceBackTriangularFrame
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.CongrOrbit


set_option maxHeartbeats 4000000 in
theorem exists_congr_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 1 ≤ r → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ η : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ η ∧ (∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (η : Matrix (Fin r) (Fin r) E) w - w = (l.M : E) • y) ∧ ∃ b ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor (U.X k).Ψ r, x = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact η (ReciprocityTheory.ChartRestriction.G.FD.lact γ x)) b := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hA _hr k γ hγ x hx
  have hx' : lact γ x ∈ (U.X k).dom := dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)

  let b₁ : Frame (U.X k).Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hm₁ : ∀ τ, mat b₁ τ = 1 := fun τ => rfl
  have hb₁ : b₁ ∈ Bor (U.X k).Ψ r := fun τ => ⟨by rw [hm₁]; simp, fun a c hca => by
    have := hm₁ τ
    change Matrix.of (b₁ τ) = 1 at this
    have h2 := congrFun (congrFun this a) c
    simpa [Matrix.one_apply_ne (ne_of_gt hca)] using h2⟩
  have hrm : rmul (lact γ x) b₁ = lact γ x := by
    funext τ
    change mat (lact γ x) τ * mat b₁ τ = lact γ x τ
    rw [hm₁, Matrix.mul_one]
    rfl
  obtain ⟨t, hB⟩ : ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k ⟨x, hx⟩) (U.un k ⟨lact γ x, hx'⟩) :=
    (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨lact γ x, hx'⟩).2 ⟨γ, hγ, b₁, hb₁, by rw [hrm]⟩
  obtain ⟨hrr, hty, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k ⟨lact γ x, hx'⟩
  have hu : F.u (ik k) P' = F.u (ik k) P := by rw [← hPx, ← hPx', hB.1]
  obtain ⟨h, gam, hex, hh, hiso, hM, -⟩ := GlobalTheory.T.familyUnif_exp_unique_alt E H Dw l Xo _ g _ F (ik k) (ik k) P' P p' p hu

  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := F.t_surj (ik k) b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di (ik k)) l gam hiso hM'

  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P p _ ((U.un k ⟨x, hx⟩).u τ) _ (hv τ)
      (cf τ i) ((U.un k ⟨lact γ x, hx'⟩).u τ i)).1 (hPx ▸ hcf3 τ i)
    have d0 := hv' τ i
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P p) h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P p
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  let gm : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k).Λ := (φ k).symm ≪≫ₗ gam ≪≫ₗ φ k
  let A : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ i j =>
    if hij : i < Dw.mult τ ∧ j < Dw.mult τ then Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0
  have hA0 : ∀ τ i j, j < i → A τ i j = 0 := by
    intro τ i j hji
    simp only [A]
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  have hAr : ∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x (gm v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i =
        ∑ j ∈ Finset.range (Dw.mult τ), A τ i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j := by
    intro τ i hi v
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P' v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP', Equiv.apply_symm_apply]
    simp only [A]
    rw [dite_eq_left ⟨hi, j.2⟩]
    rfl
  have hgiso : ∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (gm u : Fin r → E)
      (gm v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E)) := by
    intro u v
    obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [gm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]

  obtain ⟨η, ε, -, hξ, hav, hlat, hisoη⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k) (fun _ => rfl) gm hgiso
  have hε : ε = 1 := mul_right_cancel₀ (U.X k).ξ0_ne (hξ.symm.trans (one_mul _).symm)
  have hUS : IsUStab (U.X k).Gm (U.X k).Λ η := ⟨fun u v => by rw [hisoη, hε, one_mul], hlat⟩
  have hcong : ∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ,
      (η : Matrix (Fin r) (Fin r) E) *ᵥ w - w = (l.M : E) • y := by
    intro w hw
    obtain ⟨a, ha⟩ := (φ k).surjective ⟨w, hw⟩
    obtain ⟨e₀, he₀⟩ := f₁ a
    refine ⟨(φ k e₀ : Fin r → E), (φ k e₀).2, ?_⟩
    have h1 := hav ⟨w, hw⟩
    have h2 : gm ⟨w, hw⟩ = ⟨w, hw⟩ + l.M • φ k e₀ := by
      simp only [gm, LinearEquiv.trans_apply, ← ha, LinearEquiv.symm_apply_apply, he₀, map_add (f := _), map_nsmul]
    rw [h2] at h1
    change (η : Matrix (Fin r) (Fin r) E) *ᵥ w = _ at h1
    rw [h1]
    simp [Nat.cast_smul_eq_nsmul]

  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  let ρe := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (ρe.symm τ) = τ := ρe.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (ρe.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (ρe.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (ρe.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k) x ((η : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (ρe.symm τ)), A (ρe.symm τ) i j *
          Formalism.L2.PjFree.perFr (U.X k) (lact γ x) v τ j :=
    fun τ i hi v hv => by
      have := hAr (ρe.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  obtain ⟨b, hb, hxb, -⟩ := GlobalTheory.T.frames_differ_by_isometry_and_triangular_of_periods E r (U.X k) (U.X k) η (isMatch_of_isUStab (U.X k) hUS)
    (fun τ => Dw.mult (ρe.symm τ)) m1 m2 (lact γ x) hx' x hx (fun τ => A (ρe.symm τ))
    (fun τ => hA0 _) hrel
  exact ⟨η, hUS, hcong, b, hb, hxb⟩

end GlobalTheory.CongrOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalCongruenceBackTriangularFrameStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_congruence_back_triangular_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → l.A = 1 → 1 ≤ r → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ η : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab (U.X k).Gm (U.X k).Λ η ∧ (∀ w ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (η : Matrix (Fin r) (Fin r) E) w - w = (l.M : E) • y) ∧ ∃ b ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor (U.X k).Ψ r, x = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact η (ReciprocityTheory.ChartRestriction.G.FD.lact γ x)) b := by
  first | exact @GlobalTheory.CongrOrbit.exists_congr_back | exact GlobalTheory.CongrOrbit.exists_congr_back | (intros; apply GlobalTheory.CongrOrbit.exists_congr_back <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasureTwo
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory

namespace GKConjScale

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_eq_ofAdd_ordL {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold ordL
  rw [dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem coe_mul_le_iff (g h : Multiplicative ℤ) (x : WithZero (Multiplicative ℤ)) :
    (g : WithZero (Multiplicative ℤ)) * x ≤ h ↔ x ≤ ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro H
    calc x = ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * (g * x) := by
          rw [← mul_assoc, ← WithZero.coe_mul, inv_mul_cancel, WithZero.coe_one, one_mul]
      _ ≤ ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * h := by gcongr
      _ = _ := by rw [WithZero.coe_mul]
  · intro H
    calc (g : WithZero (Multiplicative ℤ)) * x ≤ g * ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ = h := by rw [WithZero.coe_mul, ← mul_assoc, ← WithZero.coe_mul, mul_inv_cancel, WithZero.coe_one, one_mul]

variable {n : ℕ}

theorem inv_offdiag {σ : L →+* L} (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i j : Fin n) (hij : i ≠ j) :
    (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  rw [Subgroup.coe_inv, (GlobalTheory.LGrp.mem_GU_iff σ n _).1 t.2 i j,
    ht _ _ (fun h => hij (Fin.rev_injective h).symm), map_zero]


end GKConjScale

end GlobalTheory
end
end
