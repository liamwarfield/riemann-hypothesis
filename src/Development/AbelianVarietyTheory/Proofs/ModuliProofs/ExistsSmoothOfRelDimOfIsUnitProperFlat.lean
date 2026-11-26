module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SmoothNearFibre

open GlobalTheory.VeryDenseFibres

private lemma smoothOfRelativeDimension_pullback_snd_restrict {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (W : Z.Opens)
    (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd s t)) :
    SmoothOfRelativeDimension g (pullback.snd (W.ι ≫ s) t) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd s t W.ι,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) h _

private lemma smoothOfRelativeDimension_opensRange_ι_comp' {U Z S : Scheme.{0}} (i : U ⟶ Z) [IsOpenImmersion i] (s : Z ⟶ S)
    (g : ℕ) (h : SmoothOfRelativeDimension g (i ≫ s)) :
    SmoothOfRelativeDimension g (i.opensRange.ι ≫ s) := by
  rw [← i.isoOpensRange_inv_comp, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
  exact h

theorem exists_opens_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}} (s : Z ⟶ Spec R)
    [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
  have hF : Smooth ((pullback.snd s t).fiberToSpecResidueField w) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have hF' : Smooth (s.fiberToSpecResidueField (s z)) := by
    rw [hw]
    exact smooth_fiber_of_smooth_fiber s t w hF
  have hz : z ∈ s.smoothLocus := mem_smoothLocus_of_smooth_fiber s z hF'
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext a
    simp
  have h' : SmoothOfRelativeDimension g (pullback.snd (s.smoothLocus.ι ≫ s) t) :=
    smoothOfRelativeDimension_pullback_snd_restrict s t _ g h
  obtain ⟨V, hV, hVg⟩ :=
    exists_opens_smoothOfRelativeDimension (s.smoothLocus.ι ≫ s) t g h' ⟨z, hz⟩ w (by simpa using hw)
  refine ⟨(V.ι ≫ s.smoothLocus.ι).opensRange, ⟨⟨⟨z, hz⟩, hV⟩, by simp⟩, ?_⟩
  apply smoothOfRelativeDimension_opensRange_ι_comp'
  simpa using hVg

theorem smoothOfRelativeDimension_pullback_snd {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (g : ℕ)
    (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  have hb := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
  have key : ∀ p : ↥(pullback s t), ∃ U : (pullback s t).Opens,
      p ∈ U ∧ SmoothOfRelativeDimension g (U.ι ≫ pullback.snd s t) := by
    intro p
    have hc : s (pullback.fst s t p) = t (pullback.snd s t p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨W, hzW, hW⟩ := h _ _ hc
    let e := pullbackRightPullbackFstIso s t W.ι
    let j := e.inv ≫ pullback.snd W.ι (pullback.fst s t)
    have hj : j ≫ pullback.snd s t = pullback.snd (W.ι ≫ s) t := by
      simp [j, e]
    refine ⟨j.opensRange, ?_, ?_⟩
    · obtain ⟨q, -, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := W.ι) (g := pullback.fst s t) ⟨_, hzW⟩ p (by simp)
      refine ⟨e.hom q, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      simpa [j] using hq2
    · rw [← j.isoOpensRange_inv_comp, Category.assoc, hj,
        MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension g)]
      exact MorphismProperty.pullback_snd _ _ hW
  choose U hU hP using key
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) U ?_ hP
  rw [eq_top_iff]
  intro p _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hU p⟩

theorem exists_smoothOfRelativeDimension_of_isUnit :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  intro R _ _ Z s g K _ x hprop hflat hsm
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := sSup {W : Z.Opens | SmoothOfRelativeDimension g (W.ι ≫ s)}
  have hpt : ∀ w : Sp K, ∀ z : Z, (s z).asIdeal = RingHom.ker x → z ∈ U := by
    intro w z hz
    have hzw : s z = spMap x w := PrimeSpectrum.ext (by rw [hz, spMap_apply_asIdeal])
    obtain ⟨W, hzW, hW⟩ :=
      exists_opens_of_flat (R := CommRingCat.of R) s (spMap x) g hsm z w hzw
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨W, hW, hzW⟩
  let w₀ : Sp K := IsLocalRing.closedPoint K
  let C : Set (Sp R) := s '' (U : Set Z)ᶜ
  have hC : IsClosed C := s.isClosedMap _ U.isOpen.isClosed_compl
  have hp : spMap x w₀ ∈ Cᶜ := by
    rintro ⟨z, hzU, hzp⟩
    apply hzU
    apply hpt w₀ z
    rw [hzp, spMap_apply_asIdeal]
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfC⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hC.isOpen_compl
  refine ⟨f, ?_, ?_⟩
  · intro hf0
    apply hpf
    show f ∈ (spMap x w₀).asIdeal
    rw [spMap_apply_asIdeal]
    exact hf0
  · intro R' _ φ hφ
    apply smoothOfRelativeDimension_pullback_snd
    intro z w hzw
    have hzU : z ∈ U := by
      by_contra hzU
      have hmem : s z ∈ C := ⟨z, hzU, rfl⟩
      apply hfC (PrimeSpectrum.mem_basicOpen _ _ |>.mpr ?_) hmem
      rw [hzw]
      show f ∉ (PrimeSpectrum.comap (CommRingCat.ofHom φ).hom w).asIdeal
      intro hfw
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfw hφ)
    obtain ⟨W, hW, hzW⟩ := TopologicalSpace.Opens.mem_sSup.mp hzU
    exact ⟨W, hzW, hW⟩

end GlobalTheory.SmoothNearFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  first | exact @GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | exact GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | (intros; apply GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantCondition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DiagCoord

theorem exists_linearIndependent_of_iSupIndep {k V I T : Type} [Field k] [AddCommGroup V] [Module k V] [Finite I]
    (W : T → Submodule k V) (hW : iSupIndep W) (ty : I → T)
    (b : ∀ τ, Nonempty (Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ))) :
    ∃ v : I → V, LinearIndependent k v ∧ ∀ i, v i ∈ W (ty i) := by
  classical
  let B : ∀ τ, Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ) := fun τ => (b τ).some
  let e : ∀ τ, {i // ty i = τ} ≃ Fin (Nat.card {i // ty i = τ}) := fun τ => Finite.equivFin _
  let f : ∀ τ, {i // ty i = τ} → V := fun τ j => ((B τ (e τ j) : W τ) : V)
  have hmem : ∀ τ j, f τ j ∈ W τ := fun τ j => (B τ (e τ j)).2
  have hspan : ∀ τ, Submodule.span k (Set.range (f τ)) ≤ W τ := by
    intro τ
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem τ j
  have hsig : LinearIndependent k (fun p : Σ τ, {i // ty i = τ} => f p.1 p.2) := by
    refine linearIndependent_iUnion_finite (fun τ => ?_) (fun τ t _ hτ => ?_)
    · exact ((B τ).linearIndependent.map' (W τ).subtype (Submodule.ker_subtype _)).comp
        (e τ) (e τ).injective
    · exact (hW.disjoint_biSup hτ).mono (hspan τ) (iSup₂_mono fun σ _ => hspan σ)
  let s : I → Σ τ, {i // ty i = τ} := fun i => ⟨ty i, ⟨i, rfl⟩⟩
  have hs : Function.Injective s := fun i j h => congrArg (fun p : Σ τ, {i // ty i = τ} => (p.2 : I)) h
  exact ⟨fun i => f (ty i) ⟨i, rfl⟩, hsig.comp s hs, fun i => hmem (ty i) ⟨i, rfl⟩⟩


open GlobalTheory.Serre ReciprocityTheory.ChartRestriction.G.Chart in
theorem exists_diff_linear {O : Type} [CommRing O] {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (act : OAct O A) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ d : Serre.Lie act →ₗ[ℂ] (Fin g → ℂ), Function.Injective d ∧ ∀ v, u.IsDiff (d v) v.hom := by
  classical
  let dd : Serre.Lie act → (Fin g → ℂ) := fun v => (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose
  have hdd : ∀ v : Serre.Lie act, u.IsDiff (dd v) v.hom := fun v =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose_spec
  have huniq : ∀ (v : Serre.Lie act) (w : Fin g → ℂ), u.IsDiff w v.hom → dd v = w := fun v w hw =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).unique (hdd v) hw
  have hcomb : ∀ (n : ℕ) (r : Fin n → ℂ) (vs : Fin n → Serre.Lie act),
      u.IsDiff (∑ i, r i • dd (vs i)) (∑ i, r i • vs i).hom := fun n r vs =>
    GlobalTheory.UnifDifferential.isDiff_of_isLieComb A L g n u (fun i => dd (vs i)) (fun i => (vs i).hom) r _
      (fun i => GlobalTheory.Serre.Lie.isTangent (vs i)) (fun i => hdd (vs i))
      ((GlobalTheory.Serre.Lie.isLieComb_iff r vs _).2 rfl)
  have hadd : ∀ v w : Serre.Lie act, dd (v + w) = dd v + dd w := by
    intro v w
    apply huniq
    have h2 := hcomb 2 ![1, 1] ![v, w]
    simpa [Fin.sum_univ_two] using h2
  have hsmul : ∀ (c : ℂ) (v : Serre.Lie act), dd (c • v) = c • dd v := by
    intro c v
    apply huniq
    have h1 := hcomb 1 ![c] ![v]
    simpa using h1
  refine ⟨{ toFun := dd, map_add' := hadd, map_smul' := hsmul }, ?_, hdd⟩
  intro v w hvw
  apply GlobalTheory.Serre.Lie.ext
  have hw : u.IsDiff (dd v) w.hom := by
    have := hdd w
    have hvw' : dd v = dd w := hvw
    rwa [← hvw'] at this
  exact (h₂ (dd v)).unique ⟨GlobalTheory.Serre.Lie.isTangent v, hdd v⟩ ⟨GlobalTheory.Serre.Lie.isTangent w, hw⟩

end GlobalTheory.DiagCoord


open GlobalTheory.DiagCoord GlobalTheory.Serre in
theorem GlobalTheory.exists_diagonal_coordinates_of_detCond :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → DetCond D act (𝟙 (Sp ℂ)) H.rt0 → ∃ h : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ (a : 𝓞 E) z, u.ex (h (fun i => ty i (a : E) * z i)) = u.ex (h z) ≫ act.act a := by
  intro _ _ _ _ E _ _ _ H D P u Hm χ act ty _ hty hdet
  unfold DetCond at hdet
  unfold IsTypeFn at hty
  have : IsCommMonObj P.A := Out.PolAV.isCommMonObj P
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u P.smoothDim
  obtain ⟨d, hdinj, hdd⟩ := exists_diff_linear u act h₁ h₂
  let ty' : Fin P.g → (𝓞 E →+* ℂ) := fun i => (ty i).comp (algebraMap (𝓞 E) E)
  have hinj : ∀ τ : 𝓞 E →+* ℂ, Function.Injective τ := by
    intro τ
    refine (RingHom.injective_iff_ker_eq_bot τ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
    ext n
    simp [RingHom.mem_ker]
  have hcard : ∀ τ : 𝓞 E →+* ℂ, ∃ σ : E →+* ℂ, σ (H.rt : E) = τ H.rt ∧
      Nat.card {i // ty' i = τ} = Nat.card {i // ty i = σ} := by
    intro τ
    refine ⟨IsFractionRing.lift (hinj τ), IsFractionRing.lift_algebraMap (hinj τ) H.rt,
      Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun hi => ?_, fun hi => ?_⟩)⟩
    · refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
      exact congrArg (fun f : 𝓞 E →+* ℂ => f x) hi
    · refine RingHom.ext fun x => ?_
      show ty i (algebraMap (𝓞 E) E x) = τ x
      rw [hi]
      exact IsFractionRing.lift_algebraMap (hinj τ) x
  have hb : ∀ τ : 𝓞 E →+* ℂ,
      Nonempty (Module.Basis (Fin (Nat.card {i // ty' i = τ})) ℂ (GlobalTheory.Serre.Lie.eig act τ)) := by
    intro τ
    obtain ⟨σ, hσ, hc⟩ := hcard τ
    refine (GlobalTheory.Serre.Lie.lieMult_id_iff act τ _).1 ?_
    rw [hc]
    by_cases hτ : τ H.rt = H.rt0
    · rw [(hty σ).1 (hσ.trans hτ)]
      exact (hdet τ).1 hτ
    · rw [(hty σ).2 (fun h => hτ (hσ.symm.trans h))]
      exact (hdet τ).2 hτ
  obtain ⟨v, hvli, hvmem⟩ :=
    exists_linearIndependent_of_iSupIndep (GlobalTheory.Serre.Lie.eig act) (GlobalTheory.Serre.Lie.iSupIndep_eig act) ty' hb
  choose F hF using fun a : 𝓞 E =>
    GlobalTheory.exists_linear_lift_of_isMonHom_polAV P P P.L P.L u u (act.act a) (act.hom a)
  have key : ∀ (a : 𝓞 E) (i : Fin P.g), F a (d (v i)) = ty i (a : E) • d (v i) := by
    intro a i
    have := act.hom a
    have e1 := GlobalTheory.HomLinear.isDiff_comp u u (act.act a) (F a) (hF a)
      (GlobalTheory.Serre.Lie.isTangent (v i)) (hdd (v i))
    have hv : a • v i = ty' i a • v i := (GlobalTheory.Serre.Lie.mem_eig_iff.1 (hvmem i)) a
    have e2 : (ty' i a • v i).hom = (v i).hom ≫ act.act a := by
      rw [← hv, GlobalTheory.Serre.Lie.hom_act_smul]
    rw [← e2] at e1
    have e3 := hdd (ty' i a • v i)
    rw [map_smul] at e3
    exact (h₁ _ (GlobalTheory.Serre.Lie.isTangent _)).unique e1 e3
  have hli : LinearIndependent ℂ (d ∘ v) := hvli.map' d (LinearMap.ker_eq_bot.2 hdinj)
  let B : Module.Basis (Fin P.g) ℂ (Fin P.g → ℂ) :=
    basisOfLinearIndependentOfCardEqFinrank' (d ∘ v) hli (by simp)
  have hB : ∀ i, B i = d (v i) := fun i => by simp [B]
  refine ⟨B.equivFun.symm, fun a z => ?_⟩
  rw [← hF a]
  refine congrArg u.ex ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hB, key, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantConditionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_coordinates_of_determinantCondition : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → DetCond D act (𝟙 (Sp ℂ)) H.rt0 → ∃ h : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ (a : 𝓞 E) z, u.ex (h (fun i => ty i (a : E) * z i)) = u.ex (h z) ≫ act.act a := by
  first | exact @GlobalTheory.exists_diagonal_coordinates_of_detCond | exact GlobalTheory.exists_diagonal_coordinates_of_detCond | (intros; apply GlobalTheory.exists_diagonal_coordinates_of_detCond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreconnectedSpacePtsOfIsIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.OpenSubgroupPts

open GlobalTheory.Points

theorem isPreconnected_affineOpen {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p]
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsPreconnected {x : Pts p | ⊤ ≤ x.1 ⁻¹ᵁ U} := by
  have key : ∀ {R : CommRingCat.{0}} [IsDomain R] (q : Spec R ⟶ Sp ℂ) [LocallyOfFiniteType q],
      PreconnectedSpace (Pts q) := by
    intro R _ q hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact FiniteClasses.preconnectedSpace_pts R
  have := key (hU.fromSpec ≫ p)
  have h := isPreconnected_range (PtsOver.continuous_map (C := ℂ) hU.fromSpec (q := p) rfl (𝟙 _))
  rw [PtsOver.range_map, range_comp_of_isOpenImmersion, hU.opensRange_fromSpec] at h
  exact h

theorem preconnectedSpace_pts_of_isIntegral {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ)
    [LocallyOfFiniteType p] : PreconnectedSpace (Pts p) := by
  refine ⟨isPreconnected_of_forall_pair fun x _ y _ => ?_⟩
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_le x.1 (le_preimage_top _)
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top _)
  have hx' := (le_preimage_iff x.1 U).1 hx
  have hy' := (le_preimage_iff y.1 V).1 hy
  have : Nonempty U := ⟨⟨_, hx'⟩⟩
  have : Nonempty V := ⟨⟨_, hy'⟩⟩
  obtain ⟨z, hz, hzm⟩ := ComplexPoints.exists_point_mem p (Z := (U : Set Y) ∩ V)
    (U.isOpen.inter V.isOpen).isLocallyClosed
    (nonempty_preirreducible_inter U.isOpen V.isOpen ⟨_, hx'⟩ ⟨_, hy'⟩)
  exact ⟨_, Set.subset_univ _, Or.inl hx, Or.inr hy, IsPreconnected.union (⟨z, hz⟩ : Pts p)
    ((le_preimage_iff z U).2 (hzm _).1) ((le_preimage_iff z V).2 (hzm _).2)
    (isPreconnected_affineOpen p hU) (isPreconnected_affineOpen p hV)⟩

theorem subgroup_eq_top_of_nhds_one :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤ := by
  intro X G _ x H U κ _ f O hs hc hO h1 h1O hH
  let p := pullback.snd G.hom x
  have : IsIntegral (pullback G.hom x) :=
    isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback G.hom x)
  have := preconnectedSpace_pts_of_isIntegral p
  let Y : Over X := Over.mk (p ≫ x)
  let π : Y ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  let s : Y ⟶ Over.mk x := Over.homMk p rfl
  let inc : Pts p → (Over.mk x ⟶ Y) := fun y => Over.homMk y.1 (by
    show y.1 ≫ p ≫ x = x
    rw [← Category.assoc, y.2, Category.id_comp])
  have hin : ∀ y, inc y ≫ s = 𝟙 _ := fun y => Over.OverMorphism.ext y.2
  have hsurj : ∀ a : Over.mk x ⟶ G, ∃ y, inc y ≫ π = a := fun a =>
    ⟨⟨pullback.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp x).symm), pullback.lift_snd _ _ _⟩,
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hopen : IsOpen {z : Sp ℂ ⟶ G.left | ⊤ ≤ z ⁻¹ᵁ U ∧ (fun j => valAt' z U (f j)) ∈ O} :=
    (continuousOn_pi.2 fun j => continuousOn_valR (C := ℂ) (f j)).isOpen_inter_preimage
      (isOpen_setOf_le_preimage U) hO
  have hl : IsLocallyConstant fun y : Pts p => inc y ≫ π ∈ H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    let τ : Y ⟶ G := (s ≫ (inc y₀ ≫ π)⁻¹) * π
    have hτ : ∀ y, inc y ≫ τ = (inc y₀ ≫ π)⁻¹ * (inc y ≫ π) := fun y => by
      rw [MonObj.comp_mul, ← Category.assoc, hin, Category.id_comp]
    have hcont : Continuous fun y : Pts p => (show Sp ℂ ⟶ G.left from (inc y ≫ τ).left) :=
      (continuous_comp (C := ℂ) (X := pullback G.hom x) τ.left).comp continuous_subtype_val
    have hN := (hopen.preimage hcont).mem_nhds (x := y₀) (by
      simp only [Set.mem_preimage, hτ, inv_mul_cancel]
      exact ⟨h1, h1O⟩)
    filter_upwards [hN] with y hy
    have h := hH _ hy.1 hy.2
    rw [hτ] at h
    have h' := H.mul_mem_cancel_right (y := inc y₀ ≫ π) h
    rw [mul_inv_cancel_left] at h'
    exact propext h'
  rw [eq_top_iff]
  intro a _
  obtain ⟨y, rfl⟩ := hsurj a
  obtain ⟨y₁, hy₁⟩ := hsurj 1
  have h := hl.apply_eq_of_preconnectedSpace y y₁
  simp only [hy₁] at h
  rw [h]
  exact H.one_mem

end GlobalTheory.OpenSubgroupPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOpensSmoothOfRelativeDimensionOfFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ProperFlatNearFibre

theorem exists_opens_smoothOfRelativeDimension_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}}
    (s : Z ⟶ Spec R) [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  have hz : z ∈ s.smoothLocus := by
    refine GlobalTheory.VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
    exact GlobalTheory.VeryDenseFibres.smooth_fiber_of_smooth_fiber s t w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))
  have : Smooth (s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (s.smoothLocus.ι ≫ s) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (s.smoothLocus.ι ≫ s) t g (by simpa using h2) ⟨z, hz⟩ w hw
  let j := W.ι ≫ s.smoothLocus.ι
  refine ⟨j.opensRange, ⟨⟨⟨z, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : j.opensRange.ι ≫ s = j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + g)
      (j.isoOpensRange.inv ≫ (W.ι ≫ s.smoothLocus.ι ≫ s)) := inferInstance
  rw [e]
  simpa using h3

theorem smoothOfRelativeDimension_pullback_snd {Z T S : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S)
    (g : ℕ) (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → (pullback s t).Opens :=
    fun W => pullback.fst s t ⁻¹ᵁ W.1
  have htop : iSup V = ⊤ := by
    rw [← top_le_iff]
    intro y _
    obtain ⟨W, hW, hW'⟩ := h (pullback.fst s t y) (pullback.snd s t y) (by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
    fun W => ?_
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{0} g)
    ((isPullback_morphismRestrict (pullback.fst s t) W.1).paste_vert
      (IsPullback.of_hasPullback s t)) W.2

theorem exists_away_smoothOfRelativeDimension :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s g K _ x hs hf h
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := ⨆ W : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)}, W.1
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  let w : Sp K := (default : PrimeSpectrum K)
  have hp : spMap x w ∈ (s '' (U : Set Z)ᶜ)ᶜ := by
    rintro ⟨z, hz, e⟩
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_flat s (spMap x) g h z w e
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩)
  obtain ⟨_, ⟨f, rfl⟩, hf1, hf2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp
      hc.isOpen_compl
  refine ⟨f, ?_, smoothOfRelativeDimension_pullback_snd _ _ g fun z y e => ?_⟩
  · have h1 : f ∉ (spMap x w).asIdeal := hf1
    rwa [GlobalTheory.VeryDenseFibres.spMap_apply_asIdeal, RingHom.mem_ker] at h1
  · have h1 : s z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨y, e.symm⟩
    have h2 : z ∈ U := by
      by_contra hz
      exact hf2 h1 ⟨z, hz, rfl⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩

end GlobalTheory.ProperFlatNearFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.RigidLinearisation

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem gs_one {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) : gs f y ⊤ (1 : Γ(X, ⊤)) = 1 := by
  rw [gs_eq _ y ⊤ trivial, map_one, map_one]

theorem gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (c : Γ(X, ⊤)) (n : ℕ) : gs f y ⊤ (c ^ n) = gs f y ⊤ c ^ n := by
  rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_pow, map_pow]

theorem exists_good' {X Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem val_eq_of_rigid {X Y S : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : S ⟶ Y) (he : ∀ c : Γ(Y, ⊤), (e.app ⊤).hom c = 1 → c = 1)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨c, hc⟩ := exists_ratio hM hF hu hu'
  have c1 : c = 1 := he c (fn_ext (V := ⊤) fun y _ => by
    obtain ⟨I, hI⟩ := exists_good' hM y
    have := hc _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 S) e y ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← this]
    exact (gs_one (𝟙 S) y).symm)
  have := hc Z r z J hJ
  rw [c1, gs_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gen_of_iso {Y : Scheme.{0}} (L : LB Y) (τ : Y ⟶ Y) (h : LBIso L (L.pull τ)) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), t.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j ≤ (L.pull τ).U (fun _ => j 1) ⊓ L.U (j 0) :=
    fun j y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy 1), Set.mem_iInter.1 hy 0⟩
  refine ⟨⟨fun j => (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j : Fin 2 → L.ι, y ∈ LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j →
      gm (𝟙 Y) y (LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j) (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹ =
        (gw w (𝟙 Y) y (j 1) (j 0))⁻¹ := fun j hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 Y) y (le j) hj _))
  refine (v j hj).trans (Eq.trans ?_ (congrArg (_ * ·) (v j' hj')).symm)
  rw [hp Y (𝟙 Y) y (j 1) (j' 1) (j 0) (j' 0) (Set.mem_iInter.1 hj 1) (Set.mem_iInter.1 hj' 1)
    (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0), trF, Fin.prod_univ_two]
  show _ = gm (𝟙 Y ≫ 𝟙 Y) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 Y ≫ τ) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) * _
  rw [Category.id_comp (𝟙 Y), zpow_one, zpow_neg_one, mul_inv, mul_inv, inv_inv, mul_comm (_⁻¹) (gm (𝟙 Y) y _ _)]

theorem exists_normalised {X Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : Y ⟶ X) (e : X ⟶ Y) (he : e ≫ p = 𝟙 X)
    (ρ : X ⟶ X) (τ : Y ⟶ Y) (hτ : e ≫ τ = ρ ≫ e) (r : (L.pull e).Gen) (hr : r.IsGen) (h : LBIso L (L.pull τ)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ X) (z : Z) (J), Good L z J →
        val u (b ≫ e) z J = val r b z J * (val r (b ≫ ρ) z J)⁻¹ := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso L τ h
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![𝟙 Y, τ]) (ε' := ![1, -1]) (fun U _ k => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fintype.prod_unique,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc, hτ, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (p ≫ e))))
      (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ r p) (LB.invGen L _ _ (LB.pullGen L _ _ r (p ≫ ρ)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _))))
  refine ⟨u, hu, fun Z b z J hJ => ?_⟩
  have e₁ : (b ≫ e) ≫ p = b := by rw [Category.assoc, he, Category.comp_id]
  rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ,
    ← Category.assoc (b ≫ e) p e, ← Category.assoc (b ≫ e) p ρ, e₁, mul_inv_cancel, _root_.one_mul]

theorem exists_const {k : Type} [Field k] [IsAlgClosed k] {F : Scheme.{0}} [IsIntegral F] (q : F ⟶ Sp k)
    (c : Γ(F, ⊤)) {n : ℕ} (hn : n ≠ 0) (hc : c ^ n = 1) : ∃ a : Γ(Sp k, ⊤), (q.app ⊤).hom a = c := by
  let f : k →+* Γ(F, ⊤) := (q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Splits := IsAlgClosed.splits _
  have hm : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Monic := Polynomial.monic_X_pow_sub_C _ hn
  have e := congrArg (Polynomial.eval₂ f c) (hs.eq_prod_roots_of_monic hm)
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at e
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one, hc, sub_self,
    Polynomial.eval₂_one] at e
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 e.symm)
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at ha
  exact ⟨_, (sub_eq_zero.1 ha).symm⟩

theorem exists_linearisation : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left) (ρ : Γ →* Aut X) (τ : Γ →* Aut P.left) (L : LB P.left), e ≫ P.hom = 𝟙 X → GeometricallyIntegral P.hom → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → (∀ g, (τ g).asIso.hom ≫ P.hom = P.hom ≫ (ρ g).asIso.hom ∧ e ≫ (τ g).asIso.hom = (ρ g).asIso.hom ≫ e) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst P.hom x ≫ (τ g).asIso.hom = pullback.fst P.hom x) → L.IsLB → (∃ r : (L.pull e).Gen, r.IsGen) → (∀ g, LBIso L (L.pull (τ g).asIso.hom)) → ∃ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 P.left, (τ g).asIso.hom] ![1, -1]), (∀ g, (u g).IsGen) ∧ (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).asIso.hom))) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ P.left) g, y ≫ (τ g).asIso.hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L) := by
  intro Γ _ _ X P e ρ τ L he hgi hrig hcomm hfix hL ⟨r, hr⟩ hiso
  choose u hu hn using fun g => exists_normalised hL P.hom e he (ρ g).asIso.hom (τ g).asIso.hom (hcomm g).2 r hr (hiso g)
  have rig : ∀ c : Γ(P.left, ⊤), (e.app ⊤).hom c = 1 → c = 1 := fun c hc =>
    hrig ⊤ c le_top (by
      have : e.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ le_top = e.app ⊤ := (e.app_eq_appLE (U := ⊤)).symm
      rw [this]; exact hc)
  have τm : ∀ g h, (τ (h * g)).asIso.hom = (τ g).asIso.hom ≫ (τ h).asIso.hom := fun g h => by rw [map_mul]; rfl
  have ρm : ∀ g h, (ρ (h * g)).asIso.hom = (ρ g).asIso.hom ≫ (ρ h).asIso.hom := fun g h => by rw [map_mul]; rfl
  have coc : ∀ g h (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → val (u (h * g)) s z J =
      val (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).asIso.hom)) s z J := fun g h =>
    val_eq_of_rigid hL (fun U _ k => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, τm, Category.comp_id]
        simp) e rig (hu _)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hu g) (DVR.pullGen_isGen _ _ _ _ (hu h) _)) (fun y J hJ => by
        have a₁ := hn (h * g) X (𝟙 X) y J hJ
        have a₂ := hn g X (𝟙 X) y J hJ
        have a₃ := hn h X (ρ g).asIso.hom y J hJ
        simp only [Category.id_comp] at a₁ a₂
        rw [val_mul hJ, val_pull hJ, (hcomm g).2, a₁, a₂, a₃, ρm]
        simp)
  refine ⟨u, hu, fun g h => corr_of_val hL fun y J hJ => coc g h _ _ y J hJ, fun k _ _ y g hy => ?_⟩
  have hx : (y ≫ P.hom) ≫ (ρ g).asIso.hom = y ≫ P.hom := by
    rw [Category.assoc, ← (hcomm g).1, ← Category.assoc, hy]
  have hf := hfix k _ g hx
  have : IsIntegral (pullback P.hom (y ≫ P.hom)) :=
    hgi.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  obtain ⟨c, hc⟩ := exists_ratio hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ k => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hf, Category.comp_id]
      simp)
    (DVR.pullGen_isGen _ _ _ _ (hu g) (pullback.fst P.hom (y ≫ P.hom))) (u' := LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.one_mul _)).symm)
  have hc' : ∀ (Z : Scheme.{0}) (s : Z ⟶ pullback P.hom (y ≫ P.hom)) (z : Z) (J), Good L z J →
      (val (u g) (s ≫ pullback.fst _ _) z J).val = gs s z ⊤ c := fun Z s z J hJ => by
    rw [← hc Z s z J hJ, val_pull hJ, val_one, inv_one, _root_.mul_one]
  have pw : ∀ (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → s ≫ (τ g).asIso.hom = s →
      val (u g) s z J ^ orderOf g = 1 := fun Z s z J hJ hs => by
    have one : val (u 1) s z J = 1 := by
      have := coc 1 1 Z s z J hJ
      rw [val_mul hJ, val_pull hJ, _root_.mul_one, show s ≫ (τ 1).asIso.hom = s by rw [map_one]; exact Category.comp_id s] at this
      exact mul_eq_left.1 this.symm
    have all : ∀ n : ℕ, val (u (g ^ n)) s z J = val (u g) s z J ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero, pow_zero, one]
      | succ n ih => rw [pow_succ, coc g (g ^ n) Z s z J hJ, val_mul hJ, val_pull hJ, hs, ih, pow_succ']
    rw [← all, pow_orderOf_eq_one, one]
  have cn : c ^ orderOf g = 1 := fn_ext fun z _ => by
    obtain ⟨J, hJ⟩ := exists_good' hL z
    rw [gs_pow, gs_one, ← hc' _ _ z J hJ, ← Units.val_pow_eq_pow_val,
      pw _ _ z J hJ (by rw [Category.assoc, hf]), Units.val_one]
  obtain ⟨a, ha⟩ := exists_const (pullback.snd P.hom (y ≫ P.hom)) c (orderOf_pos g).ne' cn
  have sec : ∀ (s : Sp k ⟶ pullback P.hom (y ≫ P.hom)) (z : Sp k), s ≫ pullback.snd _ _ = 𝟙 _ →
      gs s z ⊤ c = gs (𝟙 _) z ⊤ a := fun s z hs => by
    rw [← ha, ← hs]
    exact gs_pull s _ z ⊤ trivial a
  refine corr_of_val hL fun z J hJ => Units.ext ?_
  have b₁ := hc' _ (pullback.lift y (𝟙 _) (Category.id_comp _).symm) z J hJ
  have b₂ := hc' _ (pullback.lift ((y ≫ P.hom) ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])) z J hJ
  rw [sec _ z (pullback.lift_snd _ _ _), pullback.lift_fst] at b₁ b₂
  rw [hn g _ _ z J hJ, hx, mul_inv_cancel] at b₂
  rw [val_pull hJ, Category.id_comp, val_one, b₁, b₂]

end GlobalTheory.RigidLinearisation
end
