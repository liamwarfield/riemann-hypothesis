module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section
namespace GlobalTheory.Poinc.FieldConj
open GlobalTheory.Points RatModel
open scoped Pointwise

theorem eq_of_val_eq_fibre {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {X : Scheme.{0}}
    (q : M.Z ⟶ X) [IsAffineHom q] {K : Type} [Field K] (y y' : Sp K ⟶ M.Z) (hyy : y ≫ q = y' ≫ q)
    (h : ∀ b ∈ M.ringOn {z | q z = (y ≫ q) (IsLocalRing.closedPoint K)}, M.val y b = M.val y' b) : y = y' := by
  set x := (y ≫ q) (IsLocalRing.closedPoint K) with hx
  have hxz : q (y (IsLocalRing.closedPoint K)) = x := rfl
  have hxz' : q (y' (IsLocalRing.closedPoint K)) = x := by rw [hx, hyy]; rfl
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsub : ∀ a ∈ M.ringOn (q ⁻¹ᵁ V : Set M.Z), a ∈ M.ringOn {z | q z = x} := by
    have hsubset : {z : M.Z | q z = x} ⊆ (q ⁻¹ᵁ V : Set M.Z) := by
      intro z hz
      change q z ∈ V
      rw [hz]
      exact hxV
    exact fun a ha => M.ringOn_anti hsubset ha
  have hzU : y (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz]; exact hxV
  have hzU' : y' (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz']; exact hxV
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)

  have hinv : ∀ {w : Sp K ⟶ M.Z} (hw : Set.range w = {w (IsLocalRing.closedPoint K)}) {a : Ω},
      a ∈ M.O (w (IsLocalRing.closedPoint K)) → a ≠ 0 → (a⁻¹ ∈ M.O (w (IsLocalRing.closedPoint K)) ↔ M.val w a ≠ 0) := by
    intro w hw a ha h0
    rw [val_ne_zero_iff hw ⟨a, ha⟩, isUnit_O_iff]
    exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  have hpt : y (IsLocalRing.closedPoint K) = y' (IsLocalRing.closedPoint K) := by
    refine GlobalTheory.Points.point_eq_of_inv_mem_iff o Ω M _ hU _ _ hzU hzU' fun a ha h0 => ?_
    rw [hinv hr (M.ringOn_le_O hzU ha) h0, hinv hr' (M.ringOn_le_O hzU' ha) h0, h a (hsub a ha)]
  set z := y (IsLocalRing.closedPoint K) with hz
  have hO : ∀ a ∈ M.O z, M.val y a = M.val y' a := by
    intro a ha
    obtain ⟨c, hc, d, hd, hd0, hdi, rfl⟩ :=
      GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine o Ω M _ hU z hzU a ha
    have hsp : ∀ w, y w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
    have hsp' : ∀ w, y' w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K), hpt]
    have hcz := M.ringOn_le_O hzU hc
    have hdz := M.ringOn_le_O hzU hd
    have hq : c / d ∈ M.O z := ha
    have e1 := val_mul hsp hq hdz
    have e1' := val_mul hsp' hq hdz
    rw [div_mul_cancel₀ c hd0] at e1 e1'
    have hne : M.val y d ≠ 0 := (hinv hr hdz hd0).1 hdi
    have hne' : M.val y' d ≠ 0 := by rw [← h d (hsub d hd)]; exact hne
    rw [eq_div_of_mul_eq hne e1.symm, eq_div_of_mul_eq hne' e1'.symm, h c (hsub c hc), h d (hsub d hd)]
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local hpt fun W h₁ h₂ => ?_
  have hW : z ∈ W := h₁ (x := IsLocalRing.closedPoint K) trivial
  ext f
  have e1 := val_valF ((top_le_preimage_iff y W).1 h₁) f
  have e2 := val_valF ((top_le_preimage_iff y' W).1 h₂) f
  have e3 := hO _ (valF_mem_O hW f)
  rw [e1, e2] at e3
  unfold valF at e3
  rw [dite_eq_left h₁, dite_eq_left h₂] at e3
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e3

theorem galConj : ∀ (A F L K : Type) [CommRing A] [IsDomain A] [Field F] [Field L] [Field K] [CharZero K] [Algebra A F] [IsFractionRing A F] [IsIntegrallyClosed A] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [IsGalois F L] (B : Subring L), (∀ b : L, b ∈ B ↔ IsIntegral A b) → ∀ e e' : B →+* K, (∀ b : B, (∃ a : A, algebraMap A L a = b) → e b = e' b) → ∃ σ : L ≃ₐ[F] L, ∀ b c : B, (c : L) = σ b → e' b = e c := by
  intro A F L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ B hB e e' hA
  classical
  have hσB : ∀ (σ : L ≃ₐ[F] L) (b : L), b ∈ B → σ b ∈ B := fun σ b hb =>
    (hB _).2 (IsIntegral.map ((σ : L →ₐ[F] L).restrictScalars A) ((hB b).1 hb))
  let σB : (L ≃ₐ[F] L) → B →+* B := fun σ =>
    ((σ : L →+* L).comp B.subtype).codRestrict B fun b => hσB σ b b.2
  have hσB_apply : ∀ σ (b : B), ((σB σ b : B) : L) = σ b := fun _ _ => rfl

  have claim : ∀ b : B, ∃ σ : L ≃ₐ[F] L, e' b = e (σB σ b) := by
    intro b
    let P : Polynomial B := ∏ σ : L ≃ₐ[F] L, (Polynomial.X - Polynomial.C (σB σ b))
    have hPmap : ∀ τ : L ≃ₐ[F] L, (P.map B.subtype).map (τ : L →+* L) = P.map B.subtype := by
      intro τ
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
      rfl
    have hcoeff : ∀ n, ∃ a : A, algebraMap A L a = (P.coeff n : L) := by
      intro n
      have hfix : ∀ τ : L ≃ₐ[F] L, τ (P.coeff n : L) = P.coeff n := by
        intro τ
        have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) (hPmap τ)
        simpa [Polynomial.coeff_map] using this
      obtain ⟨f, hf⟩ := (IsGalois.mem_bot_iff_fixed (P.coeff n : L)).2 hfix
      change algebraMap F L f = _ at hf
      have hint : IsIntegral A (algebraMap F L f) := by rw [hf]; exact (hB _).1 (P.coeff n).2
      have hint' : IsIntegral A f := by
        rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A F L) (algebraMap F L).injective]
        exact hint
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
      exact ⟨a, by rw [IsScalarTower.algebraMap_apply A F L, ha, hf]⟩
    have hmap : P.map e = P.map e' := by
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      obtain ⟨a, ha⟩ := hcoeff n
      exact hA _ ⟨a, ha⟩
    have h0 : (P.map e').eval (e' b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [sub_eq_zero]; exact Subtype.ext rfl), map_zero]
    rw [← hmap] at h0
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨σ, -, hσ⟩ := Finset.prod_eq_zero_iff.1 h0
    exact ⟨σ, sub_eq_zero.1 hσ⟩
  let H : (L ≃ₐ[F] L) → AddSubgroup B := fun σ =>
    (e'.toAddMonoidHom - (e.comp (σB σ)).toAddMonoidHom).ker
  have hmemH : ∀ σ (b : B), b ∈ H σ ↔ e' b = e (σB σ b) := fun σ b => by
    simp [H, AddMonoidHom.mem_ker, sub_eq_zero]
  have hcover : ⋃ σ ∈ (Finset.univ : Finset (L ≃ₐ[F] L)), (0 : B) +ᵥ ((H σ : AddSubgroup B) : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨σ, hσ⟩ := claim b
    refine Set.mem_iUnion₂.2 ⟨σ, Finset.mem_univ _, ?_⟩
    rw [zero_vadd]
    exact (hmemH σ b).2 hσ
  obtain ⟨σ, -, hfin⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcover
  refine ⟨σ, fun b c hc => ?_⟩
  have hcσ : c = σB σ b := Subtype.ext hc
  subst hcσ
  have hn : (H σ).index ≠ 0 := hfin.index_ne_zero
  have hmem := (hmemH σ _).1 (AddSubgroup.nsmul_index_mem (H σ) b)
  rw [map_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hmem
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) hmem

theorem val_algebraMap_of_comp {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
    [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z}
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {K : Type} [Field K] (y : Sp K ⟶ M₂.Z) {x : Ω₁}
    (hx : x ∈ M₁.O ((y ≫ q) (IsLocalRing.closedPoint K))) :
    M₂.val y (algebraMap Ω₁ Ω₂ x) = M₁.val (y ≫ q) x := by
  obtain ⟨U, f, hzU, rfl⟩ := hx
  have h1 : Set.range (y ≫ q) ⊆ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  have h2 : Set.range y ⊆ q ⁻¹ᵁ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  rw [← GlobalTheory.Poinc.FinPts.valF_app hg ⟨_, hzU⟩ f, val_valF h2, val_valF h1]
  exact (valR_comp y q U f).symm

theorem exists_aut_eq_of_comp_eq : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ _ _ M₁ M₂ q hN₁ hN₂ hF hg K _ _ y y' hyy
  set z₁ := (y ≫ q) (IsLocalRing.closedPoint K) with hz₁
  haveI : IsIntegrallyClosed (M₁.O z₁) := isIntegrallyClosed_O hN₁ z₁
  let B : Subring Ω₂ := (M₂.ringOn {z | q z = z₁}).toSubring
  have hB : ∀ b : Ω₂, b ∈ B ↔ IsIntegral (M₁.O z₁) b := by
    intro b
    letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
    have h1 := (GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg z₁).1 b
    have h2 : IsIntegral (M₁.Z.presheaf.stalk z₁) b ↔ IsIntegral (M₁.O z₁) b := by
      constructor
      · intro hb
        exact IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).toRingHom (RingHom.id Ω₂) (RingHom.ext fun _ => rfl) hb
      · intro hb
        refine IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).symm.toRingHom (RingHom.id Ω₂) (RingHom.ext fun x => ?_) hb
        show algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ ((M₁.stalkEquiv z₁).symm x)) = algebraMap Ω₁ Ω₂ (x : Ω₁)
        rw [← coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [← h2, ← mem_integralClosure_iff, h1, Subalgebra.mem_toSubring, mem_ringOn]
    rfl
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)
  have hz : q (y (IsLocalRing.closedPoint K)) = z₁ := rfl
  have hz' : q (y' (IsLocalRing.closedPoint K)) = z₁ := by rw [hz₁, hyy]; rfl
  let e : B →+* K := (M₂.valHom y _ hr).comp
    (Subring.inclusion (show B ≤ (M₂.O (y (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz))
  let e' : B →+* K := (M₂.valHom y' _ hr').comp
    (Subring.inclusion (show B ≤ (M₂.O (y' (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz'))
  have he : ∀ b : B, e b = M₂.val y b := fun _ => rfl
  have he' : ∀ b : B, e' b = M₂.val y' b := fun _ => rfl
  have hA : ∀ b : B, (∃ a : M₁.O z₁, algebraMap (M₁.O z₁) Ω₂ a = b) → e b = e' b := by
    rintro b ⟨a, hab⟩
    rw [he, he', ← hab]
    show M₂.val y (algebraMap Ω₁ Ω₂ a) = M₂.val y' (algebraMap Ω₁ Ω₂ a)
    rw [val_algebraMap_of_comp hg y a.2, val_algebraMap_of_comp hg y' (by rw [← hyy]; exact a.2), hyy]
  obtain ⟨σ, hσ⟩ := galConj (M₁.O z₁) Ω₁ Ω₂ K B hB e e' hA
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.Poinc.GalAut.autAct o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg σ
  haveI := hF
  have key : y ≫ s = y' := by
    refine eq_of_val_eq_fibre M₂ q (y ≫ s) y' (by rw [Category.assoc, hs2, hyy]) fun b hb => ?_
    have hys : (y ≫ s) ≫ q = y ≫ q := by rw [Category.assoc, hs2]
    rw [hys] at hb
    have hbB : b ∈ B := hb
    have hσB : σ b ∈ B := (hB _).2
      (IsIntegral.map ((σ : Ω₂ →ₐ[Ω₁] Ω₂).restrictScalars (M₁.O z₁)) ((hB b).1 hbB))
    rw [hs3]
    exact (hσ ⟨b, hbB⟩ ⟨σ b, hσB⟩ rfl).symm
  refine ⟨σ, s, hs1, key, fun b => ?_⟩
  rw [← key]
  exact hs3 K y b

end GlobalTheory.Poinc.FieldConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_aut_conjugate_field_points_cover : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  first | exact @GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq | exact GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq | (intros; apply GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackCh
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackCh
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ q) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = bcPull w (fv f) := by
  intro R R' _ _ σ X X' q w m f
  unfold fv bcPull
  rfl

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackChStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback_changeOfBase : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ q) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = bcPull w (fv f) := by
  first | exact @GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase | exact GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase | (intros; apply GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ptAlg_apply_of_left {R D E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]
    (z : Pt (SpAlg R D) E) (f : D →+* E) (h : z.left = spMap f) (a : D) : ptAlg z a = f a := by
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom a = f a
  rw [h, Spec.preimage_map]
  rfl

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.bcPull_sumMul_fv : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D]
    (B : Over (Sp R)) (B' : Over (Sp D)) (q : B'.left ⟶ (SpAlg R D ⊗ B).left)
    (w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)) (π : B'.left ⟶ B.left),
    q ≫ (fst (SpAlg R D) B).left = B'.hom → q ≫ (snd (SpAlg R D) B).left = π →
    ∀ (mB : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 D) (B'.hom ≫ 𝟙 _) (algebraMap R D) π)
      (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))),
      bcPull w (sumMul d fun i ↦ fv (X := B) (β i)) =
        fv (X := B') (∑ i, d i • mB.coef.pullbackOneCocycle (β i)) := by
  classical
  intro R D _ _ _ B B' q w π hfst hsnd mB J _ d β
  have w' : π ≫ B.hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← hsnd, Category.assoc, Over.w (snd (SpAlg R D) B), w]
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  funext E i1 i2 E' i3 i4 ψ y
  have hzero : fv (X := B') 0 E E' ψ y = 0 := by
    have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd 0 0)
    simp only [add_zero, Fn1.add] at h
    linear_combination -h
  have hsum : ∀ s : Finset J, fv (X := B') (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)) E E' ψ y =
      ∑ i ∈ s, algebraMap D E' (d i) * fv (X := B') (mB.coef.pullbackOneCocycle (β i)) E E' ψ y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd (d j • mB.coef.pullbackOneCocycle (β j)) (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)))
      simp only [Fn1.add] at h
      rw [h, ih, hsmul]
  rw [hsum]
  simp only [bcPull, sumMul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback_changeOfBase R D (algebraMap R D) B B' π w' mB (β i)]
  congr 1
  · let _ : Algebra R E := algVia (algebraMap R D) E
    have hl : (ptVia w y ≫ fst (SpAlg R D) B).left = spMap (algebraMap D E) := by
      rw [Over.comp_left]
      change (y.left ≫ q) ≫ (fst (SpAlg R D) B).left = _
      rw [Category.assoc, hfst]
      exact Over.w y
    rw [ptAlg_apply_of_left _ _ hl]
    exact ψ.commutes (d i)
  · simp only [bcPull]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    change (y.left ≫ q) ≫ (snd (SpAlg R D) B).left = y.left ≫ π
    rw [Category.assoc, hsnd]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEqStatement
theorem GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq :
    type_of% (@GlobalTheory.PtExt.bcPull_sumMul_fv) :=
  @GlobalTheory.PtExt.bcPull_sumMul_fv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactor
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.CubeIso

section

variable {X X₁ X₂ Y : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

theorem mem_ext {x : X} {j₁ : L₁.ι} {j₂ : L₂.ι} (h₁ : f₁ x ∈ L₁.U j₁) (h₂ : f₂ x ∈ L₂.U j₂) :
    x ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) :=
  ⟨mem_pull.2 h₁, mem_pull.2 h₂⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂') :
    gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
        (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂'))
      ((extLB L₁ L₂ f₁ f₂).g (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂')) =
      gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') * gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') := by
  have hm : r z ∈ (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓
      (extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂') := ⟨mem_ext h₁ h₂, mem_ext h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hm _).trans ?_) ((gm_res r z _ hm _).trans ?_))
  · exact gm_pull_g L₁ f₁ r z (fun _ => j₁) (fun _ => j₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g L₂ f₂ r z (fun _ => j₂) (fun _ => j₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

def ev (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j₁ : L₁.ι) (j₂ : L₂.ι) (k : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂) ⊓ L.U k)
    (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k))

theorem ev_trans {w : LB.Iso L (extLB L₁ L₂ f₁ f₂)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z)
    (j₁ j₁' : L₁.ι) (j₂ j₂' : L₂.ι) (k k' : L.ι)
    (h₁ : f₁ (r z) ∈ L₁.U j₁) (h₁' : f₁ (r z) ∈ L₁.U j₁') (h₂ : f₂ (r z) ∈ L₂.U j₂) (h₂' : f₂ (r z) ∈ L₂.U j₂')
    (h : r z ∈ L.U k) (h' : r z ∈ L.U k') :
    ev w r z j₁ j₂ k = gm (r ≫ f₁) z (L₁.U j₁ ⊓ L₁.U j₁') (L₁.g j₁ j₁') *
      gm (r ≫ f₂) z (L₂.U j₂ ⊓ L₂.U j₂') (L₂.g j₂ j₂') * (gm r z (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        ev w r z j₁' j₂' k' := by
  rw [← gm_ext_g r z j₁ j₁' j₂ j₂' h₁ h₁' h₂ h₂']
  exact AdjComp.gm_iso hw r z (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, k) (extIdx (f₁ := f₁) (f₂ := f₂) j₁' j₂', k')
    ⟨mem_ext h₁ h₂, h⟩ ⟨mem_ext h₁' h₂', h'⟩

theorem exists_linComb (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (w₀ : LB.Iso L (extLB L₁ L₂ f₁ f₂))
    (hw₀ : w₀.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ₁ : K → (Y ⟶ X₁)) (ε : K → ℤ) (σ : K → K)
    (h₁ : ∀ k, φ k ≫ f₁ = φ₁ k) (h₂ : ∀ k, φ k ≫ f₂ = φ (σ k) ≫ f₂)
    (hε : ∀ (G : Type) [CommGroup G] (a : K → G), (∀ k, a k = a (σ k)) → ∏ k, a k ^ ε k = 1) :
    ∃ w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L₁ φ₁ ε), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (jC : K → L₁.ι) (jA : K → L.ι) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ φ₁ jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) →
        gm f z (LB.wchart L₁ φ₁ jC ⊓ LB.wchart L φ jA) (w.s (jC, jA)) =
          ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
  obtain rfl : (fun k => φ k ≫ f₁) = φ₁ := funext h₁
  have cover : ∀ y : Y, ∃ β : K → L₂.ι, (∀ k, f₂ (φ k y) ∈ L₂.U (β k)) ∧ ∀ k, β k = β (σ k) := fun y => by
    choose c hc using exists_chart hL₂
    exact ⟨fun k => c ((φ k ≫ f₂) y), fun k => hc _, fun k => congrArg (fun q : Y ⟶ X₂ => c (q y)) (h₂ k)⟩
  have glue : ∀ (jC : K → L₁.ι) (jA : K → L.ι),
      ∃ s : Γ(Y, LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (β : K → L₂.ι),
        f z ∈ LB.wchart L₁ (fun k => φ k ≫ f₁) jC → f z ∈ LB.wchart L φ jA → (∀ k, f₂ (φ k (f z)) ∈ L₂.U (β k)) →
        (∀ k, β k = β (σ k)) → gm f z _ s = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β k) (jA k) ^ ε k := by
    intro jC jA
    let W : {β : K → L₂.ι // ∀ k, β k = β (σ k)} → Y.Opens := fun β =>
      LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA ⊓ LB.wchart L₂ (fun k => φ k ≫ f₂) β.1
    have l₀ : ∀ β, W β ≤ LB.wchart L₁ (fun k => φ k ≫ f₁) jC ⊓ LB.wchart L φ jA := fun β => inf_le_left
    have l₁ : ∀ β k, W β ≤ φ k ⁻¹ᵁ
        ((extLB L₁ L₂ f₁ f₂).U (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k)) ⊓ L.U (jA k)) := fun β k y hy =>
      ⟨mem_ext (Set.mem_iInter.1 hy.1.1 k) (Set.mem_iInter.1 hy.2 k), Set.mem_iInter.1 hy.1.2 k⟩
    let u : ∀ β, Γ(Y, W β)ˣ := fun β => ∏ k, res (l₁ β k)
      (pullU (φ k) _ (w₀.s (extIdx (f₁ := f₁) (f₂ := f₂) (jC k) (β.1 k), jA k))) ^ ε k
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) β (hz : f z ∈ W β),
        gm f z (W β) (u β) = ∏ k, ev w₀ (f ≫ φ k) z (jC k) (β.1 k) (jA k) ^ ε k := fun Z f z β hz =>
      (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res f z (l₁ β k) hz _).trans (gm_pull f (φ k) z _ (l₁ β k hz) _))))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun y hy => by
        obtain ⟨β, hβ, hβ'⟩ := cover y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨β, hβ'⟩, hy, Set.mem_iInter.2 hβ⟩) u (fun β β' y hy => by
        rw [hu _ (𝟙 Y) y β hy.1, hu _ (𝟙 Y) y β' hy.2]
        have a : ∀ k, ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β.1 k) (jA k) =
            gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k)) *
              ev w₀ (𝟙 Y ≫ φ k) y (jC k) (β'.1 k) (jA k) := fun k => by
          have m₁ : f₁ (φ k y) ∈ L₁.U (jC k) := Set.mem_iInter.1 hy.1.1.1 k
          have m : φ k y ∈ L.U (jA k) := Set.mem_iInter.1 hy.1.1.2 k
          rw [Category.id_comp, ev_trans hw₀ (φ k) y (jC k) (jC k) (β.1 k) (β'.1 k) (jA k) (jA k) m₁ m₁
            (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k) m m, gm_self hL₁ (φ k ≫ f₁) y m₁,
            gm_self hL (φ k) y m, _root_.one_mul, inv_one, _root_.mul_one]
        simp only [a, mul_zpow, Finset.prod_mul_distrib]
        rw [hε _ (fun k => gm (φ k ≫ f₂) y (L₂.U (β.1 k) ⊓ L₂.U (β'.1 k)) (L₂.g (β.1 k) (β'.1 k))) (fun k => by
          have key : ∀ (q q' : Y ⟶ X₂) (i i' j j' : L₂.ι), q = q' → i = i' → j = j' →
              gm q y (L₂.U i ⊓ L₂.U j) (L₂.g i j) = gm q' y (L₂.U i' ⊓ L₂.U j') (L₂.g i' j') := by
            rintro _ _ _ _ _ _ rfl rfl rfl; rfl
          exact key _ _ _ _ _ _ (h₂ k) (β.2 k) (β'.2 k)), _root_.one_mul])
    refine ⟨s, fun Z f z β hC hA hβ hβ' => ?_⟩
    have hy : f z ∈ W ⟨β, hβ'⟩ := ⟨⟨hC, hA⟩, Set.mem_iInter.2 hβ⟩
    exact (gm_res f z (l₀ ⟨β, hβ'⟩) hy s).symm.trans
      ((congrArg (gm f z (W ⟨β, hβ'⟩)) (hs ⟨β, hβ'⟩)).trans (hu Z f z ⟨β, hβ'⟩ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun i j => unit_ext fun y hy => ?_,
    fun Z f z jC jA β hC hA hβ hβ' => hs jC jA Z f z β hC hA hβ hβ'⟩
  obtain ⟨β, hβ, hβ'⟩ := cover y
  have e₁ := hs i.1 i.2 _ (𝟙 Y) y β hy.1.1 hy.1.2 hβ hβ'
  have e₂ := hs j.1 j.2 _ (𝟙 Y) y β hy.2.1 hy.2.2 hβ hβ'
  have gC := gm_linComb L₁ (fun k => φ k ≫ f₁) ε (𝟙 Y) y i.1 j.1 hy.1.1 hy.2.1
  have gA := gm_linComb L φ ε (𝟙 Y) y i.2 j.2 hy.1.2 hy.2.2
  refine (gm_res (𝟙 Y) y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) ((gm_div (LB.LinComb L φ ε) (LB.LinComb L₁ (fun k => φ k ≫ f₁) ε) (𝟙 Y) y i j hy).trans
    (congrArg₂ (fun a b => a * b⁻¹) gC gA)) ((gm_res (𝟙 Y) y _ hy _).trans e₂)).trans ?_
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Category.id_comp]
  rw [ev_trans hw₀ (φ k) y (i.1 k) (j.1 k) (β k) (β k) (i.2 k) (j.2 k) (Set.mem_iInter.1 hy.1.1 k)
    (Set.mem_iInter.1 hy.2.1 k) (hβ k) (hβ k) (Set.mem_iInter.1 hy.1.2 k) (Set.mem_iInter.1 hy.2.2 k),
    gm_self hL₂ (φ k ≫ f₂) y (hβ k), _root_.mul_one, mul_zpow, mul_zpow, inv_zpow]

end

theorem cancel_two (G : Type) [CommGroup G] (a : ULift.{0} (Finset (Fin 2)) → G)
    (h : ∀ I, a I = a ⟨insert 0 I.down⟩) : ∏ I, a I ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  rw [← Equiv.prod_comp (Equiv.ulift.{0}.symm : Finset (Fin 2) ≃ ULift.{0} (Finset (Fin 2)))]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have e₀ : a ⟨∅⟩ = a ⟨{0}⟩ := h ⟨∅⟩
  have e₁ : a ⟨{1}⟩ = a ⟨{0, 1}⟩ := h ⟨{1}⟩
  show a ⟨∅⟩ ^ (1 : ℤ) * (a ⟨{0}⟩ ^ (-1 : ℤ) * (a ⟨{1}⟩ ^ (-1 : ℤ) * a ⟨{0, 1}⟩ ^ (1 : ℤ))) = 1
  rw [e₀, e₁]
  simp

end GlobalTheory.MumProd.CubeIso

namespace GlobalTheory.MumProd

theorem exists_cubeIso : ∀ (S : Scheme.{0}) (B B₁ B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B₂] [IsCommMonObj B₂] (M : LB B.left) (M₁ : LB B₁.left) (M₂ : LB B₂.left), M.IsLB → M₁.IsLB → M₂.IsLB → ∀ (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (wM : LB.Iso M (extLB M₁ M₂ p₁.left p₂.left)), wM.IsGen → ∀ (x : Fin 2 → (T ⟶ B)) (x₁ : Fin 2 → (T ⟶ B₁)), (∀ I : Finset (Fin 2), psum B x I ≫ p₁ = psum B₁ x₁ I) → (∀ I : Finset (Fin 2), psum B x I ≫ p₂ = psum B x (insert 0 I) ≫ p₂) → ∃ w : LB.Iso (cubeLB B x M) (cubeLB B₁ x₁ M₁), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ T.left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → M₁.ι) (jA : ULift.{0} (Finset (Fin 2)) → M.ι) (β : ULift.{0} (Finset (Fin 2)) → M₂.ι), f z ∈ (cubeLB B₁ x₁ M₁).U jC → f z ∈ (cubeLB B x M).U jA → (∀ I, (f ≫ (psum B x I.down).left ≫ p₂.left) z ∈ M₂.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum B x I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  intro S B B₁ B₂ T _ _ _ _ _ _ M M₁ M₂ hM hM₁ hM₂ p₁ p₂ wM hwM x x₁ h₁ h₂
  obtain ⟨w, hw, H⟩ := CubeIso.exists_linComb hM hM₁ hM₂ wM hwM (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B x I.down).left) (fun I => (psum B₁ x₁ I.down).left) (fun I => (-1) ^ (2 - I.down.card))
    (fun I => ⟨insert 0 I.down⟩) (fun I => by rw [← Over.comp_left, h₁])
    (fun I => by rw [← Over.comp_left, ← Over.comp_left, h₂]) CubeIso.cancel_two
  exact ⟨w, hw, fun Z f z jC jA β hC hA hβ hβ' => H Z f z jC jA β hC hA hβ hβ'⟩

end GlobalTheory.MumProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeBundleIsoExternalTensorFirstFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubeBundle_iso_externalTensor_first_factor : ∀ (S : Scheme.{0}) (B B₁ B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B₂] [IsCommMonObj B₂] (M : LB B.left) (M₁ : LB B₁.left) (M₂ : LB B₂.left), M.IsLB → M₁.IsLB → M₂.IsLB → ∀ (p₁ : B ⟶ B₁) (p₂ : B ⟶ B₂) (wM : LB.Iso M (extLB M₁ M₂ p₁.left p₂.left)), wM.IsGen → ∀ (x : Fin 2 → (T ⟶ B)) (x₁ : Fin 2 → (T ⟶ B₁)), (∀ I : Finset (Fin 2), psum B x I ≫ p₁ = psum B₁ x₁ I) → (∀ I : Finset (Fin 2), psum B x I ≫ p₂ = psum B x (insert 0 I) ≫ p₂) → ∃ w : LB.Iso (cubeLB B x M) (cubeLB B₁ x₁ M₁), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ T.left) (z : Z) (jC : ULift.{0} (Finset (Fin 2)) → M₁.ι) (jA : ULift.{0} (Finset (Fin 2)) → M.ι) (β : ULift.{0} (Finset (Fin 2)) → M₂.ι), f z ∈ (cubeLB B₁ x₁ M₁).U jC → f z ∈ (cubeLB B x M).U jA → (∀ I, (f ≫ (psum B x I.down).left ≫ p₂.left) z ∈ M₂.U (β I)) → (∀ I, β I = β ⟨insert 0 I.down⟩) → gm f z _ (w.s (jC, jA)) = ∏ I, gm (f ≫ (psum B x I.down).left) z _ (wM.s (extIdx (f₁ := p₁.left) (f₂ := p₂.left) (jC I) (β I), jA I)) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  first | exact @GlobalTheory.MumProd.exists_cubeIso | exact GlobalTheory.MumProd.exists_cubeIso | (intros; apply GlobalTheory.MumProd.exists_cubeIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFields
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrecompleteOfPowLe
noncomputable section

open IsLocalRing

namespace GlobalTheory.FiniteCompletionLocalHom

theorem isLocalHom_of_finite {R R₂ V : Type*} [CommRing R] [IsLocalRing R] [CommRing R₂] [IsLocalRing R₂]
    [CommRing V] [IsLocalRing V] (ρ : R →+* R₂) (hρ : ρ.Finite) (ψ : R₂ →+* V)
    (h : IsLocalHom (ψ.comp ρ)) : IsLocalHom ψ := by
  letI := ρ.toAlgebra
  haveI : Module.Finite R R₂ := hρ
  haveI : Algebra.IsIntegral R R₂ := Algebra.IsIntegral.of_finite R R₂

  have hc : (maximalIdeal V).comap (ψ.comp ρ) = maximalIdeal R :=
    ((IsLocalRing.local_hom_tfae (ψ.comp ρ)).out 1 5).mp h
  have hP : ((maximalIdeal V).comap ψ).IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    have hc' : ((maximalIdeal V).comap ψ).comap (algebraMap R R₂) = maximalIdeal R := hc
    change (((maximalIdeal V).comap ψ).comap (algebraMap R R₂)).IsMaximal
    rw [hc']
    infer_instance
  exact ((IsLocalRing.local_hom_tfae ψ).out 1 5).mpr (IsLocalRing.eq_maximalIdeal hP)

theorem exists_extension : ∀ (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), IsLocalHom φ →
    ∀ (ρ : R →+* R₂), RingHom.Finite ρ → ∀ (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω) (m : R₂ →+* Ω),
    Function.Injective m → (∀ r : R, m (ρ r) = j (algebraMap W (FractionRing W) (φ r))) →
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ GlobalTheory.Mum.FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧
      (∀ w : W, j₂ (algebraMap W₂ (FractionRing W₂) (σ w)) = j (algebraMap W (FractionRing W) w)) ∧
      ∀ r : R₂, j₂ (algebraMap W₂ (FractionRing W₂) (φ₂ r)) = m r := by
  intro R R₂ W _ _ _ _ _ _ _ _ _ hW φ hφ ρ hρ Ω _ j m hm hcomp
  obtain ⟨hdvr, hcompl, hchar⟩ := (GlobalTheory.LN.cDvr_iff W).mp hW
  haveI := hdvr
  haveI := hcompl
  haveI := hchar
  letI : Algebra (FractionRing W) Ω := j.toAlgebra
  letI : Algebra W Ω := (j.comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl

  obtain ⟨s₀, hs₀int, hs₀⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ m (fun r => hcomp r)
  have hmint : ∀ r, IsIntegral W (m r) := fun r =>
    hs₀ (integralClosure W Ω) (fun x hx => hs₀int x hx) r

  let F : IntermediateField (FractionRing W) Ω := algebraicClosure (FractionRing W) Ω
  have hmF : ∀ r, m r ∈ F := fun r =>
    ((hmint r).tower_top : IsIntegral (FractionRing W) (m r))
  letI : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W))).toAlgebra
  haveI : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic W F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing W)).mpr inferInstance
  haveI : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).mpr
    ((algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W (FractionRing W)))
  let mF : R₂ →+* F := m.codRestrict F hmF
  obtain ⟨s, hsint, hs⟩ := GlobalTheory.ArcPointDescent.exists_finset ρ hρ φ mF (fun r => Subtype.ext (hcomp r))

  obtain ⟨W', hdvr', hc₁, -, hfin, -, hloc, -, hmem⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra W F s
  haveI := hdvr'
  have hWs : ∀ a, mF a ∈ W' := hs W' fun x hx => hmem x hx (hsint x hx)
  let φ₂ : R₂ →+* W' := mF.codRestrict W' hWs
  let σ : W →+* W' := algebraMap W W'
  have hσinj : Function.Injective σ := fun a b hab =>
    FaithfulSMul.algebraMap_injective W F (congrArg Subtype.val hab)
  let ι : W' →+* Ω := (algebraMap F Ω).comp (algebraMap W' F)
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  let j₂ : FractionRing W' →+* Ω := IsFractionRing.lift hιinj
  have hC : GlobalTheory.LN.CDvr W' :=
    (GlobalTheory.LN.cDvr_iff W').mpr ⟨hdvr', hc₁, charZero_of_injective_algebraMap hσinj⟩
  have hcomm : φ₂.comp ρ = σ.comp φ := RingHom.ext fun r => Subtype.ext (Subtype.ext (hcomp r))
  haveI : IsLocalHom σ := hloc
  have hloc₂ : IsLocalHom (φ₂.comp ρ) := by
    rw [hcomm]
    exact RingHom.isLocalHom_comp σ φ
  refine ⟨W', inferInstance, inferInstance, inferInstance, σ, φ₂, j₂, hC,
    (⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hC, hσinj, RingHom.finite_algebraMap.mpr hfin⟩ : _ ∧ _ ∧ _),
    hloc, fun a b hab => hm (congrArg (fun x : W' => ((x : F) : Ω)) hab),
    isLocalHom_of_finite ρ hρ φ₂ hloc₂, hcomm, fun w => IsFractionRing.lift_algebraMap hιinj (σ w),
    fun r => IsFractionRing.lift_algebraMap hιinj (φ₂ r)⟩

end GlobalTheory.FiniteCompletionLocalHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFields
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FieldTraitExt

theorem exists_normalization (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R)
    (K' : Type) [Field K'] (io : FractionRing R →+* K') (hio : io.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂)
      (e : R₂ →+* K'), FinExt ρ ∧ Function.Injective e ∧ (∀ r, e (ρ r) = io (algebraMap R _ r)) ∧
      ∀ y, i (e y) = algebraMap R₂ _ y := by
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hchar⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hio
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let R₂ := integralClosure R K'
  haveI hfin : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) K' R₂
  haveI : IsLocalRing R₂ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) R₂
  haveI : IsFractionRing R₂ K' := IsIntegralClosure.isFractionRing_of_finite_extension R (FractionRing R) K' R₂
  have hRK : Function.Injective (algebraMap R K') := io.injective.comp (IsFractionRing.injective R _)
  have hinj : Function.Injective (algebraMap R R₂) := fun x y h => hRK (congrArg Subtype.val h)
  haveI : IsNoetherianRing R₂ := IsNoetherianRing.of_finite R R₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, algebraMap R R₂,
    (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).toRingEquiv, algebraMap R₂ K',
    ⟨⟨inferInstance, inferInstance, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, hinj, RingHom.finite_algebraMap.2 hfin⟩,
    Subtype.val_injective, fun r => rfl, fun y => ?_⟩
  exact (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).commutes y

theorem exists_trait (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (φ : R →+* W)
    (hφ : IsLocalHom φ) (ρ : R →+* R₂) (hρ : ρ.Finite) (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω)
    (m : R₂ →+* Ω) (hm : Function.Injective m) (hc : ∀ r, m (ρ r) = j (algebraMap W _ (φ r))) :
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧
      ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = m r := by
  first
  | exact @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | (apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension ..)

end GlobalTheory.FieldTraitExt

namespace GlobalTheory.FieldTraitExt

theorem exists_finite_extension_of_trait : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  intro R W _ _ _ _ _ _ hR hW φ _ hφ K' Ω _ _ io j l hio hc
  obtain ⟨R₂, _, _, _, ρ, i, e, hfe, he, heρ, hie⟩ := exists_normalization R hR K' io hio
  obtain ⟨W₂, _, _, _, σ, φ₂, j₂, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, hj₁, hj₂⟩ :=
    exists_trait R R₂ W hW φ hφ ρ hfe.2.2 Ω j (l.comp e) (l.injective.comp he)
      (fun r => by rw [RingHom.comp_apply, heρ, hc])
  refine ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hfe, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, fun r => ?_, hj₁,
    fun r => ?_⟩
  · rw [← heρ, hie]
  · rw [hj₂, RingHom.comp_apply]
    congr 1
    rw [RingEquiv.eq_symm_apply, hie]

end GlobalTheory.FieldTraitExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFieldsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_extension_dvr_fraction_fields : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  first | exact @GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait | exact GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait | (intros; apply GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecDivNonzeroLocusEq
set_option autoImplicit false

noncomputable section

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

namespace GlobalTheory.Cartier.RatSecDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_mul_unit_iff {x : X} {a u : X.functionField} (hu : UnitAt x u) :
    UnitAt x (a * u) ↔ UnitAt x a := by
  refine ⟨fun h => ?_, fun h => h.mul hu⟩
  have e : a = a * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one]
  rw [e]; exact h.mul hu.inv

theorem local_of {D D' : CartierDiv X} {V : X.Opens} {h : X.functionField}
    (H : ∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V))
    {x : X} {gi rk : X.functionFieldˣ} (hi : D.IsEqn x gi) (hk : D'.IsEqn x rk) :
    RegAt x (h * (gi : X.functionField) / (rk : X.functionField)) ∧
      (UnitAt x (h * (gi : X.functionField) / (rk : X.functionField)) ↔ x ∈ V) := by
  obtain ⟨g, g', hg, hg', hr, hu⟩ := H x
  have u : UnitAt x (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) :=
    (hg.iff_unitAt.1 hi).mul (hk.iff_unitAt.1 hg')
  have e : h * (gi : X.functionField) / (rk : X.functionField) =
      h * (g : X.functionField) / (g' : X.functionField) *
        (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) := by
    have := g.ne_zero; have := g'.ne_zero; have := rk.ne_zero
    field_simp
  rw [e, unitAt_mul_unit_iff u]
  exact ⟨hr.mul u.regAt, hu⟩

end GlobalTheory.Cartier.RatSecDiv


open GlobalTheory.Cartier.RatSecDiv in
theorem GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq :
    ∀ {X : Scheme.{0}} [IsIntegral X] (D D' : CartierDiv X) (L : LB X) (r : L.ι → X.functionFieldˣ),
    Presents D' L r → ∀ (V : X.Opens) (h : X.functionField),
    (∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V)) →
    ∃ θ : (LB.div (toLB D) L).Sec, nonzeroLocus θ = V := by
  intro X _ D D' L r hP V h H
  have key (p : (LB.div (toLB D) L).ι) : ∃ a : Γ(X, (LB.div (toLB D) L).U p), ∀ hp,
      fnOf _ hp a = h * (p.1.1.2 : X.functionField) / (r p.2 : X.functionField) := by
    by_cases hp : genericPoint X ∈ (LB.div (toLB D) L).U p
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hp fun x hx =>
        (local_of H (p.1.2.2 x hx.1) (hP.isEqn p.2 x hx.2)).1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hp h').elim⟩
  choose a ha using key
  refine ⟨⟨a, fun p q => fn_ext fun hpq => ?_⟩, ?_⟩
  · have hp : genericPoint X ∈ (LB.div (toLB D) L).U p := hpq.1
    have hq : genericPoint X ∈ (LB.div (toLB D) L).U q := hpq.2
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg _ (fnOf_resG _ hpq _))).symm)
    rw [ha p hp, ha q hq]
    have eL := hP.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2)
    have e1 : fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val =
        (p.1.1.2 : X.functionField) / (q.1.1.2 : X.functionField) := fnOf_toLB_g _ _ _
    have eg : fnOf _ hpq ((LB.div (toLB D) L).g p q).val =
        fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val *
          (fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val)⁻¹ := by
      change fnOf _ hpq ((res _ ((toLB D).g p.1 q.1) * (res _ (L.g p.2 q.2))⁻¹ : Γ(X, _)ˣ).val) = _
      erw [Units.val_mul, map_mul, map_units_inv]
      exact congrArg₂ (· * ·) (fnOf_resG _ _ _) (congrArg _ (fnOf_resG _ _ _))
    have eL' : fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val =
        (r p.2 : X.functionField) / (r q.2 : X.functionField) :=
      (eq_div_of_mul_eq (r q.2).ne_zero eL.symm)
    rw [eg, e1, eL']
    have := (p.1.1.2).ne_zero; have := (q.1.1.2).ne_zero
    have := (r p.2).ne_zero; have := (r q.2).ne_zero
    field_simp
  · have hmem (p : (LB.div (toLB D) L).ι) (y : X) (hy : y ∈ (LB.div (toLB D) L).U p) :
        y ∈ X.basicOpen (a p) ↔ y ∈ V := by
      rw [← unitAt_fnOf_iff hy (gen_mem hy), ha p (gen_mem hy)]
      exact (local_of H (p.1.2.2 y hy.1) (hP.isEqn p.2 y hy.2)).2
    refine le_antisymm (iSup_le fun p y hy => (hmem p y (X.basicOpen_le _ hy)).1 hy) fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
    obtain ⟨k, hk⟩ := exists_chart hP.isLB y
    exact Opens.mem_iSup.2 ⟨(i, k), (hmem (i, k) y ⟨hi, hk⟩).2 hy⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLine
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
namespace GlobalTheory.LogCanon

theorem exOf_kapBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) :
    (fun ix : Ix Dw => Option.elim ix 0 fun x =>
      (fun τ : E →+* ℂ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) x.1) =
      AllWt.exOf Dw (kapBase Dw) 0 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · by_cases h' : τ (H.rt : E) = H.rt0
    · have hi : (i : ℕ) < Dw.p := by
        have := i.2; simp only [Datum.mult, if_pos h'] at this; exact this
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_pos h', dif_pos h', dif_pos hi, kapBase, sub_zero,
        if_pos hi]
    · have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg h'] at this; exact this
      have hc : conjEmb τ (H.rt : E) = H.rt0 := by
        have := (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H τ).resolve_left h'
        unfold InPsi at this
        rw [ComplexEmbedding.conjugate_coe_eq] at this
        exact this
      have hn : ¬ (Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p) := by omega
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_neg h', dif_neg h', dif_pos hc, dif_pos hi, kapBase,
        if_neg hn, neg_neg, sub_zero]

theorem exists_kap_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  intro E hE hNumber hCM H Dw l Xo c TF Z hpq hF hSmooth K
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  letI : IsIntegral (X₀ TF.Y Z) := hI
  obtain ⟨φ₀, f₀, hgen, hdiv⟩ := GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal E H Dw l Xo c TF Z
  obtain ⟨D, hpull, hD⟩ := hdiv fun τ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [exOf_kapBase Dw] at hpull
    exact hpull
  · obtain ⟨i₀, hi₀⟩ := exists_chart K.isLB (genericPoint (X₀ TF.Y Z))
    have hP := presents_ofLB K.isLB i₀ hi₀
    have hKS := @GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent
      E hE hNumber hCM H Dw l Xo c TF Z hpq hF hI hSmooth K
      (ofLB K.isLB i₀ hi₀) (frameRat K.bundle i₀ hi₀) hP φ₀ f₀ hgen D hD
    obtain ⟨h, hh⟩ := hKS
    exact GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq D _ K.bundle _ hP _ h hh
end GlobalTheory.LogCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLineStatement
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
theorem _root_.GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  first | exact @GlobalTheory.LogCanon.exists_kap_theta | exact GlobalTheory.LogCanon.exists_kap_theta | (intros; apply GlobalTheory.LogCanon.exists_kap_theta <;> assumption)
end
end
