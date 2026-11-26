module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormReciprocityOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightPowEqDegreeLogCardFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightPowEqDegreeLogCardFiniteField
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtVert

theorem isEmpty_cxPts {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k) (σ : k →+* ℂ) (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : κ →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp (y.1.appTop.hom.comp (algebraMap κ Γ(Z, ⊤)))
  have : CharZero κ := f.charZero
  exact not_finite κ

theorem mixArch_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  have h0 : ∀ (L' : HermLB q), L'.archInt M e hr = 0 := by
    intro L'
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    have := h σ
    simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]
  simp [mixArch, FibreProj.pol, h0]

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem finite_Γ {Z : Scheme.{0}} [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] [IsAffine Z]
    (hp : IsProjOver (strHom κ (X := Z))) (φ : Γ(Z, ⊤) →+* Z.residueField (genericPoint Z)) (hφ : Function.Bijective φ) :
    Finite Γ(Z, ⊤) := by
  have : IsProper (strHom κ (X := Z)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have h1 : (strHom κ Z).appTop.hom.FiniteType :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) |>.1 inferInstance
  have h2 : (algebraMap κ Γ(Z, ⊤)).FiniteType := by
    have e : algebraMap κ Γ(Z, ⊤) = (strHom κ Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom :=
      RingHom.ext (algebraMap_eq_strHom κ Z)
    rw [e]
    exact h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have hft : Algebra.FiniteType κ Γ(Z, ⊤) := RingHom.finiteType_algebraMap.1 h2
  letI : Algebra κ (Z.residueField (genericPoint Z)) := (φ.comp (algebraMap κ Γ(Z, ⊤))).toAlgebra
  let ψ : Γ(Z, ⊤) →ₐ[κ] Z.residueField (genericPoint Z) := { φ with commutes' := fun _ => rfl }
  have : Algebra.FiniteType κ (Z.residueField (genericPoint Z)) := Algebra.FiniteType.of_surjective ψ hφ.2
  have : Module.Finite κ (Z.residueField (genericPoint Z)) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Finite (Z.residueField (genericPoint Z)) := Module.finite_of_finite κ
  exact Finite.of_injective φ hφ.1

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem hasDim_iff {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ) :
    HasDim (i (genericPoint Z)) d ↔ topologicalKrullDim Z = d := by
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [HasDim, topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm]

theorem dim_zero {X : Scheme.{0}} {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (h0 : topologicalKrullDim Z = (0 : ℕ))
    (hp : IsProjOver (strHom κ (X := Z))) :
    Real.log (Nat.card (X.residueField (i (genericPoint Z)))) = chi κ (structureModule Z) * Real.log (Nat.card κ) := by
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hZ : ({genericPoint Z} : Set Z) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint Z} : Set Z) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (Z.fromSpecResidueField (genericPoint Z)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (Z.fromSpecResidueField (genericPoint Z))
  have : IsAffine Z := .of_isIso (inv (Z.fromSpecResidueField (genericPoint Z)))
  have : IsIso (Z.fromSpecResidueField (genericPoint Z)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (i.residueFieldMap (genericPoint Z)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := Z.residue_surjective _ a
    obtain ⟨b, rfl⟩ := i.stalkMap_surjective _ a
    exact ⟨X.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((Z.fromSpecResidueField (genericPoint Z)).appTop ≫
      (Scheme.ΓSpecIso (Z.residueField (genericPoint Z))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(Z, ⊤) ≃ X.residueField (i (genericPoint Z)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  have : Finite Γ(Z, ⊤) := finite_Γ κ hp _ b₂
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, Module.natCard_eq_pow_finrank (K := κ)]
  simp

theorem isProjOver_strHom {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hX : IsAmb p) {Z : Scheme.{0}}
    (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)] : IsProjOver (strHom κ (X := Z)) := by
  have := hX.finite
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have hpr' : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  exact (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom κ Z)).2 ⟨hpr', _, hH.pull_of_isClosedImmersion i⟩

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem mixHt_pow_eq_topSelf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  intro k _ X p hA m T hT N d
  induction d with
  | zero =>
    intro _ Z i _ _ κ _ _ _ hd
    rw [hT.zero _ _ ((hasDim_iff i 0).2 hd), dim_zero i κ hd (isProjOver_strHom hA i κ), topSelf_def,
      interNum_of_isEmpty]
  | succ e ih =>
    intro hm Z i _ _ κ _ _ _ hd
    have hZa : IsAmb (i ≫ p) := hA.sub i
    have : IsNoetherian Z := hZa.isNoetherian
    have hp := isProjOver_strHom hA i κ
    have : IsProper (strHom κ (X := Z)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    obtain ⟨r, hr⟩ := exists_isRatSec (N.restr i).isLB
    have hL : (N.B.pull i).IsLB := (N.restr i).isLB
    have hrec := hT.recur Z (i ≫ p) i rfl e hm hd N (fun _ => N) (N.restr i) (fun _ => N.restr i)
      (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr
    have ec : (Fin.cons N (fun _ => N) : Fin (e + 1) → HermLB p) = fun _ => N :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec] at hrec
    rw [hrec, recVal, mixArch_eq_zero (fun σ => isEmpty_cxPts (i ≫ p) σ κ), sub_zero]
    have key := GlobalTheory.ratSec_cycle_formula κ Z hp e hd.le (N.B.pull i) hL (fun _ => N.B.pull i) (fun _ => hL) r hr
    have ec' : (Fin.cons (N.B.pull i) (fun _ => N.B.pull i) : Fin (e + 1) → LB Z) = fun _ => N.B.pull i :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec', ← topSelf_def] at key
    have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hL hr).mult w *
        interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) fun _ : Fin e => N.B.pull i :=
      (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
    rw [key]
    have em := (AddMonoidHom.mulRight (Real.log (Nat.card κ))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
    refine .trans (finsum_congr fun z => ?_) em.symm
    change ((divOfRatSec hL hr).mult z : ℝ) * _ = (((divOfRatSec hL hr).mult z * _ : ℤ) : ℝ) * _
    by_cases hz : (divOfRatSec hL hr).mult z = 0
    · simp [hz]
    rw [Int.cast_mul, mul_assoc]
    refine congrArg _ ?_
    have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Z) hd
      (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
    obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have hrange : Set.range j = closure {j (genericPoint W)} := by
      rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
    letI := algebraΓAlong κ j
    have hW : topologicalKrullDim W = e :=
      (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
    rw [← Scheme.Hom.comp_apply, ih (by omega) W (j ≫ i) κ hW, InterModel.interNumRed_eq_interNumOn _ j _ hrange,
      interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun _ => hL), topSelf_def]
    congr 2
    refine interNum_congr_cls κ _ (fun _ => LB.isLB_pull N.isLB _) (fun _ => LB.isLB_pull hL _) fun _ => ?_
    rw [CechPic.cls_pull hL, CechPic.cls_pull N.isLB, CechPic.cls_pull N.isLB, CechPic.pull_comp]

end GlobalTheory.MixHtVert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightPowEqDegreeLogCardFiniteFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeight_pow_eq_degree_log_card_finiteField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  first | exact @GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf | exact GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf | (intros; apply GlobalTheory.MixHtVert.mixHt_pow_eq_topSelf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtDiag

theorem dim_le_of_isClosedImmersion {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] :
    topologicalKrullDim Z ≤ topologicalKrullDim X := by
  rw [i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact topologicalKrullDim_subspace_le X (Set.range i)

theorem card_residueField_eq {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z)) = Nat.card (Z.residueField z) := by
  refine Nat.card_eq_of_bijective (i.residueFieldMap z) ⟨(i.residueFieldMap z).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Z.residue_surjective z a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
  exact ⟨X.residue _ c, (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i z) c :)⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem mix_pow {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} (hT : IsMix p m T) (e : ℕ) (N : HermLB p)
    (L : Fin e → HermLB p) (x : X) (he : e + 1 ≤ m) (hx : HasDim x (e + 1)) (n : ℕ) :
    T (e + 1) (Fin.cons (N.pow n) L) x = n * T (e + 1) (Fin.cons N L) x := by
  have hiso (A B : HermLB p) (h : A.Isometric B) :
      T (e + 1) (Fin.cons A L) x = T (e + 1) (Fin.cons B L) x :=
    hT.iso (e + 1) _ _ x he hx fun a => Fin.cases h (fun j => HermLB.Isometric.refl (L j)) a
  have h0 : T (e + 1) (Fin.cons (HermLB.triv p) L) x = 0 := by
    have := hT.add e (HermLB.triv p) (HermLB.triv p) L x he hx
    rw [hiso _ _ (HermLB.triv p).isometric_tens_triv] at this
    linarith
  induction n with
  | zero => rw [hiso _ _ N.isometric_pow_zero, h0]; simp
  | succ n ih => rw [hiso _ _ (N.isometric_pow_succ n), hT.add e _ _ L x he hx, ih]; push_cast; ring

theorem exists_isArithHeight : ArchInteg → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ T, IsMix p (D + 1) T → ∀ N : HermLB p, ∃ h : X → ℝ, N.IsArithHeight h ∧ ∀ (x : X) (d : ℕ), HasDim x d → h x = T d (fun _ => N) x := by
  intro HI k _ X p D hX T hT N
  have hA : IsAmb p := isAmb_of_isArithVar hX
  obtain ⟨-, -, -, -, himm, hgen⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hA
  let h : X → ℝ := fun x =>
    T ((topologicalKrullDim (closure ({x} : Set X))).unbotD 0).toNat (fun _ => N) x
  have hh (x : X) (d : ℕ) (hd : HasDim x d) : h x = T d (fun _ => N) x := by
    have hd' : topologicalKrullDim (closure ({x} : Set X)) = d := hd
    show T ((topologicalKrullDim (closure ({x} : Set X))).unbotD 0).toNat (fun _ => N) x = _
    rw [hd']
    rfl
  have hle (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z = d) :
      d ≤ D + 1 := by
    have := dim_le_of_isClosedImmersion i
    rw [hd, hX.dim_eq] at this
    exact_mod_cast this
  have hgi (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ)
      (hd : topologicalKrullDim Z = d) : HasDim (i (genericPoint Z)) d :=
    (himm Z i _ d).2 ((hgen Z d).2 hd)
  refine ⟨h, ⟨fun Z i _ _ κ _ _ _ d hd => ?_, fun Z i _ _ _ hc hd r hr => ?_,
    fun Z i _ _ _ hc e he hd m r hr => ?_⟩, hh⟩
  · rw [hh _ d (hgi Z i d hd)]
    exact GlobalTheory.T.mixedHeight_pow_eq_degree_log_card_finiteField k X p hA (D + 1) T hT N d (hle Z i d hd) Z i κ hd
  · have hd1 : topologicalKrullDim Z = ((0 + 1 : ℕ) : WithBot ℕ∞) := by rw [hd]; rfl
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd1
    have hAZ : IsAmb (i ≫ p) := hA.sub i
    have key : T 1 (fun _ => N) (i (genericPoint Z)) =
        recVal (fun z => T 0 (fun _ => N) (i z)) (fun _ : Fin 0 => N.restr i) (N.restr i) hr := by
      have := hT.recur Z (i ≫ p) i rfl 0 (by omega) hd1 N (fun _ => N) (N.restr i) (fun _ => N.restr i)
        (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr
      refine Eq.trans ?_ this
      congr 1
      funext a
      exact Fin.cases rfl (fun j => j.elim0) a
    rw [hh _ 1 (hgi Z i 1 hd1), key, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal HI k Z (i ≫ p) hAZ (N.restr i) r hr).2 0 hd1 (N.restr i),
      GlobalTheory.ArchDimZero.main k Z (i ≫ p) hZ _ _ r hr, HermLB.curveDeg]
    refine congrArg (· - _) (finsum_congr fun z => ?_)
    by_cases hz : ((N.restr i).div hr).mult z = 0
    · simp [hz]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    have hz0 : HasDim (i z) 0 := (himm Z i z 0).2 (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Z (i ≫ p) hAZ 0 hd1).1 z).1 hz1)
    rw [hT.zero _ _ hz0, card_residueField_eq i z]
  · have hAZ : IsAmb (i ≫ p) := hA.sub i
    refine ⟨GlobalTheory.T.archIntegrable_of_projArithAmbient HI k Z (i ≫ p) hAZ e hd _ _ r hr, ?_⟩
    have hle' := hle Z i (e + 1) hd
    have hx := hgi Z i (e + 1) hd
    have hiso : ((N.pow m).pull i rfl).Isometric ((N.restr i).pow m) :=
      HermLB.icls_eq_iff.1 (by simp only [HermLB.icls_pull, HermLB.icls_pow, map_nsmul])
    have key := hT.recur Z (i ≫ p) i rfl e hle' hd (N.pow m) (fun _ => N) ((N.restr i).pow m)
      (fun _ => N.restr i) hiso (fun _ => HermLB.Isometric.refl _) r hr
    rw [mix_pow hT e N (fun _ => N) _ hle' hx m] at key
    have e1 : (Fin.cons N (fun _ : Fin e => N) : Fin (e + 1) → HermLB p) = fun _ => N :=
      funext fun a => Fin.cases rfl (fun _ => rfl) a
    rw [e1] at key
    rw [hh _ (e + 1) hx, key, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal HI k Z (i ≫ p) hAZ ((N.restr i).pow m) r hr).2 e hd (N.restr i)]
    refine congrArg (· - _) (finsum_congr fun z => ?_)
    by_cases hz : (((N.restr i).pow m).div hr).mult z = 0
    · simp [hz]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    have hze : HasDim (i z) e := (himm Z i z e).2 (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Z (i ≫ p) hAZ e hd).1 z).1 hz1)
    rw [hh _ e hze]

end GlobalTheory.MixHtDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal : ArchInteg → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ T, IsMix p (D + 1) T → ∀ N : HermLB p, ∃ h : X → ℝ, N.IsArithHeight h ∧ ∀ (x : X) (d : ℕ), HasDim x d → h x = T d (fun _ => N) x := by
  first | exact @GlobalTheory.MixHtDiag.exists_isArithHeight | exact GlobalTheory.MixHtDiag.exists_isArithHeight | (intros; apply GlobalTheory.MixHtDiag.exists_isArithHeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditive
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.PolForm

def expv {ι : Type} {n : ℕ} (c : Fin n → ι) : ι →₀ ℕ := ∑ a, Finsupp.single (c a) 1

theorem prod_X_eq {ι : Type} {n : ℕ} (c : Fin n → ι) :
    (∏ a, X (c a) : MvPolynomial ι ℝ) = monomial (expv c) 1 := by
  rw [expv, monomial_sum_one]; rfl

theorem expv_apply {ι : Type} [DecidableEq ι] {n : ℕ} (c : Fin n → ι) (i : ι) :
    expv c i = Fintype.card {a // c a = i} := by
  rw [expv, Finsupp.finsetSum_apply, Fintype.card_subtype]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole]
  simp

theorem weight_expv {ι : Type} {n : ℕ} (c : Fin n → ι) : Finsupp.weight 1 (expv c) = n := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [expv, map_sum, Finsupp.weight_apply, Finsupp.sum_single_index]

theorem exists_perm_of_expv_eq {ι : Type} {n : ℕ} {c c' : Fin n → ι} (h : expv c = expv c') :
    ∃ e : Equiv.Perm (Fin n), ∀ a, c' a = c (e a) := by
  classical
  have hc : ∀ i, Fintype.card {a // c' a = i} = Fintype.card {a // c a = i} := fun i => by
    have := congrArg (fun s => s i) h
    simp only [expv_apply] at this
    convert this.symm
  let E : ∀ i, {a // c' a = i} ≃ {a // c a = i} := fun i => Fintype.equivOfCardEq (hc i)
  refine ⟨(Equiv.sigmaFiberEquiv c').symm.trans ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv c)),
    fun a => ?_⟩
  show c' a = c (E (c' a) ⟨a, rfl⟩).1
  exact (E (c' a) ⟨a, rfl⟩).2.symm

end GlobalTheory.MixHt.PolForm

namespace GlobalTheory.MixHt


open PolForm in
theorem exists_linear_of_multiadditive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (d : ℕ) (F : (Fin (d + 1) → HermLB p) → ℝ), (∀ L M, (∀ a, (L a).Isometric (M a)) → F L = F M) → (∀ L (e : Equiv.Perm (Fin (d + 1))), F (fun a => L (e a)) = F L) → (∀ (A B : HermLB p) (L : Fin d → HermLB p), F (Fin.cons (A.tens B) L) = F (Fin.cons A L) + F (Fin.cons B L)) → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (∀ n : Fin (d + 1) → ι → ℤ, Φ (∏ a, lin fun i => (n a i : ℝ)) = F fun a => comb L (n a)) ∧ ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d + 1 → P.IsHomogeneous e → Φ P = 0 := by
  intro k _ X p d F hiso hsymm hadd ι _ L
  classical
  let rep : HermLB.IsomClass p → HermLB p := fun x => Quotient.out (s := HermLB.isometrySetoid p) x
  have hrepcls : ∀ x, (rep x).icls = x := fun x => Quotient.out_eq (s := HermLB.isometrySetoid p) x
  let G' : (Fin (d + 1) → HermLB.IsomClass p) → ℝ := fun v => F fun a => rep (v a)
  have hG : ∀ M : Fin (d + 1) → HermLB p, G' (fun a => (M a).icls) = F M :=
    fun M => hiso _ _ fun a => HermLB.icls_eq_iff.1 (hrepcls _)
  have hGs : ∀ v (e : Equiv.Perm (Fin (d + 1))), G' (fun a => v (e a)) = G' v :=
    fun v e => hsymm (fun a => rep (v a)) e
  have hG0 : ∀ (x y : HermLB.IsomClass p) (w : Fin d → HermLB.IsomClass p),
      G' (Fin.cons (x + y) w) = G' (Fin.cons x w) + G' (Fin.cons y w) := by
    intro x y w
    have hc : ∀ z, (fun a => rep ((Fin.cons z w : Fin (d + 1) → HermLB.IsomClass p) a)) =
        Fin.cons (rep z) (fun a => rep (w a)) := fun z => by
      funext a; exact Fin.cases rfl (fun _ => rfl) a
    show F (fun a => rep ((Fin.cons (x + y) w : Fin (d + 1) → HermLB.IsomClass p) a)) =
      F (fun a => rep ((Fin.cons x w : Fin (d + 1) → HermLB.IsomClass p) a)) +
        F (fun a => rep ((Fin.cons y w : Fin (d + 1) → HermLB.IsomClass p) a))
    rw [hc, hc, hc, ← hadd]
    refine hiso _ _ fun a => Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero]
      exact HermLB.icls_eq_iff.1 (by rw [HermLB.icls_tens, hrepcls, hrepcls, hrepcls])
    · simp only [Fin.cons_succ]; exact HermLB.Isometric.refl _
  have h0 : ∀ (q : Fin (d + 1) → HermLB.IsomClass p) (x y : HermLB.IsomClass p),
      G' (Function.update q 0 (x + y)) = G' (Function.update q 0 x) + G' (Function.update q 0 y) := by
    intro q x y
    rw [← Fin.cons_self_tail q, Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero]
    exact hG0 x y _
  have hGi : ∀ (m : Fin (d + 1) → HermLB.IsomClass p) (i : Fin (d + 1)) (x y : HermLB.IsomClass p),
      G' (Function.update m i (x + y)) = G' (Function.update m i x) + G' (Function.update m i y) := by
    intro m i x y
    have key : ∀ z, G' (Function.update m i z) = G' (Function.update (m ∘ Equiv.swap 0 i) 0 z) := fun z => by
      rw [← hGs (Function.update m i z) (Equiv.swap 0 i)]
      show G' (Function.update m i z ∘ Equiv.swap 0 i) = _
      rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [key, key, key]
    exact h0 _ x y
  let Mlt : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => HermLB.IsomClass p) ℝ :=
    { toFun := G'
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact hGi m i x y
      map_update_smul' := by
        intro inst m i c x
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun z => G' (Function.update m i z)) (hGi m i)) c x }
  let g : ι → HermLB.IsomClass p := fun i => (L i).icls
  let f : (Fin (d + 1) → ι) → ℝ := fun c => G' fun a => g (c a)
  have hf : ∀ c (e : Equiv.Perm (Fin (d + 1))), f (fun a => c (e a)) = f c := fun c e => hGs (fun a => g (c a)) e
  have hF : ∀ n : Fin (d + 1) → ι → ℤ, F (fun a => comb L (n a)) =
      ∑ c : Fin (d + 1) → ι, (∏ a, (n a (c a) : ℝ)) * f c := by
    intro n
    rw [← hG]
    simp only [icls_comb]
    have e1 := Mlt.map_sum (fun a i => n a i • g i)
    have e2 : ∀ c : Fin (d + 1) → ι, Mlt (fun a => n a (c a) • g (c a)) = (∏ a, (n a (c a) : ℝ)) * f c := by
      intro c
      rw [Mlt.map_smul_univ (fun a => n a (c a)) (fun a => g (c a)), zsmul_eq_mul, Int.cast_prod]
      rfl
    simp only [e2] at e1
    exact e1
  let φ : (ι →₀ ℕ) → ℝ := fun s => if h : ∃ c : Fin (d + 1) → ι, expv c = s then f h.choose else 0
  have hφ : ∀ c, φ (expv c) = f c := by
    intro c
    have h : ∃ c' : Fin (d + 1) → ι, expv c' = expv c := ⟨c, rfl⟩
    simp only [φ, dif_pos h]
    obtain ⟨e, he⟩ := exists_perm_of_expv_eq h.choose_spec
    rw [← hf h.choose e]
    exact congrArg f (funext fun a => (he a).symm)
  let Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ := (basisMonomials ι ℝ).constr ℝ φ
  have hΦ : ∀ s, Φ (monomial s 1) = φ s := by
    intro s
    have := (basisMonomials ι ℝ).constr_basis ℝ φ s
    rwa [coe_basisMonomials] at this
  refine ⟨Φ, fun n => ?_, fun P e he hP => ?_⟩
  · rw [hF]
    simp only [lin]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, prod_X_eq, C_mul', map_smul, hΦ, hφ, smul_eq_mul]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hm : monomial s (AddMonoidAlgebra.coeff P s) = AddMonoidAlgebra.coeff P s • monomial s (1 : ℝ) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, hΦ, smul_eq_mul]
    refine mul_eq_zero_of_right _ (dif_neg ?_)
    rintro ⟨c, rfl⟩
    have := hP (mem_support_iff.1 hs)
    rw [weight_expv] at this
    exact he this.symm

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (d : ℕ) (F : (Fin (d + 1) → HermLB p) → ℝ), (∀ L M, (∀ a, (L a).Isometric (M a)) → F L = F M) → (∀ L (e : Equiv.Perm (Fin (d + 1))), F (fun a => L (e a)) = F L) → (∀ (A B : HermLB p) (L : Fin d → HermLB p), F (Fin.cons (A.tens B) L) = F (Fin.cons A L) + F (Fin.cons B L)) → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (∀ n : Fin (d + 1) → ι → ℤ, Φ (∏ a, lin fun i => (n a i : ℝ)) = F fun a => comb L (n a)) ∧ ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d + 1 → P.IsHomogeneous e → Φ P = 0 := by
  first | exact @GlobalTheory.MixHt.exists_linear_of_multiadditive | exact GlobalTheory.MixHt.exists_linear_of_multiadditive | (intros; apply GlobalTheory.MixHt.exists_linear_of_multiadditive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalytic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatements
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeights
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arFormExists_of_isMix : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q →
    ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  intro hA hT k _ X _ p D hX ι _ L
  obtain ⟨T, hT⟩ := hT k X p (isAmb_of_isArithVar hX) (D + 1)
  have hg : HasDim (genericPoint X) (D + 1) :=
    ((GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p (isAmb_of_isArithVar hX)).2.2.2.2.2 X (D + 1)).2 hX.dim_eq
  obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D (fun M => T (D + 1) M (genericPoint X))
    (fun M N h => hT.iso (D + 1) M N _ le_rfl hg h)
    (fun M e => hT.symm (D + 1) M e _ le_rfl hg)
    (fun A B M => hT.add D A B M _ le_rfl hg) ι L
  refine ⟨Φ, fun n => ?_, hΦ0⟩
  obtain ⟨h, hh, hx⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hA k X p D hX T hT (comb L n)
  refine ⟨h, hh, ?_⟩
  rw [hx _ _ hg, ← Fin.prod_const (D + 1) (lin fun i => (n i : ℝ)), hΦ (fun _ => n)]

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeightsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  first | exact @GlobalTheory.MixHt.arFormExists_of_isMix | exact GlobalTheory.MixHt.arFormExists_of_isMix | (intros; apply GlobalTheory.MixHt.arFormExists_of_isMix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationMixedTermOfPowers
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

theorem addMonoidHom_intCast_mul_real {A : Type} [CommRing A] (θ : A →+ ℝ) (k : ℤ) (z : A) :
    θ ((k : A) * z) = (k : ℝ) * θ z := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem polarisation_mixed_term_of_powers : ∀ (A : Type) [CommRing A] (θ : A →+ ℝ) (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), (∀ n : Option ι → ℤ, Φ (lin (fun o => (n o : ℝ)) ^ (D + 1)) = θ ((∑ o, n o • x o) ^ (D + 1))) → ∀ n : ι → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  intro A _ θ ι _ x D Φ h n
  set Y : MvPolynomial (Option ι) ℝ := MvPolynomial.X none with hY
  set L : MvPolynomial (Option ι) ℝ := rename some (lin fun i => (n i : ℝ)) with hL
  set y : A := ∑ i, n i • x (some i) with hy
  set P : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hP
  set Q : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hQ
  have key : ∀ t : ℤ, P.eval (t : ℝ) = Q.eval (t : ℝ) := by
    intro t
    have ht := h (fun o => Option.elim o t n)
    have hlin : lin (fun o => ((Option.elim o t n : ℤ) : ℝ)) = MvPolynomial.C (t : ℝ) * Y + L := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lin, Fintype.sum_option, Option.elim, hY, hL, map_sum, map_mul, rename_C, rename_X]
    have hsum : (∑ o, (Option.elim o t n) • x o) = (t : A) * x none + y := by
      simp only [Fintype.sum_option, Option.elim, hy, zsmul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hlin, hsum, add_pow, add_pow, map_sum, map_sum] at ht
    simp only [hP, hQ, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    have e1 : ∀ a : ℕ, Φ ((MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ))
        = Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : (MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ)
          = ((t : ℝ) ^ a * ((D + 1).choose a : ℝ)) • (Y ^ a * L ^ (D + 1 - a)) := by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, mul_pow, map_natCast]
        ring
      rw [this, map_smul, smul_eq_mul]
      ring
    have e2 : ∀ a : ℕ, θ (((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A))
        = θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : ((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A)
          = (((t ^ a * ((D + 1).choose a : ℤ)) : ℤ) : A) * (x none ^ a * y ^ (D + 1 - a)) := by
        push_cast
        ring
      rw [this, addMonoidHom_intCast_mul_real]
      push_cast
      ring
    simp only [e1, e2] at ht
    exact ht
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun t : ℤ => (t : ℝ)))
    · rintro _ ⟨t, rfl⟩
      exact key t
    · exact Set.infinite_range_of_injective Int.cast_injective
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 1) hPQ
  simp only [hP, hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  simp only [Finset.sum_ite_eq, Finset.mem_range] at hc
  rw [if_pos (by omega), if_pos (by omega)] at hc
  · simp only [pow_one, Nat.choose_one_right, Nat.add_sub_cancel] at hc
    have hD : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hc hD
    have := mul_right_cancel₀ hD hc
    rw [mul_comm (y ^ D)]
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeights
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem isometric_pull_id {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) :
    (L.pull (𝟙 X) (Category.id_comp p)).Isometric L := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : Points.PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  have hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
    refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
      (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
    · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))
  exact hiso.symm

theorem hasDim_genericPoint {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) : HasDim (genericPoint X) (D + 1) :=
  (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Set.range_id.trans (genericPoint_spec X).def.symm)).trans hX.dim_eq

theorem hasDim_of_coheight_eq_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {z : X} (hz : Order.coheight z = 1) : HasDim z D := by
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  unfold HasDim
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
  exact PrimeDivDim.dim_eq_of_coheight_eq_one k X p D hX Z i hz

theorem lin_intCast {ι : Type} [Fintype ι] (n : ι → ℤ) :
    lin (fun i => (n i : ℝ)) = ∑ i, n i • (MvPolynomial.X i : MvPolynomial ι ℝ) := by
  simp only [lin, zsmul_eq_mul, map_intCast]

theorem arMix_of_mixHt : ArchInteg →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) →
    GlobalTheory.Published.ArMix := by
  intro hAI hEx k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  refine ⟨hAI k X p D hX M (comb L n) r hr, ?_⟩
  obtain ⟨T, hT⟩ := hEx k X p (isAmb_of_isArithVar hX) (D + 1)
  have hgen := hasDim_genericPoint hX
  set F' : Option ι → HermLB p := fun o => o.elim M L with hF'
  let F : (Fin (D + 1) → HermLB p) → ℝ := fun K => T (D + 1) K (genericPoint X)
  obtain ⟨Φ₀, hΦ₀, -⟩ := GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D F (fun K K' hK => hT.iso _ K K' _ le_rfl hgen hK)
    (fun K e => hT.symm _ K e _ le_rfl hgen) (fun A B K => hT.add D A B K _ le_rfl hgen) (Option ι) F'

  have hpow : ∀ m : Option ι → ℤ, Φ (lin (fun o => (m o : ℝ)) ^ (D + 1)) =
      Φ₀.toAddMonoidHom ((∑ o, m o • (MvPolynomial.X o : MvPolynomial (Option ι) ℝ)) ^ (D + 1)) := by
    intro m
    obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT (comb F' m)
    have h₁ : (comb F' m).IsSelfInter (T (D + 1) (fun _ => comb F' m) (genericPoint X)) :=
      ⟨g, hg, hg' _ _ hgen⟩
    have h₂ := hΦ₀ (fun _ => m)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h₂
    rw [HermLB.IsSelfInter.unique hX (hΦ.1 m) h₁, ← lin_intCast]
    exact h₂.symm
  have hpol := GlobalTheory.polarisation_mixed_term_of_powers (MvPolynomial (Option ι) ℝ) Φ₀.toAddMonoidHom ι MvPolynomial.X D Φ hpow n
  rw [hpol]

  let m₀ : Option ι → ℤ := fun o => o.elim 1 0
  let m₁ : Option ι → ℤ := fun o => o.elim 0 n
  have hprod : (∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D * MvPolynomial.X none =
      ∏ a : Fin (D + 1), lin (fun o => ((Fin.cons m₀ (fun _ => m₁) : Fin (D + 1) → Option ι → ℤ) a o : ℝ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, lin_intCast,
      Fintype.sum_option, m₀, m₁, Option.elim, zero_smul, zero_add, one_smul]
    simp only [Pi.zero_apply, Int.cast_zero, Int.cast_one, zsmul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one, one_mul]
    ring
  have hval : Φ₀.toAddMonoidHom ((∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D *
      MvPolynomial.X none) = T (D + 1) (Fin.cons M (fun _ => comb L n)) (genericPoint X) := by
    rw [LinearMap.toAddMonoidHom_coe, hprod, hΦ₀]
    refine hT.iso _ _ _ _ le_rfl hgen fun a => ?_
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [Fin.cons_zero]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₀, F']
    · simp only [Fin.cons_succ]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₁, F']
  rw [hval]

  set N := comb L n
  have hrec := hT.recur X p (𝟙 X) (Category.id_comp p) D le_rfl hX.dim_eq M (fun _ => N) M (fun _ => N)
    (isometric_pull_id M) (fun _ => isometric_pull_id N) r hr
  have e₁ : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X := by simp
  rw [e₁] at hrec
  rw [hrec, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal hAI k X p (isAmb_of_isArithVar hX) M r hr).2 D hX.dim_eq N]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT N
  obtain rfl : h = g := hh.unique hX hg
  have e₂ : (𝟙 X : X ⟶ X) z = z := by simp
  rw [e₂, hg' z D (hasDim_of_coheight_eq_one hX (CartierDiv.coheight_eq_one_of_mult_ne_zero hz))]

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeightsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithMixedInterInductive_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArMix := by
  first | exact @GlobalTheory.MixHt.arMix_of_mixHt | exact GlobalTheory.MixHt.arMix_of_mixHt | (intros; apply GlobalTheory.MixHt.arMix_of_mixHt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatements
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtCalc

theorem arFormExists_arMix_heightProjection (hI : ArchInteg) (hR : ArchRecip) :
    GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  have hE := GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals hI hR
  refine ⟨GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights hI hE, GlobalTheory.T.arithMixedInterInductive_of_mixedHeights hI hE, ?_⟩
  intro k _ X Y _ p q D e hX hY π hπ _ _ L h hh
  obtain ⟨T, hT⟩ := hE k Y q (isAmb_of_isArithVar hY) (e + 1)
  obtain ⟨h', hh', -⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hI k Y q e hY T hT (L.pull π hπ)
  exact ⟨h', hh', GlobalTheory.T.arithHeight_projectionFormula_every_point k X Y p q D e hX hY π hπ L h h' hh hh' (genericPoint Y)⟩

end GlobalTheory.MixHtCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatementsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  first | exact @GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | exact GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | (intros; apply GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalytic
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arCalc_cycleHeights_of_analytic :
    ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := fun hI hR =>
  have h := GlobalTheory.T.arithIntersection_forms_of_archimedean_statements hI hR
  have hC : GlobalTheory.Published.ArCalc := GlobalTheory.Published.arCalc_of_form_mix_projection h.1 h.2.1 h.2.2
  ⟨hC, GlobalTheory.Published.cycleHeights_of_arCalc hC⟩

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalyticStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic : ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := by
  first | exact @GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic | exact GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic | (intros; apply GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormRationalSectionArchIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormRationalSectionArchIntegrable
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

open Set Filter Topology

namespace GlobalTheory.LogNormIntGen

theorem archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, IsArithVar p D → GenSmooth p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ}
      (hr : GlobalTheory.Cartier.IsRatSec N.B r), M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX hs M N r hr σ
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hs σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      LogNormInt.exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.LogNormIntGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormRationalSectionArchIntegrableStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logNorm_rationalSection_archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → GenSmooth p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX hs M N r hr σ
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hs σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      LogNormInt.exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntGenSmooth

open Set

theorem archIntegrable : Published.Principalisation → ∀ (k : Type) [CommRing k] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (M N : HermLB q)
    (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro hP k _ Y _ q e hY M N r hr σ
  obtain ⟨Y', ρ, _, hcov, hgs⟩ := GlobalTheory.GenSmoothCover.exists_isCov_genSmooth hP k Y q e hY
  have hη : ρ (genericPoint Y') ⤳ genericPoint Y := hcov.2.1 ▸ specializes_rfl
  have hr' := MultPull.isRatSec_pull_map ρ hη hr
  have hup := GlobalTheory.T.logNorm_rationalSection_archIntegrable hcov.1 hgs (N.restr ρ) (M.restr ρ) hr' σ
  have hsub : ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl) ⊆
      offSupp (ρ ≫ q) σ ((M.restr ρ).div hr') := fun y hy =>
    GlobalTheory.ArchIntAlter.mem_offSupp_pull M ρ hη hr hy
  have hm : MeasurableSet (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :=
    (isOpen_ptsIn _).measurableSet
  have heq : EqOn (logNorm ((M.restr ρ).φ σ) fun c => Units.map
      (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom (r (c PUnit.unit)))
      (fun y => logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) := fun y hy =>
    GlobalTheory.ArchIntAlter.logNorm_pull M ρ hη hr hy
  exact GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite k Y q e hY Y' ρ hcov.1 hcov.2.1 hcov.2.2 N σ _ _
    (GlobalTheory.ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ))
    ⟨(hup.1.mono_set hsub).congr_fun heq hm, (hup.2.mono_set hsub).congr_fun heq hm⟩

end GlobalTheory.ArchIntGenSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisation
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ArchIntegClosing

theorem archInteg : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg :=
  fun hP k _ Y _ q e hY M N r hr => GlobalTheory.ArchIntGenSmooth.archIntegrable hP k Y q e hY M N r hr

end GlobalTheory.ArchIntegClosing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archLogNormChernIntegrable_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg := by
  first | exact @GlobalTheory.ArchIntegClosing.archInteg | exact GlobalTheory.ArchIntegClosing.archInteg | (intros; apply GlobalTheory.ArchIntegClosing.archInteg <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem GlobalTheory.MixHt.arCalc_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArCalc := fun h =>
  (GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic (GlobalTheory.T.archLogNormChernIntegrable_of_principalisation h) (GlobalTheory.T.archLogNormReciprocity_of_principalisation h)).1
