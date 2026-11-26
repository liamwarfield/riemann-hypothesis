module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairs
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Cartier GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NadelApp

theorem isIso_idealModuleι_of_forall_notMem {X : Scheme.{0}} (I : X.IdealSheafData)
    (h : ∀ x, x ∉ I.support) : IsIso (idealModuleι I) := by
  have h0 : toSubscheme I = 0 := by
    haveI : IsEmpty I.subscheme := ⟨fun z => h _ (I.range_subschemeι.le ⟨z, rfl⟩)⟩
    ext V t
    have e : I.subschemeι ⁻¹ᵁ V = ⊥ := eq_bot_iff.2 fun z _ => isEmptyElim z
    have : Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) := by
      rw [e]
      infer_instance
    exact this.elim _ _
  exact kernel.ι_of_zero h0

theorem qWeil_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem kawamataViehweg_complex : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → IsIntegral X → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef ℂ N) → (letI := algebraΓOfHom p; IsBig ℂ N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hN X p D _ hproj _ K N hnef hbig q hq
  letI := algebraΓOfHom p
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  obtain ⟨J, hJ, hv⟩ := nadel_canonical_add hN X p D hproj K N N hnef.isLB 0 1 1 one_pos one_pos
    CartierDiv.eff_zero hnef hbig (fun C _ => by
      rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
      simp)
  haveI := isIso_idealModuleι_of_forall_notMem J fun x hx => (hJ x).1 hx (by
    rw [qWeil_zero]
    exact kltAt_zero_of_smooth (topologicalKrullDim_eq_of_smooth X p D) x)
  exact @Function.Injective.subsingleton _ _ _ (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((twistFunctor (tens K.bundle N)).mapIso (asIso (idealModuleι J)))).symm.injective (hv q hq)

end GlobalTheory.NadelApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_of_nadel_pairs : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → IsIntegral X → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef ℂ N) → (letI := algebraΓOfHom p; IsBig ℂ N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  first | exact @GlobalTheory.NadelApp.kawamataViehweg_complex | exact GlobalTheory.NadelApp.kawamataViehweg_complex | (intros; apply GlobalTheory.NadelApp.kawamataViehweg_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VanishEmbedded

open GlobalTheory.HSCore.VanishNumberField

theorem subsingleton_coh_canon_tens : GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → ∀ (F : Type) [Field F], Nonempty (F →+* ℂ) → ∀ (X : Scheme.{0}) (p : X ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef F N) → (letI := algebraΓOfHom p; IsBig F N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hNum hNad F _ ⟨σ⟩ X p D hsm hp hgc K N hnef hbig q hq
  letI := σ.toAlgebra
  let X' := pullback p (spMap (algebraMap F ℂ))
  let π : X' ⟶ X := pullback.fst _ _
  let p' : X' ⟶ Sp ℂ := pullback.snd _ _
  have H : IsPullback π p' p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hI, -, hsm', hp', -⟩ := GlobalTheory.BaseChangeVariety.baseChange_props F ℂ X X' p p' π D H hp hgc
  haveI : Nonempty X := ⟨π (Classical.arbitrary X')⟩
  letI := algebraΓOfHom p
  letI := algebraΓOfHom p'
  obtain ⟨hprop, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hL := LB.isLB_pull hnef.isLB π
  have hnef' : IsNef ℂ (N.pull π) := GlobalTheory.NefFieldExt.isNef_baseChange hNum F ℂ X X' p p' π H hp N hnef
  have hbig' : IsBig ℂ (N.pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hbig.3
    have hD : topologicalKrullDim X = D := topologicalKrullDim_eq_of_smooth p D hsm
    obtain rfl : D₀ = D := by exact_mod_cast hD₀.symm.trans hD
    refine (isBig_iff (f := p') (fun _ => rfl) hp'
      (topologicalKrullDim_eq_of_smooth _ D₀ hsm')).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hbig.1, cls_pull (isLB_lbPow hbig.1 m), cls_lbPow hbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull H (isLB_lbPow hbig.1 m) 0).symm
  have hKV := GlobalTheory.T.kawamataViehweg_vanishing_of_nadel_pairs hNad X' p' D hp' hI (K.baseChange H) (N.pull π) hnef' hbig' q hq
  have hM : (tens K.bundle N).IsLB := isLB_tens K.isLB hnef.isLB
  have hK' := LB.isLB_pull K.isLB π
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X') (LB.isLB_pull hM π) (isLB_tens hK' hL)
    (by rw [cls_pull hM π, cls_tens K.isLB hnef.isLB, cls_tens hK' hL, cls_pull K.isLB π, cls_pull hnef.isLB π, map_add (f := _)])
  exact subsingleton_coh_of_pull (f := p) (f' := p') H hM q
    ((cohOn.mapIso Γ(X', ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 hKV)

end GlobalTheory.VanishEmbedded
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField : GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → ∀ (F : Type) [Field F], Nonempty (F →+* ℂ) → ∀ (X : Scheme.{0}) (p : X ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef F N) → (letI := algebraΓOfHom p; IsBig F N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  first | exact @GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens | exact GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens | (intros; apply GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldDescent

theorem interNum_one_nonneg_of_isNef {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k (X := V))) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : IsNef k N) :
    0 ≤ interNum k (GlobalTheory.structureModule V) ![N] := by
  refine CurveDevissage.interNum_one_nonneg hp hd hN.isLB (fun Z i hi hZ _ ha hdZ => ?_) _ inferInstance
  have hpr : IsProper (strHom k (X := V)) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  have h := (isNef_iff_isClosedImmersion.1 hN).2 Z i hi hZ hdZ inferInstance
  rw [interNumOn, interNum_pushforward_of_isClosedImmersion ha _ (isLB_vecOne hN.isLB)] at h
  rw [topSelf_def]
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j; rfl

theorem isNef_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ L : LB Y, L.IsLB → (letI := algebraΓOfHom q; IsNef E (L.pull π)) → (letI := algebraΓOfHom p; IsNef k L) := by
  intro k E _ _ _ Y X p q π H hp L hL hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  refine ⟨hL, fun C hC => ?_⟩
  have H₁ : IsPullback (pullback.fst (redι C) π) (pullback.snd (redι C) π ≫ q) (redι C ≫ p)
      (spMap (algebraMap k E)) := (IsPullback.of_hasPullback (redι C) π).paste_vert H
  have hpC : IsProjOver (redι C ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hpr : IsProper (redι C ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpC).1
  have hp' := ProjSpace.isProjOver_of_isPullback_spMap _ H₁ hpC
  have hd : topologicalKrullDim (pullback (redι C) π : Scheme.{0}) ≤ 1 :=
    (FieldExtDim.topologicalKrullDim_baseChange_le k E _ _ _ _ _ H₁).trans
      ((topologicalKrullDim_red C).trans hC.2).le
  have hLC := LB.isLB_pull hL (redι C)
  have key := FieldChangeInter.interNum_pull H₁ (isLB_vecOne hLC)
  letI := algebraΓOfHom (pullback.snd (redι C) π ≫ q)
  have hN' : IsNef E ((L.pull π).pull (pullback.snd (redι C) π)) :=
    hN.pull_of_isClosedImmersion _ fun _ => rfl
  have h0 := interNum_one_nonneg_of_isNef (k := E)
    (by rw [strHom_eq (f := pullback.snd (redι C) π ≫ q) fun _ => rfl]; exact hp') hd hN'
  rw [interNumRed_one_eq hL]
  refine (h0.trans_eq ?_).trans_eq key
  refine interNum_congr_cls E _ (isLB_vecOne hN'.isLB)
    (fun i => LB.isLB_pull (isLB_vecOne hLC i) _) fun i => ?_
  fin_cases i
  change pull _ (pull π (cls L hL)) = pull _ (pull (redι C) (cls L hL))
  simp only [← pull_comp, pullback.condition]

end GlobalTheory.NefFieldDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNefLineBundle_of_baseChange_field : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ L : LB Y, L.IsLB → (letI := algebraΓOfHom q; IsNef E (L.pull π)) → (letI := algebraΓOfHom p; IsNef k L) := by
  first | exact @GlobalTheory.NefFieldDescent.isNef_of_baseChange | exact GlobalTheory.NefFieldDescent.isNef_of_baseChange | (intros; apply GlobalTheory.NefFieldDescent.isNef_of_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonLineBundleCohomologyProjBaseChangeIf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonLineBundleCohomologyProjBaseChangeIf
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.FieldChangeInter

namespace GlobalTheory.CohFieldChange

theorem subsingleton_coh_pull_iff {X X' : Scheme.{0}} {k E : Type} [Field k] [Field E] [Algebra k E]
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}
    [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X') (M.pull π)) n) ↔
      Subsingleton (coh (twist (GlobalTheory.structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  refine e₂.toEquiv.subsingleton_congr.symm.trans (Iff.trans ?_ e₁.toEquiv.subsingleton_congr)
  refine e₄.toEquiv.subsingleton_congr.symm.trans (e₃.toEquiv.subsingleton_congr.trans ?_)
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k E

theorem subsingleton_coh_pull_iff_of_isProjOver : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → ∀ M : LB Y, M.IsLB → ∀ n : ℕ, (Subsingleton (coh (twist (GlobalTheory.structureModule X) (M.pull π)) n) ↔ Subsingleton (coh (twist (GlobalTheory.structureModule Y) M) n)) := by
  intro k E _ _ _ Y X p q π H h _ M hM n
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact subsingleton_coh_pull_iff (f := p) (f' := q) H hM n

end GlobalTheory.CohFieldChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonLineBundleCohomologyProjBaseChangeIfStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_lineBundleCohomology_projBaseChange_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → ∀ M : LB Y, M.IsLB → ∀ n : ℕ, (Subsingleton (coh (twist (GlobalTheory.structureModule X) (M.pull π)) n) ↔ Subsingleton (coh (twist (GlobalTheory.structureModule Y) M) n)) := by
  first | exact @GlobalTheory.CohFieldChange.subsingleton_coh_pull_iff_of_isProjOver | exact GlobalTheory.CohFieldChange.subsingleton_coh_pull_iff_of_isProjOver | (intros; apply GlobalTheory.CohFieldChange.subsingleton_coh_pull_iff_of_isProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfield
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ProjCountableDescent


open GlobalTheory.PolCountableDescent in
theorem projLB_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  intro K _ X p hp L hL
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ X p hp
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ X p₀ p φ L hL sq
  let s : Finset K := s₀ ∪ s₂
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  have sq₁ : IsPullback (pullback.fst p₀ inc) (pullback.snd p₀ inc) p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : X ⟶ pullback p₀ inc := sq₁.lift φ (p ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ pullback.fst p₀ inc = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd p₀ inc = p ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨L₁, hL₁, hI⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) _ _ _ ψ
    sq₁ hψ₁ hψ₂
  refine ⟨K₁, _, pullback.snd p₀ inc, ψ, L₁, countable_closure s,
    ProjSpace.isProjOver_pullback_snd _ hp₀, ?_, hL₁, hI⟩
  refine IsPullback.of_right (t := sq₁) ?_ hψ₂
  have e : spMap (algebraMap K₁ K) ≫ inc = spMap K₀.subtype := spMap_subtype_comp h
  rw [hψ₁, e]
  exact sq

end GlobalTheory.ProjCountableDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveLineBundle_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  first | exact @GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield | exact GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield | (intros; apply GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIff
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.BigFieldChange

theorem isBig_pull_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k)
    (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q →
    topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB →
    ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  intro k E _ _ _ Y X p q π H hp hq hd L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hL' := LB.isLB_pull hL π
  have e : ∀ m : ℕ, lbH0 E (lbPow (L.pull π) m) = lbH0 k (lbPow L m) := fun m => by
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL m) π)
      (by rw [cls_lbPow hL', cls_pull hL, cls_pull (isLB_lbPow hL m), cls_lbPow hL, map_nsmul])]
    exact FieldChangeInter.hdim_pull H (isLB_lbPow hL m) 0
  constructor
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL, fun m => finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_lbPow hL m),
      D, hd.symm.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m))⟩
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL', fun m => finite_coh_zero_twist_of_isProjOver (f := q) (fun _ => rfl) hq (isLB_lbPow hL' m),
      D, hd.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m).symm)⟩

end GlobalTheory.BigFieldChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIffStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB → ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  first | exact @GlobalTheory.BigFieldChange.isBig_pull_iff | exact GlobalTheory.BigFieldChange.isBig_pull_iff | (intros; apply GlobalTheory.BigFieldChange.isBig_pull_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtension
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.FieldDescentSm

theorem smoothOfRelativeDimension_and_geometricallyConnected_descend : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  intro k E _ _ _ Y X p q π H D hX hD hq
  have hf := GlobalTheory.FieldDescentAb.fpqc_spMap (algebraMap k E)
  have hsq : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hsm : Smooth p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hf hsq
  have hp : GeometricallyConnected p :=
    GlobalTheory.FieldDescentAb.geometricallyConnected_of_isPullback (algebraMap k E) H
  refine ⟨?_, hp⟩
  have hc : ConnectedSpace Y :=
    hp.geometrically_connectedSpace (𝟙 _) (𝟙 Y) p (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨x⟩ := hX
  obtain ⟨D', hD'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected p (π x)
  have h' : SmoothOfRelativeDimension D' q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D').of_isPullback H hD'
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique q hD h' x]
  exact hD'

end GlobalTheory.FieldDescentSm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtensionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  first | exact @GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | exact GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | (intros; apply GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend <;> assumption)
end
end

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.KVFromPair

theorem subsingleton_coh_twist (hN : GlobalTheory.Published.NefNumerics) (hV : GlobalTheory.Published.NadelVanishingPair)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ) [hs : SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (K : CanonLB p D) (N : LB X) (h₁ : letI := algebraΓOfHom p; IsNef k N)
    (h₂ : letI := algebraΓOfHom p; IsBig k N) (q : ℕ) (hq : 0 < q) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  have hNl : N.IsLB := by
    letI := algebraΓOfHom p
    exact h₁.isLB
  obtain ⟨K₁, X₁, p₁, ψ, L₁, hc, hp₁, H, hL₁, e⟩ := GlobalTheory.T.projectiveLineBundle_descends_to_countable_subfield k X p hp N hNl
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hg : GeometricallyConnected p := GlobalTheory.geometricallyConnected_of_isAlgClosed p
  obtain ⟨hs₁, hg₁⟩ := GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension K₁ k X₁ X p₁ p ψ H D inferInstance hs hg
  have hne : Nonempty X₁ := ⟨ψ (Classical.arbitrary X)⟩
  have hP := LB.isLB_pull hL₁ ψ
  have ec : cls N hNl = cls (L₁.pull ψ) hP := (cls_eq_iff _ _).2 e
  have n₁ := GlobalTheory.T.isNefLineBundle_of_baseChange_field K₁ k X₁ X p₁ p ψ H hp₁ L₁ hL₁ (by
    letI := algebraΓOfHom p
    exact h₁.of_cls_eq hP ec.symm)
  have b₁ := (GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff K₁ k X₁ X p₁ p ψ H hp₁ hp
    ((GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p D hs).trans
      (GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p₁ D hs₁).symm) L₁ hL₁).1 (by
    letI := algebraΓOfHom p
    exact h₂.of_cls_eq hP ec.symm)
  let C : CanonLB p₁ D := CanonLB.all p₁ D
  have v₁ := GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField hN hV K₁ (GlobalTheory.KeyHouse.nonempty_ringHom_complex K₁) X₁ p₁ D hp₁ hg₁
    C L₁ n₁ b₁ q hq
  have hT := isLB_tens C.isLB hL₁
  have v := (GlobalTheory.T.subsingleton_lineBundleCohomology_projBaseChange_iff K₁ k X₁ X p₁ p ψ H hp₁ hp _ hT q).2 v₁
  have eK : cls K.bundle K.isLB = cls (C.bundle.pull ψ) (LB.isLB_pull C.isLB ψ) := by
    obtain ⟨w, hw, -⟩ := canonLB_baseChange K₁ k _ X₁ X p₁ p ψ D H C K
    exact (cls_eq_iff _ _).2 ⟨w, hw⟩
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (GlobalTheory.structureModule X) (isLB_tens K.isLB hNl)
    (LB.isLB_pull hT ψ) (by
      rw [cls_tens K.isLB hNl, cls_pull hT, cls_tens C.isLB hL₁, map_add (f := _), eK, ec,
        cls_pull C.isLB, cls_pull hL₁])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q i).toEquiv.subsingleton_congr.2 v

theorem kawamataViehweg_of_nadelVanishingPair :
    GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.KawamataViehweg := by
  intro hN hV k _ _ _ X a _ D hs hp K N h₁ h₂ q hq
  have ha : a = algebraΓOfHom (strHom k X) := Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)
  have v := subsingleton_coh_twist hN hV k X (strHom k X) D hp K N (ha ▸ h₁) (ha ▸ h₂) q hq
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q (Twist.unitTwistIso _)).toEquiv.subsingleton_congr.1 v

end GlobalTheory.KVFromPair
