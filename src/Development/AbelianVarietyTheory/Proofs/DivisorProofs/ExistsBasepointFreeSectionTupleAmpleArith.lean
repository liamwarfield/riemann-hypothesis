module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTermsTorusTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowSectionNonvanishingOnClosedStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVertical
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem dim_le_zero_of_fib_of_subset_affine : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  intro k _ X p h ℓ U C hℓ hU hC hCc hfib hCU
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  set Y := GlobalTheory.MixHt.clo η
  set i := GlobalTheory.MixHt.cloι η
  have hgen : i (genericPoint Y) = η := GlobalTheory.MixHt.cloι_genericPoint η
  have hrange : i '' Set.univ = C := by
    rw [← (genericPoint_spec Y).def, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton, hgen, hη.def]
  have htop : i ⁻¹ᵁ U = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hCU (hrange ▸ Set.mem_image_of_mem i (Set.mem_univ y))
  have hV : IsAffineOpen (⊤ : Y.Opens) := htop ▸ hU.preimage i
  have hA := h.sub i
  have := hA.finite
  have : IsProper (i ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hA.isProjOver
    have := isProper_str k N
    exact hj ▸ inferInstance

  have hφ := isIntegral_appTop_of_universallyClosed (i ≫ p)
  let A := Γ(Sp k, ⊤)
  let R := Γ(Y, ⊤)
  let e : A ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hAint : Algebra.IsIntegral ℤ A :=
    Algebra.IsIntegral.of_surjective e.symm.toRingHom.toIntAlgHom e.symm.surjective
  letI : Algebra A R := (i ≫ p).appTop.hom.toAlgebra
  have hRA : Algebra.IsIntegral A R := ⟨hφ⟩
  have hRint : Algebra.IsIntegral ℤ R := Algebra.IsIntegral.trans A

  have hchar : ((ℓ : ℕ) : R) = 0 := by
    have hcX : CharP (X.residueField η) ℓ := ringChar.eq_iff.mp (hfib hη.mem)
    have h1 : ((ℓ : ℕ) : X.residueField (i (genericPoint Y))) = 0 := by
      rw [hgen]; exact CharP.cast_eq_zero _ ℓ
    have h2 : ((ℓ : ℕ) : Y.residueField (genericPoint Y)) = 0 := by
      have := congrArg (i.residueFieldMap (genericPoint Y)).hom h1
      simpa using this
    have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
        (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
      (RingHom.injective (Y.residue (genericPoint Y)).hom).comp
        (germ_injective_of_isIntegral Y (U := ⊤) (genericPoint Y) trivial)
    apply hinj
    simpa using h2

  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP R ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 hchar
  letI : Algebra (ZMod ℓ) R := ZMod.algebra R ℓ
  have : Algebra.IsIntegral (ZMod ℓ) R := Algebra.IsIntegral.tower_top ℤ
  have hR : IsField R := isField_of_isIntegral_of_isField' (Field.toIsField (ZMod ℓ))

  have hdimY : topologicalKrullDim ((⊤ : Y.Opens) : Set Y) = 0 := by
    rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding hV.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R)).trans (ringKrullDim_eq_zero_of_isField hR)
  rw [← hrange, GlobalTheory.MixHt.DimBasic.dim_image i.isClosedEmbedding.isEmbedding]
  rw [TopologicalSpace.Opens.coe_top] at hdimY
  exact hdimY.le

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_le_zero_fibre_affineOpen : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  first | exact @GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | exact GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine | (intros; apply GlobalTheory.MixHt.dim_le_zero_of_fib_of_subset_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleZeroSetSectionClosedIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleZeroSetSectionClosedIrreducible
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KrullZero

theorem coheight_le_one {Y : Scheme.{0}} [IsLocallyNoetherian Y] {N : LB Y} (hN : N.IsLB) (t : N.Sec) (w : Y)
    (hw : w ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t)
    (hgen : ∀ y : Y, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) : Order.coheight w ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_chart hN w
  obtain ⟨V, hV, hwV, hle⟩ := exists_isAffineOpen_mem_and_subset hk
  have hle' : V ≤ N.U k := hle
  set g : Γ(Y, V) := Y.presheaf.map (homOfLE hle').op (t.f k) with hg
  have hbo : Y.basicOpen g = V ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    rw [hg, Scheme.basicOpen_res, ← GlobalTheory.nonzeroLocus_inf_chart, inf_comm _ (N.U k), ← inf_assoc,
      inf_eq_left.2 hle']
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(Y, V), hV.fromSpec P = w := by
    have : w ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hwV
    exact this
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hmemb : ∀ Q : PrimeSpectrum Γ(Y, V), g ∈ Q.asIdeal ↔ hV.fromSpec Q ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    intro Q
    have h1 : Q ∈ PrimeSpectrum.basicOpen g ↔ hV.fromSpec Q ∈ Y.basicOpen g := by
      rw [← hV.fromSpec_preimage_basicOpen]; rfl
    have h2 : hV.fromSpec Q ∈ V := by
      have := Set.mem_range_self (f := hV.fromSpec) Q
      rwa [hV.range_fromSpec] at this
    rw [hbo] at h1
    constructor
    · intro hgQ hQ
      exact (PrimeSpectrum.mem_basicOpen _ _).1 (h1.2 ⟨h2, hQ⟩) hgQ
    · intro hQ
      by_contra hgQ
      exact hQ (h1.1 ((PrimeSpectrum.mem_basicOpen _ _).2 hgQ)).2
  have hgP : g ∈ P.asIdeal := (hmemb P).2 (hP ▸ hw)
  have hmin : P.asIdeal ∈ (Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hgP⟩, fun Q hQ hQP => ?_⟩
    have hgQ : g ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.2
    by_contra hne
    let Q' : PrimeSpectrum Γ(Y, V) := ⟨Q, hQ.1⟩
    have hsp : Q' ⤳ P := (PrimeSpectrum.le_iff_specializes Q' P).1 hQP
    have hsp' : hV.fromSpec Q' ⤳ w := hP ▸ hsp.map hV.fromSpec.continuous
    have hneq : hV.fromSpec Q' ≠ w := by
      rw [← hP]
      intro h
      have := hV.fromSpec.isOpenEmbedding.injective h
      exact hne (by rw [← this])
    have hlt : w < hV.fromSpec Q' := lt_of_le_not_ge (show w ≤ hV.fromSpec Q' from hsp') fun h => hneq (hsp'.antisymm h).eq
    exact (hmemb Q').1 hgQ (hgen _ hlt)
  have hh : P.asIdeal.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  let x : Spec Γ(Y, V) := P
  have eS := (asIso (hV.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(Y, V) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight w := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight, hP]
  have : ((Order.coheight w : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [← hPh]; exact_mod_cast hh
  exact_mod_cast this

end GlobalTheory.KrullZero

namespace GlobalTheory.KrullZero


open GlobalTheory.MixHt in
theorem exists_irreducible_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : LB X) (s : M.Sec) (C : Set X), M.IsLB → IsIrreducible C → IsClosed C →
    (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X)).Nonempty → ¬ C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) →
    ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) ∧
      topologicalKrullDim C ≤ topologicalKrullDim C' + 1 := by
  intro k _ X _ p D hX M s C hM hC hCc hmeet hnot
  set Z := ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s with hZ
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  haveI : IsNoetherian X := hamb.isNoetherian
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  have hηC : closure ({η} : Set X) = C := hη
  let i := cloι η
  have hambY : IsAmb (i ≫ p) := hamb.sub i
  haveI : IsNoetherian (clo η) := hambY.isNoetherian
  have hgi : i (genericPoint (clo η)) = η := cloι_genericPoint η
  have hWm : ∀ y : clo η, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) ↔ i y ∈ Z := fun y => by
    rw [GlobalTheory.nonzeroLocus_secPull]; rfl
  have basic := hasDim_basic k X p hamb
  have basicY := hasDim_basic k (clo η) (i ≫ p) hambY
  obtain ⟨m, hm⟩ := basicY.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo η))
  have hdY : topologicalKrullDim (clo η) = d := (basicY.2.2.2.2.2 (clo η) d).1 hd
  have hdC : topologicalKrullDim C = d := by
    have h := (basic.2.2.2.2.1 (clo η) i (genericPoint (clo η)) d).2 hd
    rw [hgi] at h
    rw [← hηC]; exact h

  have hrange : C ⊆ Set.range i := by
    rw [← hηC]
    refine closure_minimal ?_ i.isClosedEmbedding.isClosed_range
    rintro _ rfl
    exact ⟨_, hgi⟩

  obtain ⟨x, hxC, hxZ⟩ := Set.not_subset.1 hnot
  obtain ⟨y₀, rfl⟩ := hrange hxC
  have hηZ : η ∈ Z := by
    obtain ⟨x', hx'C, hx'Z⟩ := hmeet
    rw [← hηC] at hx'C
    exact (specializes_iff_mem_closure.2 hx'C).mem_open Z.isOpen hx'Z

  obtain ⟨w, hw, hwmin⟩ := (InvImage.wf (Order.coheight : clo η → ℕ∞) wellFounded_lt).has_min
    {y | y ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i)} ⟨y₀, fun h => hxZ ((hWm y₀).1 h)⟩
  obtain ⟨e, -, he⟩ := hm w
  have hce : Order.coheight w + (e : ℕ∞) = d := GlobalTheory.DimCoheight.coheight_add_eq k (clo η) (i ≫ p) hambY d hdY w e he
  have hfin : Order.coheight w < ⊤ := by
    refine lt_of_le_of_lt (le_self_add) (hce ▸ ENat.natCast_lt_top d)
  have hgen : ∀ y : clo η, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) := by
    intro y hlt
    by_contra hy
    exact hwmin y hy (Order.coheight_strictAnti hlt ((Order.coheight_anti hlt.le).trans_lt hfin))
  have h1 : Order.coheight w ≤ 1 := coheight_le_one (LB.isLB_pull hM i) (GlobalTheory.secPull s i) w hw hgen
  have h0 : Order.coheight w ≠ 0 := by
    intro h0
    have hmax : IsMax w := Order.coheight_eq_zero.1 h0
    have hsp : genericPoint (clo η) ⤳ w := genericPoint_specializes w
    have hle : genericPoint (clo η) ≤ w := hmax (show w ≤ genericPoint (clo η) from hsp)
    have heq : w = genericPoint (clo η) := (hsp.antisymm hle).eq.symm
    have hgW := (hWm (genericPoint (clo η))).2 (by rw [hgi]; exact hηZ)
    rw [← heq] at hgW
    exact hw hgW
  have hc1 : Order.coheight w = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  rw [hc1] at hce
  have hde : d = e + 1 := by
    have : ((e + 1 : ℕ) : ℕ∞) = d := by push_cast; rw [← hce, add_comm]
    exact_mod_cast this.symm
  refine ⟨closure {i w}, isIrreducible_singleton.closure, isClosed_closure, ?_, ?_⟩
  · refine closure_minimal ?_ (hCc.sdiff Z.isOpen)
    rintro _ rfl
    refine ⟨?_, fun h => hw ((hWm w).2 h)⟩
    have hs := (genericPoint_specializes w).map i.continuous
    rw [hgi] at hs
    rw [← hηC]
    exact specializes_iff_mem_closure.1 hs
  · have hC' : topologicalKrullDim (closure ({i w} : Set X)) = e := (basic.2.2.2.2.1 (clo η) i w e).2 he
    rw [hdC, hC', hde]
    push_cast
    exact le_rfl

end GlobalTheory.KrullZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleZeroSetSectionClosedIrreducibleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_zeroSet_section_closedIrreducible : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : LB X) (s : M.Sec) (C : Set X), M.IsLB → IsIrreducible C → IsClosed C → (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X)).Nonempty → ¬ C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) ∧ topologicalKrullDim C ≤ topologicalKrullDim C' + 1 := by
  first | exact @GlobalTheory.KrullZero.exists_irreducible_zero | exact GlobalTheory.KrullZero.exists_irreducible_zero | (intros; apply GlobalTheory.KrullZero.exists_irreducible_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibre
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.AmpleCut

theorem le_of_succ_le_add_one {x : WithBot ℕ∞} {d : ℕ} (h : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ x + 1) :
    (d : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe n =>
      have : d + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : d ≤ n)

theorem exists_irreducible_diff_NV : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d e : ℕ) (C : Set X) (f : X.functionField), ℓ.Prime →
    IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C → 0 < e →
    f ∈ P.H e 0 → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ NV P e 0 f ∧
      (d : WithBot ℕ∞) ≤ topologicalKrullDim C' := by
  intro k _ X _ p D hX P hA ℓ d e C f hℓ hCi hCc hCf hdim he hf
  by_cases h0 : C ∩ NV P e 0 f = ∅
  · refine ⟨C, hCi, hCc, fun x hx => ⟨hx, fun hx' => ?_⟩, ?_⟩
    · exact (Set.eq_empty_iff_forall_notMem.1 h0) x ⟨hx, hx'⟩
    · exact le_trans (by exact_mod_cast Nat.le_succ d) hdim
  obtain ⟨u, hu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P e).2 f hf
  have hisP : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hX.isProjOver
  have hne : (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)).Nonempty := by
    rw [← hu]; exact Set.nonempty_iff_ne_empty.2 h0
  by_cases hsub : C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)
  · exfalso
    have haff := IsAmpleLB.isAffineOpen_nonzeroLocus p hA he u
    have h1 := GlobalTheory.T.topologicalKrullDim_le_zero_fibre_affineOpen k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) ℓ _ C hℓ haff hCi hCc hCf hsub
    have h2 := hdim.trans h1
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h2
    have := WithBot.coe_le_coe.1 this
    norm_cast at this
  · obtain ⟨C', h1, h2, h3, h4⟩ :=
      GlobalTheory.T.exists_irreducible_zeroSet_section_closedIrreducible k X p D hX (lbPow P.L.B e) u C (isLB_lbPow hA.isLB e) hCi hCc hne hsub
    refine ⟨C', h1, h2, ?_, le_of_succ_le_add_one (hdim.trans h4)⟩
    rw [hu]; exact h3

end GlobalTheory.AmpleCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d e : ℕ) (C : Set X) (f : X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C → 0 < e → f ∈ P.H e 0 → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ NV P e 0 f ∧ (d : WithBot ℕ∞) ≤ topologicalKrullDim C' := by
  first | exact @GlobalTheory.AmpleCut.exists_irreducible_diff_NV | exact GlobalTheory.AmpleCut.exists_irreducible_diff_NV | (intros; apply GlobalTheory.AmpleCut.exists_irreducible_diff_NV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVertical
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem GlobalTheory.HSAmp.common_zero_of_le_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  intro k _ X _ p D hX P hA ℓ d
  induction d with
  | zero =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨x, hx⟩ := hC.nonempty
    exact ⟨x, hx, by simp⟩
  | succ d ih =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨C', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre k X p D hX P hA ℓ d (e 0) C (g 0) hℓ hC hCc hCf
      (by exact_mod_cast hd) (hg 0).1 (hg 0).2
    obtain ⟨x, hxC', hx⟩ := ih C' (fun j => e j.succ) (fun j => g j.succ) hℓ h1 h2
      (h3.trans (Set.diff_subset.trans hCf)) h4 (fun j => hg j.succ)
    refine ⟨x, (h3 hxC').1, ?_⟩
    simp only [Set.mem_iUnion, not_exists] at hx ⊢
    intro j
    refine Fin.cases ?_ (fun j => hx j) j
    exact (h3 hxC').2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVerticalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_zero_ample_sections_vertical : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  first | exact @GlobalTheory.HSAmp.common_zero_of_le_dim | exact GlobalTheory.HSAmp.common_zero_of_le_dim | (intros; apply GlobalTheory.HSAmp.common_zero_of_le_dim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsCutGenericFibreFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_sec_nonvanishing_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  intro k _ X _ p D _ P hA S hS
  obtain ⟨n, hn, s, h₁, -, -⟩ := hA.exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
  obtain ⟨f, hf, e⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P n).1 s
  refine ⟨n, hn, f, hf, ?_⟩
  rw [e]
  exact h₁

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  first | exact @GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | exact GlobalTheory.HSAmp.exists_sec_nonvanishing_finite | (intros; apply GlobalTheory.HSAmp.exists_sec_nonvanishing_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsCutGenericFibreFinite
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GenCut

theorem exists_finite_drop {T : Type} [TopologicalSpace T] [NoetherianSpace T] (Y : Set T) (d : ℕ)
    (hY : topologicalKrullDim Y ≤ (d + 1 : ℕ)) :
    ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → topologicalKrullDim ↥(Y \ U) ≤ d := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hne : ∀ C : irreducibleComponents Y, ∃ y : Y, y ∈ C.1 := fun C => C.2.1.nonempty
  choose y hy using hne
  have : Finite (irreducibleComponents Y) := hfin.to_subtype
  refine ⟨Set.range fun C => (y C : T), Set.finite_range _, fun U hU hS => ?_⟩
  have hC : IsClosed ((Subtype.val : Y → T) ⁻¹' Uᶜ) := hU.isClosed_compl.preimage continuous_subtype_val
  have h := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero Y).1 _ (d + 1) hC hY fun Z hZ _ hsub =>
    hsub (hy ⟨Z, hZ⟩) (hS ⟨⟨Z, hZ⟩, rfl⟩)
  let f : ↥(Y \ U) → ↥((Subtype.val : Y → T) ⁻¹' Uᶜ) := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  have hf : IsInducing f := by
    refine (IsInducing.subtypeVal.comp IsInducing.subtypeVal).of_comp_iff.1 ?_
    exact IsInducing.subtypeVal
  have h2 := lt_of_le_of_lt hf.topologicalKrullDim_le h
  rw [Nat.cast_add, Nat.cast_one] at h2
  exact ENat.WithBot.lt_add_one_iff.1 h2

theorem exists_sections_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → topologicalKrullDim ↥(Z ∩ fib X 0) ≤ d → ∃ (e : Fin d → ℕ) (g : Fin d → X.functionField), (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) ∧ ((Z \ ⋃ j, NV P (e j) 0 (g j)) ∩ fib X 0).Finite := by
  intro k _ X _ p D hp P hA d
  have := hp.isNoetherian
  induction d with
  | zero =>
    intro Z _ hd
    have hf : Finite ↥(Z ∩ fib X 0) := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero ↥(Z ∩ fib X 0)).2 inferInstance (by simpa using hd)
    refine ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, ?_⟩
    exact (Set.toFinite (Z ∩ fib X 0)).subset (Set.inter_subset_inter_left _ Set.sdiff_subset)
  | succ d ih =>
    intro Z hZ hd
    obtain ⟨S, hS, hdrop⟩ := exists_finite_drop (Z ∩ fib X 0) d hd
    obtain ⟨e₀, he₀, f, hf, hSf⟩ := GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite k X p D hp P hA S hS
    have hU : IsOpen (NV P e₀ 0 f) := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e₀ 0 f hf).1
    have h := hdrop _ hU hSf
    rw [show (Z ∩ fib X 0) \ NV P e₀ 0 f = (Z \ NV P e₀ 0 f) ∩ fib X 0 from by
      ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto] at h
    obtain ⟨e, g, heg, hfin⟩ := ih _ (hZ.sdiff hU) h
    refine ⟨Fin.cons e₀ e, Fin.cons f g, fun j => ?_, hfin.subset ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨he₀, hf⟩
      · exact heg j
    · rintro x ⟨⟨hxZ, hx⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists] at hx
      refine ⟨⟨⟨hxZ, hx 0⟩, ?_⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists]
      exact fun j => hx j.succ

end GlobalTheory.HSAmp.GenCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsCutGenericFibreFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_cut_genericFibre_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → topologicalKrullDim ↥(Z ∩ fib X 0) ≤ d → ∃ (e : Fin d → ℕ) (g : Fin d → X.functionField), (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) ∧ ((Z \ ⋃ j, NV P (e j) 0 (g j)) ∩ fib X 0).Finite := by
  first | exact @GlobalTheory.HSAmp.GenCut.exists_sections_finite | exact GlobalTheory.HSAmp.GenCut.exists_sections_finite | (intros; apply GlobalTheory.HSAmp.GenCut.exists_sections_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenericFibreClosureInterResidueCharFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenericFibreClosureInterResidueCharFibre
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped TensorProduct

namespace GlobalTheory.GenFibClosure

theorem finite_of_finite_spec (K S : Type) [Field K] [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    [Finite (PrimeSpectrum S)] : Module.Finite K S := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := K)
  have : DiscreteTopology (PrimeSpectrum S) := JacobsonSpace.discreteTopology (Set.toFinite _)
  exact (Module.finite_iff_krullDimLE_zero K S).2
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.1 this).2

theorem isAlgebraic_of_injective {B S : Type} [CommRing B] [CommRing S] [Algebra ℚ S] [Module.Finite ℚ S]
    (f : B →+* S) (hf : Function.Injective f) : Algebra.IsAlgebraic ℤ B := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ S := Algebra.IsAlgebraic.trans ℤ ℚ S
  exact Algebra.IsAlgebraic.of_injective f.toIntAlgHom hf

theorem finiteType_of_surjective {A B : Type} [CommRing A] [CommRing B] [Algebra.FiniteType ℤ A]
    (f : A →+* B) (hf : Function.Surjective f) : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.of_surjective f.toIntAlgHom hf

theorem isAlgebraic_of_finite (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) : Algebra.IsAlgebraic ℤ B := by
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  let S := ℚ ⊗[ℤ] B
  letI : Algebra B S := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization M S := IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)
  have hinj := PrimeSpectrum.localization_comap_injective S M
  have hfin : Finite (PrimeSpectrum S) := by
    refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image (h.subset ?_) hinj.injOn)
    rintro _ ⟨Q, -, rfl⟩ n hn hQ
    have h1 : (n : S) ∈ Q.asIdeal := by
      have := hQ
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at this
      exact this
    have h2 : IsUnit (n : S) := by
      have : IsUnit (n : ℚ) := (Nat.cast_ne_zero.2 hn).isUnit
      simpa using this.map (algebraMap ℚ S)
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 h2)
  have hf : Module.Finite ℚ S := finite_of_finite_spec ℚ S
  have hi : Function.Injective (algebraMap B S) := by
    refine IsLocalization.injective S (M := M) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.ne_zero hz)
  exact isAlgebraic_of_injective _ hi

theorem finite_primes_domain (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum B | (l : B) ∈ Q.asIdeal}.Finite := by
  have := isAlgebraic_of_finite B h
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  have hd := GlobalTheory.IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one B (RingHom.injective_int _)
  rw [trdeg_eq_zero] at hd
  have hd1 : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_iff, hd]; simp
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {(l : B)})
  refine (hfin.preimage (f := PrimeSpectrum.asIdeal) fun _ _ _ _ e => PrimeSpectrum.ext e).subset ?_
  intro P hP
  refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hP⟩, fun Q hQ hQP => ?_⟩
  have hQ0 : Q ≠ ⊥ := fun e => by
    have := (Ideal.span_singleton_le_iff_mem _).1 hQ.2
    rw [e] at this
    exact Nat.cast_ne_zero.2 hl this
  have hm : Q.IsMaximal := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hd1 Q hQ0 hQ.1
  exact (hm.eq_of_le P.isPrime.ne_top hQP).ge

theorem finite_primes (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] (P : PrimeSpectrum A)
    (hP : ∀ n : ℕ, n ≠ 0 → (n : A) ∉ P.asIdeal)
    (h : {Q : PrimeSpectrum A | P ≤ Q ∧ ∀ n : ℕ, n ≠ 0 → (n : A) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum A | P ≤ Q ∧ (l : A) ∈ Q.asIdeal}.Finite := by
  let π := Ideal.Quotient.mk P.asIdeal
  have hs : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : CharZero (A ⧸ P.asIdeal) := @CharP.charP_to_charZero _ _ (by
    refine ⟨fun n => ⟨fun hn => ?_, fun hn => by rw [zero_dvd_iff.1 hn, Nat.cast_zero]⟩⟩
    by_contra hne
    refine hP n (fun e => hne (e ▸ dvd_rfl)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hn)
  have := finiteType_of_surjective π hs
  have hinj := PrimeSpectrum.comap_injective_of_surjective π hs
  have hr : Set.range (PrimeSpectrum.comap π) = PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := by
    rw [range_comap_of_surjective _ π hs, Ideal.mk_ker]
  have hf := finite_primes_domain (A ⧸ P.asIdeal) ((h.preimage hinj.injOn).subset fun Q hQ => ⟨by
    have : PrimeSpectrum.comap π Q ∈ PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := hr ▸ ⟨Q, rfl⟩
    exact this, fun n hn h1 => hQ n hn (by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h1; exact h1)⟩) l hl
  refine (hf.image (PrimeSpectrum.comap π)).subset ?_
  rintro Q ⟨h1, h2⟩
  have : Q ∈ Set.range (PrimeSpectrum.comap π) := hr ▸ h1
  obtain ⟨Q, rfl⟩ := this
  refine ⟨Q, ?_, rfl⟩
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h2
  exact h2

theorem natCast_eq_zero_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (Q : PrimeSpectrum Γ(X, U)) (n : ℕ) :
    (n : X.residueField (hU.fromSpec Q)) = 0 ↔ (n : Γ(X, U)) ∈ Q.asIdeal := by
  have hx : hU.fromSpec Q ∈ U := by
    have : hU.fromSpec Q ∈ Set.range hU.fromSpec := ⟨Q, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hb : hU.fromSpec Q ∈ X.basicOpen (n : Γ(X, U)) ↔ (n : Γ(X, U)) ∉ Q.asIdeal :=
    SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen _) Q
  rw [← map_natCast (X.evaluation U _ hx).hom n]
  exact (X.evaluation_eq_zero_iff_notMem_basicOpen _ hx _).trans (hb.not.trans not_not)

theorem finite_closure_inter_fib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  intro k _ X _ p D hX W hW hfin l
  have hsub : closure (W ∩ fib X 0) ⊆ W := closure_minimal Set.inter_subset_left hW
  rcases eq_or_ne l 0 with rfl | hl
  · exact hfin.subset (Set.inter_subset_inter_left _ hsub)
  have := hX.isNoetherian
  have hft : LocallyOfFiniteType (p ≫ spMap (Int.castRingHom k)) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hj ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    infer_instance
  have key (U : X.Opens) (hU : IsAffineOpen U) : (closure (W ∩ fib X 0) ∩ fib X l ∩ U).Finite := by
    have : Algebra.FiniteType ℤ Γ(X, U) := by
      set t := p ≫ spMap (Int.castRingHom k)
      have e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom =
        algebraMap ℤ Γ(X, U) := RingHom.ext_int _ _
      rw [← RingHom.finiteType_algebraMap, ← e, RingHom.finiteType_respectsIso.cancel_left_isIso]
      exact HasRingHomProperty.appLE @LocallyOfFiniteType t hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    have hemb := hU.fromSpec.isOpenEmbedding
    have h0 (Q : PrimeSpectrum Γ(X, U)) :
        hU.fromSpec Q ∈ fib X 0 ↔ ∀ n : ℕ, n ≠ 0 → (n : Γ(X, U)) ∉ Q.asIdeal := by
      change ringChar _ = 0 ↔ _
      simp only [← natCast_eq_zero_iff hU, ringChar.spec]
      refine ⟨fun h n hn => by rw [h, zero_dvd_iff]; exact hn, fun h => ?_⟩
      by_contra hne
      exact h _ hne dvd_rfl
    have hS : (hU.fromSpec ⁻¹' (W ∩ fib X 0)).Finite := hfin.preimage hemb.injective.injOn
    have hT := hS.biUnion (t := fun P : PrimeSpectrum Γ(X, U) =>
        {Q : PrimeSpectrum Γ(X, U) | P ≤ Q ∧ (l : Γ(X, U)) ∈ Q.asIdeal}) fun P hP =>
      finite_primes _ P ((h0 P).1 hP.2) (hS.subset fun Q hQ => ⟨hW.stableUnderSpecialization
        (((PrimeSpectrum.le_iff_specializes P Q).1 hQ.1).map hemb.continuous) hP.1, (h0 Q).2 hQ.2⟩) l hl
    refine (hT.image hU.fromSpec).subset ?_
    rintro y ⟨⟨hy, hyl⟩, hyU⟩
    have : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hyU
    obtain ⟨Q, rfl⟩ := this
    refine ⟨Q, ?_, rfl⟩
    have h1 : Q ∈ closure (hU.fromSpec ⁻¹' (W ∩ fib X 0)) := by
      rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]; exact hy
    rw [← Set.biUnion_of_singleton (hU.fromSpec ⁻¹' (W ∩ fib X 0)), hS.closure_biUnion] at h1
    obtain ⟨P, hP, h1⟩ := Set.mem_iUnion₂.1 h1
    refine Set.mem_iUnion₂.2 ⟨P, hP, (PrimeSpectrum.le_iff_specializes P Q).2 (specializes_iff_mem_closure.2 h1), ?_⟩
    exact (natCast_eq_zero_iff hU Q l).1 ((ringChar.spec _ _).2 (dvd_of_eq hyl))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.2)
    fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  refine (s.finite_toSet.biUnion fun U _ => key U.1 U.2).subset fun y hy => ?_
  obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact Set.mem_iUnion₂.2 ⟨U, hU, hy, hyU⟩

end GlobalTheory.GenFibClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenericFibreClosureInterResidueCharFibreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_genericFibreClosure_inter_residueCharFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  first | exact @GlobalTheory.GenFibClosure.finite_closure_inter_fib | exact GlobalTheory.GenFibClosure.finite_closure_inter_fib | (intros; apply GlobalTheory.GenFibClosure.finite_closure_inter_fib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem noetherianSpace_of_isArithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : NoetherianSpace X := by
  obtain ⟨N, j, hj, hjp⟩ := h.isProjOver
  haveI := h.isDomain
  haveI := h.finite
  haveI : IsNoetherian ℤ k := isNoetherian_of_isNoetherianRing_of_finite ℤ k
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  haveI : IsProper p := hjp ▸ inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  infer_instance

theorem exists_sec_fibre_dim_lt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z →
    (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) ≤ d) →
    ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, ∀ ℓ : ℕ, topologicalKrullDim ↥((Z \ NV P e 0 f) ∩ fib X ℓ) < d := by
  intro k _ X _ p D hX P hA d Z hZ hdim
  haveI : NoetherianSpace X := noetherianSpace_of_isArithVar hX
  have memfib : ∀ {x : X} {ℓ : ℕ}, x ∈ fib X ℓ ↔ ringChar (X.residueField x) = ℓ := Iff.rfl
  obtain ⟨hcov, hfibc, -, -, hWfib⟩ := GlobalTheory.T.projArith_residueCharFibre_structure k X p D hX
  have hNV : ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) :=
    fun a b g hg => (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P a b g hg).1

  obtain ⟨e₀, g, hg, hfin0⟩ := GlobalTheory.T.exists_sections_cut_genericFibre_finite k X p D hX P hA d Z hZ (hdim 0)
  have hW₀c : IsClosed (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) :=
    hZ.sdiff (isOpen_iUnion fun j => hNV _ _ _ (hg j).2)

  have hpick0 : ∀ Y : irreducibleComponents ↥(Z ∩ fib X 0), ∃ y : ↥(Z ∩ fib X 0), y ∈ Y.1 ∧
      IsClosed ({y} : Set ↥(Z ∩ fib X 0)) := fun Y =>
    (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
  choose q₀ hq₀ hq₀c using hpick0
  haveI : Finite (irreducibleComponents ↥(Z ∩ fib X 0)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  set W : Set X := (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) ∪ ⋃ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} with hWdef
  have hWc : IsClosed W := hW₀c.union (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hcl0 : ∀ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} ∩ fib X 0 ⊆ {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} := by
    rintro Y x ⟨hx, hx0⟩
    obtain ⟨K, hK, hKe⟩ := isClosed_induced_iff.1 (hq₀c Y)
    have hqK : ((q₀ Y : ↥(Z ∩ fib X 0)) : X) ∈ K := by
      have : q₀ Y ∈ Subtype.val ⁻¹' K := by rw [hKe]; rfl
      exact this
    have hxK : x ∈ K := closure_minimal (Set.singleton_subset_iff.2 hqK) hK hx
    have hxZ : x ∈ Z := closure_minimal (Set.singleton_subset_iff.2 (q₀ Y).2.1) hZ hx
    have : (⟨x, hxZ, hx0⟩ : ↥(Z ∩ fib X 0)) ∈ Subtype.val ⁻¹' K := hxK
    rw [hKe] at this
    exact congrArg Subtype.val this
  have hWfin : (W ∩ fib X 0).Finite := by
    refine (hfin0.union (Set.finite_range fun Y => ((q₀ Y : ↥(Z ∩ fib X 0)) : X))).subset ?_
    rintro x ⟨hx | hx, hx0⟩
    · exact Or.inl ⟨hx, hx0⟩
    · obtain ⟨Y, hY⟩ := Set.mem_iUnion.1 hx
      exact Or.inr ⟨Y, (hcl0 Y ⟨hY, hx0⟩).symm⟩

  obtain ⟨S, hSp, hWS⟩ := hWfib W hWc

  have hpick : ∀ i : (Σ ℓ : S, irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))), ∃ y : ↥(Z ∩ fib X (i.1 : ℕ)),
      y ∈ i.2.1 ∧ IsClosed ({(y : X)} : Set X) := by
    rintro ⟨ℓ, Y⟩
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ (hSp ℓ ℓ.2).ne_zero)
    obtain ⟨y, hy, hyc⟩ :=
      (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
    refine ⟨y, hy, ?_⟩
    have := hc.isClosedEmbedding_subtypeVal.isClosedMap _ hyc
    rwa [Set.image_singleton] at this
  choose q hq hqc using hpick
  haveI : ∀ ℓ : S, Finite (irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))) := fun _ =>
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hFc : IsClosed (Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X)) := by
    rw [← Set.iUnion_singleton_eq_range]
    exact isClosed_iUnion_of_finite hqc
  set T : Set X := closure (W ∩ fib X 0) ∪ Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X) with hTdef
  have hTc : IsClosed T := isClosed_closure.union hFc
  have hTfin : ∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite := fun ℓ =>
    ((GlobalTheory.T.finite_genericFibreClosure_inter_residueCharFibre k X p D hX W hWc hWfin ℓ).union (Set.finite_range _)).subset fun x ⟨hx, hxl⟩ =>
      hx.elim (fun h => Or.inl ⟨h, hxl⟩) Or.inr

  obtain ⟨e, he, f, hf, hTNV⟩ := GlobalTheory.T.exists_ample_pow_section_nonvanishing_on_closed k X p D hX P hA T hTc hTfin
  refine ⟨e, he, f, hf, fun ℓ => ?_⟩
  have hfo : IsOpen (NV P e 0 f) := hNV _ _ _ hf

  have key : ∀ Y ∈ irreducibleComponents ↥(Z ∩ fib X ℓ), (d : WithBot ℕ∞) ≤ topologicalKrullDim Y →
      ∃ s ∈ Y, (s : X) ∈ T := by
    intro Y hY hYd
    rcases eq_or_ne ℓ 0 with rfl | hℓ0
    · refine ⟨q₀ ⟨Y, hY⟩, hq₀ ⟨Y, hY⟩, Or.inl (subset_closure ⟨?_, (q₀ ⟨Y, hY⟩).2.2⟩)⟩
      exact Or.inr (Set.mem_iUnion.2 ⟨⟨Y, hY⟩, subset_closure rfl⟩)
    by_cases hℓS : ℓ ∈ S
    · exact ⟨q ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, hq ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, Or.inr ⟨_, rfl⟩⟩
    obtain ⟨s₀, -⟩ := hY.1.nonempty
    have hℓp : ℓ.Prime := by
      rcases hcov (s₀ : X) with h | ⟨ℓ', hℓ', h⟩
      · exact absurd ((memfib.1 s₀.2.2).symm.trans (memfib.1 h)) hℓ0
      · rwa [(memfib.1 s₀.2.2).symm.trans (memfib.1 h)]
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ hℓ0)
    have hCi : IsIrreducible (Subtype.val '' Y) := hY.1.image _ continuous_subtype_val.continuousOn
    have hCc : IsClosed (Subtype.val '' Y) :=
      hc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents Y hY)
    have hCf : Subtype.val '' Y ⊆ fib X ℓ := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2.2
    have hCd : (d : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Subtype.val '' Y) := by
      rwa [← (Topology.IsEmbedding.subtypeVal.homeomorphImage Y).isHomeomorph.topologicalKrullDim_eq]
    obtain ⟨x, ⟨s, hsY, rfl⟩, hxg⟩ :=
      GlobalTheory.T.exists_common_zero_ample_sections_vertical k X p D hX P hA ℓ d (Subtype.val '' Y) e₀ g hℓp hCi hCc hCf hCd hg
    refine ⟨s, hsY, ?_⟩
    have hxW : (s : X) ∈ W := Or.inl ⟨s.2.1, hxg⟩
    rcases hWS hxW with h | h
    · exact Or.inl h
    · obtain ⟨ℓ', hℓ'S, h'⟩ := Set.mem_iUnion₂.1 h
      have : ℓ' = ℓ := (memfib.1 h').symm.trans (memfib.1 s.2.2)
      exact absurd (this ▸ hℓ'S) hℓS
  have hCsc : IsClosed {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} :=
    (hfo.preimage continuous_subtype_val).isClosed_compl
  have hdrop := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero ↥(Z ∩ fib X ℓ)).1 _ d hCsc (hdim ℓ) fun Y hY hYd hsub => by
    obtain ⟨s, hsY, hsT⟩ := key Y hY hYd
    exact hsub hsY (hTNV hsT)
  have hset : Subtype.val '' {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} = (Z \ NV P e 0 f) ∩ fib X ℓ := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s.2.1, hs⟩, s.2.2⟩
    · rintro ⟨⟨hxZ, hxN⟩, hxl⟩
      exact ⟨⟨x, hxZ, hxl⟩, hxN, rfl⟩
  rw [← hset, ← (Topology.IsEmbedding.subtypeVal.homeomorphImage _).isHomeomorph.topologicalKrullDim_eq]
  exact hdrop

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimensionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_lowering_fibre_dimension : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) ≤ d) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, ∀ ℓ : ℕ, topologicalKrullDim ↥((Z \ NV P e 0 f) ∩ fib X ℓ) < d := by
  first | exact @GlobalTheory.HSAmp.exists_sec_fibre_dim_lt | exact GlobalTheory.HSAmp.exists_sec_fibre_dim_lt | (intros; apply GlobalTheory.HSAmp.exists_sec_fibre_dim_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArith
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.NoethGens

theorem exists_cover (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) (d : ℕ) :
    ∀ Z : Set X, IsClosed Z → (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) < d) →
      ∃ (e : ℕ) (x : Fin d → X.functionField), 0 < e ∧ (∀ l, x l ∈ P.H e 0) ∧ ∀ z ∈ Z, ∃ l, z ∈ NV P e 0 (x l) := by
  induction d with
  | zero =>
    intro Z _ h
    refine ⟨1, Fin.elim0, one_pos, fun l => l.elim0, fun z hz => ?_⟩
    exfalso
    have h₁ := h (ringChar (X.residueField z))
    have hne : Nonempty ↥(Z ∩ fib X (ringChar (X.residueField z))) := ⟨⟨z, hz, rfl⟩⟩
    obtain ⟨w⟩ := hne
    have hne' : Nonempty (IrreducibleCloseds ↥(Z ∩ fib X (ringChar (X.residueField z)))) :=
      ⟨⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Z ∩ fib X (ringChar (X.residueField z))) :=
      Order.krullDim_nonneg
    exact absurd h₁ (not_lt.2 (by simpa using h₂))
  | succ d ih =>
    intro Z hZ h
    obtain ⟨e, he, f, hf, hlt⟩ := GlobalTheory.T.exists_section_lowering_fibre_dimension k X p D hX P hP d Z hZ fun ℓ =>
      ENat.WithBot.lt_add_one_iff.1 (by simpa using h ℓ)
    have hnf := GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 f hf
    obtain ⟨e', x, he', hx, hc⟩ := ih (Z \ NV P e 0 f) (hZ.sdiff hnf.1) hlt
    have c₁ : ((e' * e : ℕ) : ℤ) = (e' : ℤ) * (e : ℤ) := Nat.cast_mul _ _
    have c₂ : ((e' * e : ℕ) : ℤ) = (e : ℤ) * (e' : ℤ) := by rw [c₁, mul_comm]
    refine ⟨e' * e, Fin.cons (f ^ e') fun l => x l ^ e, Nat.mul_pos he' he, fun l => ?_, fun z hz => ?_⟩
    · refine Fin.cases ?_ (fun l => ?_) l
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 f hf e').1
        rw [mul_zero, ← c₁] at this
        simpa only [Fin.cons_zero] using this
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e' 0 (x l) (hx l) e).1
        rw [mul_zero, ← c₂] at this
        simpa only [Fin.cons_succ] using this
    · by_cases hzf : z ∈ NV P e 0 f
      · refine ⟨0, ?_⟩
        have := hnf.2.2.1 e' he'
        rw [mul_zero, ← c₁] at this
        rw [Fin.cons_zero, this]
        exact hzf
      · obtain ⟨l, hl⟩ := hc z ⟨hz, hzf⟩
        refine ⟨l.succ, ?_⟩
        have := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e' 0 (x l) (hx l)).2.2.1 e he
        rw [mul_zero, ← c₂] at this
        rw [Fin.cons_succ, this]
        exact hl

theorem exists_gens (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) :
    ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  obtain ⟨e, x, he, hx, hc⟩ := exists_cover k X p D hX P hP (D + 1) Set.univ isClosed_univ fun ℓ => by
    rw [Set.univ_inter, Nat.cast_add_one]
    exact ENat.WithBot.lt_add_one_iff.2 ((GlobalTheory.T.projArith_residueCharFibre_structure k X p D hX).2.2.2.1 ℓ)
  exact ⟨e, x, he, hx, fun z => hc z trivial⟩

end GlobalTheory.HSAmp.NoethGens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArithStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  first | exact @GlobalTheory.HSAmp.NoethGens.exists_gens | exact GlobalTheory.HSAmp.NoethGens.exists_gens | (intros; apply GlobalTheory.HSAmp.NoethGens.exists_gens <;> assumption)
end
