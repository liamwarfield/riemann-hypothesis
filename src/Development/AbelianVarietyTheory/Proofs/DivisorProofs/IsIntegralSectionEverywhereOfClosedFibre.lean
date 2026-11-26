module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfIntegralAtFibreGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemNearFibreOfGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemNearFibreOfGenericPoint
open TensorProduct

namespace GlobalTheory.Mum.FibreReg

section Regular

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem regular_of_exact [Module.Flat A B] (c : B) {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : ∀ z : B ⊗[A] N₁, c • z = 0 → z = 0) (h₃ : ∀ z : B ⊗[A] N₃, c • z = 0 → z = 0) :
    ∀ z : B ⊗[A] N₂, c • z = 0 → z = 0 := by
  intro z hz
  have e3 : g.baseChange B z = 0 := h₃ _ (by rw [← map_smul, hz, map_zero])
  obtain ⟨y, rfl⟩ := ((lTensor_exact B hfg hg) z).1 e3
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  have : c • y = 0 := hinj (by
    have : f.baseChange B (c • y) = 0 := by rw [map_smul]; exact hz
    rw [map_zero]; exact this)
  rw [h₁ y this, map_zero]

theorem regular_quotient (c : B) (p : Ideal A)
    (hc : ∀ b : B, c * b ∈ p.map (algebraMap A B) → b ∈ p.map (algebraMap A B))
    {N : Type} [AddCommGroup N] [Module A N] (e : N ≃ₗ[A] A ⧸ p) :
    ∀ z : B ⊗[A] N, c • z = 0 → z = 0 := by
  intro z hz
  let E : B ⊗[A] N ≃ₗ[B] B ⧸ p.map (algebraMap A B) :=
    (e.baseChange A B).trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).symm.toLinearEquiv
  apply E.injective
  have h : c • E z = 0 := by rw [← map_smul, hz, map_zero]
  rw [map_zero]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (E z)
  rw [← hb] at h ⊢
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply hc
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h

variable [IsNoetherianRing A] [IsLocalRing B] [Module.Flat A B]

theorem regular_of_torsion (c : B) (q : Ideal A) (hq : q = (IsLocalRing.maximalIdeal B).comap (algebraMap A B))
    (hc : ∀ b : B, c * b ∈ q.map (algebraMap A B) → b ∈ q.map (algebraMap A B)) (n : ℕ)
    (N : Type) [AddCommGroup N] [Module A N] [hN : Module.Finite A N] :
    (∀ a ∈ q ^ n, ∀ v : N, a • v = 0) → ∀ z : B ⊗[A] N, c • z = 0 → z = 0 := by
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A with
  | subsingleton N => intro _ z _; exact Subsingleton.elim _ _
  | quotient N p e =>
    intro h
    have hle : q ≤ p.asIdeal := by
      refine (p.isPrime.pow_le_iff (n := n + 1) n.succ_ne_zero).1 fun a ha => ?_
      have := congrArg e (h a (Ideal.pow_le_pow_right n.le_succ ha) (e.symm 1))
      rw [map_smul, map_zero, e.apply_symm_apply, ← Algebra.algebraMap_eq_smul_one] at this
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    refine regular_quotient c p.asIdeal ?_ e
    by_cases hpq : p.asIdeal ≤ q
    · rw [le_antisymm hpq hle]; exact hc
    · obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hpq
      rw [hq, Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal] at ha'
      rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha) ha']
      intro b _; trivial
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro h
    refine regular_of_exact c f g hf hg hfg (h₁ fun a ha v => hf ?_) (h₃ fun a ha v => ?_)
    · rw [map_smul, h a ha, map_zero]
    · obtain ⟨w, rfl⟩ := hg v
      rw [← map_smul, h a ha, map_zero]

variable [IsNoetherianRing B]

theorem regular_of_finite (c : B) (q : Ideal A) (hq : q = (IsLocalRing.maximalIdeal B).comap (algebraMap A B))
    (hc : ∀ b : B, c * b ∈ q.map (algebraMap A B) → b ∈ q.map (algebraMap A B))
    (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N] :
    ∀ z : B ⊗[A] N, c • z = 0 → z = 0 := by
  intro z hz
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := B ⊗[A] N) (IsLocalRing.maximalIdeal B)
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  rw [← Submodule.mem_bot B, ← key, Submodule.mem_iInf]
  intro n
  let P : Submodule A N := q ^ n • ⊤
  have e3 : P.mkQ.baseChange B z = 0 := by
    refine regular_of_torsion c q hq hc n (N ⧸ P) (fun a ha v => ?_) _ (by rw [← map_smul, hz, map_zero])
    obtain ⟨w, rfl⟩ := P.mkQ_surjective v
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha trivial)
  obtain ⟨y, rfl⟩ := ((lTensor_exact B (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective) z).1 e3
  clear e3 hz
  induction y with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul b v =>
    obtain ⟨v, hv⟩ := v
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    refine Submodule.smul_induction_on (p := fun d : N => b ⊗ₜ[A] d ∈
      (IsLocalRing.maximalIdeal B) ^ n • (⊤ : Submodule B (B ⊗[A] N))) hv ?_ ?_
    · intro r hr d _
      rw [tmul_smul, ← algebraMap_smul B r]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      have h1 : q.map (algebraMap A B) ≤ IsLocalRing.maximalIdeal B := by
        rw [hq]; exact Ideal.map_comap_le
      refine Ideal.pow_right_mono h1 n ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hr
    · intro d e hd he
      rw [tmul_add]
      exact add_mem hd he

theorem regular_tensor (c : B) (q : Ideal A) (hq : q = (IsLocalRing.maximalIdeal B).comap (algebraMap A B))
    (hc : ∀ b : B, c * b ∈ q.map (algebraMap A B) → b ∈ q.map (algebraMap A B))
    (N : Type) [AddCommGroup N] [Module A N] :
    ∀ z : B ⊗[A] N, c • z = 0 → z = 0 := by
  classical
  intro z hz
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  let P : Submodule A N := Submodule.span A (S.image Prod.snd : Finset N)
  haveI : Module.Finite A P := Module.Finite.span_of_finite A (Finset.finite_toSet _)
  let y : B ⊗[A] P := ∑ i ∈ S.attach, i.1.1 ⊗ₜ[A] (⟨i.1.2, Submodule.subset_span (by
    simpa using ⟨i.1.1, i.2⟩)⟩ : P)
  have hy : P.subtype.baseChange B y = ∑ i ∈ S, i.1 ⊗ₜ[A] i.2 := by
    rw [← Finset.sum_attach S]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [y, map_sum]
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := B) P.subtype P.injective_subtype
  have : c • y = 0 := hinj (by
    have : P.subtype.baseChange B (c • y) = 0 := by rw [map_smul, hy]; exact hz
    rw [map_zero]; exact this)
  rw [← hy, regular_of_finite c q hq hc P y this, map_zero]

end Regular

section Fibre

variable {A C : Type} [CommRing A] [CommRing C] [Algebra A C] [Algebra.Smooth A C]

theorem isRadical_map_of_smooth (q : Ideal A) [q.IsPrime] : (q.map (algebraMap A C)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A ⧸ q) ((A ⧸ q) ⊗[A] C)
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C q)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C q).injective

theorem regular_mod_fibre (p₀ p : Ideal C) [p₀.IsPrime] [p.IsPrime]
    (h0 : p₀.comap (algebraMap A C) = p.comap (algebraMap A C))
    (hmin : ∀ P : Ideal C, P.IsPrime → P.comap (algebraMap A C) = p.comap (algebraMap A C) → p₀ ≤ P)
    (c : C) (hc : c ∉ p₀) (b : Localization.AtPrime p)
    (hb : algebraMap C (Localization.AtPrime p) c * b ∈
      (p.comap (algebraMap A C)).map (algebraMap A (Localization.AtPrime p))) :
    b ∈ (p.comap (algebraMap A C)).map (algebraMap A (Localization.AtPrime p)) := by
  set q := p.comap (algebraMap A C) with hq
  have hmap : q.map (algebraMap A (Localization.AtPrime p)) =
      (q.map (algebraMap A C)).map (algebraMap C (Localization.AtPrime p)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hle : p₀ ≤ p := hmin p inferInstance rfl
  have hrad : (q.map (algebraMap A (Localization.AtPrime p))).IsRadical := by
    rw [hmap, ← Ideal.radical_eq_iff, ← IsLocalization.map_radical p.primeCompl,
      (isRadical_map_of_smooth (C := C) q).radical]
  obtain ⟨d, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl b
  rw [IsLocalization.mk'_mem_iff]
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_iff, hmap,
    IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl] at hb
  obtain ⟨s', hs', hb⟩ := hb
  have hd : d ∈ p₀ := by
    have h1 : q.map (algebraMap A C) ≤ p₀ := Ideal.map_le_iff_le_comap.2 h0.ge
    rcases (‹p₀.IsPrime›.mem_or_mem (h1 hb)) with h | h
    · exact absurd (hle h) hs'
    · exact (‹p₀.IsPrime›.mem_or_mem h).resolve_left hc
  rw [← hrad.radical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro Q ⟨hQ, hQp⟩
  refine hmin (Ideal.comap (algebraMap C (Localization.AtPrime p)) Q) inferInstance (le_antisymm ?_ ?_) hd
  · refine Ideal.comap_mono ?_
    refine (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQp.ne_top)).trans ?_
    exact (Localization.AtPrime.under_maximalIdeal).le
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, ← Ideal.map_le_iff_le_comap]
    exact hQ

theorem isIntegral_tensor_of_fibre [IsNoetherianRing A] {K : Type} [CommRing K] [Algebra A K]
    (p₀ p : Ideal C) [p₀.IsPrime] [p.IsPrime]
    (h0 : p₀.comap (algebraMap A C) = p.comap (algebraMap A C))
    (hmin : ∀ P : Ideal C, P.IsPrime → P.comap (algebraMap A C) = p.comap (algebraMap A C) → p₀ ≤ P)
    (f : C ⊗[A] K) (c : C) (hc : c ∉ p₀) (hf : IsIntegral C (c • f)) :
    ∃ s, s ∉ p ∧ IsIntegral C (s • f) := by
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let B := Localization.AtPrime p
  haveI : Module.Flat A B := Module.Flat.trans A C B
  let I : Submodule A K := Subalgebra.toSubmodule (integralClosure A K)
  have hex := lTensor_exact C (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
  have key : ∀ g : C ⊗[A] K, IsIntegral C g ↔ I.mkQ.baseChange C g = 0 := by
    intro g
    refine Iff.trans ?_ (hex g).symm
    constructor
    · intro hg
      obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := A) (S := C) (B := K)).2 ⟨g, hg⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, rfl⟩
      exact (TensorProduct.toIntegralClosure A C K y).2
  let φ : C ⊗[A] (K ⧸ I) →ₗ[C] B ⊗[A] (K ⧸ I) :=
    AlgebraTensorModule.rTensor A (K ⧸ I) (Algebra.linearMap C B)
  haveI : IsLocalizedModule p.primeCompl φ := inferInstance
  have h1 : c • I.mkQ.baseChange C f = 0 := by rw [← map_smul]; exact (key _).1 hf
  have h2 : φ (I.mkQ.baseChange C f) = 0 := by
    refine regular_tensor (algebraMap C B c) (p.comap (algebraMap A C)) ?_
      (regular_mod_fibre p₀ p h0 hmin c hc) (K ⧸ I) _ ?_
    · rw [IsScalarTower.algebraMap_eq A C B, ← Ideal.comap_comap]
      exact congrArg _ (Localization.AtPrime.under_maximalIdeal).symm
    · rw [algebraMap_smul, ← map_smul, h1, map_zero]
  obtain ⟨⟨s, hs⟩, h3⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl φ).1 h2
  exact ⟨s, hs, (key _).2 (by rw [map_smul]; exact h3)⟩

theorem isIntegral_pushout_of_fibre [IsNoetherianRing A] {K D : Type} [CommRing K] [Algebra A K] [CommRing D]
    [Algebra A D] [Algebra C D] [Algebra K D] [IsScalarTower A C D] [IsScalarTower A K D] [Algebra.IsPushout A C K D]
    (p₀ p : Ideal C) [p₀.IsPrime] [p.IsPrime]
    (h0 : p₀.comap (algebraMap A C) = p.comap (algebraMap A C))
    (hmin : ∀ P : Ideal C, P.IsPrime → P.comap (algebraMap A C) = p.comap (algebraMap A C) → p₀ ≤ P)
    (f : D) (c : C) (hc : c ∉ p₀) (hf : IsIntegral C (algebraMap C D c * f)) :
    ∃ s, s ∉ p ∧ IsIntegral C (algebraMap C D s * f) := by
  let e := Algebra.IsPushout.equiv A C K D
  obtain ⟨s, hs, h⟩ := isIntegral_tensor_of_fibre p₀ p h0 hmin (e.symm f) c hc (by
    have := hf.map e.symm.toAlgHom
    rwa [← Algebra.smul_def, map_smul] at this)
  refine ⟨s, hs, ?_⟩
  have := h.map e.toAlgHom
  rw [map_smul, Algebra.smul_def] at this
  simpa using this

end Fibre

end GlobalTheory.Mum.FibreReg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem intElem_basicOpen_of_mul {X Y : Scheme.{0}} (α : Y ⟶ X) (W : X.Opens) (f : Γ(Y, α ⁻¹ᵁ W)) (s : Γ(X, W))
    (h : (α.app W).hom.IsIntegralElem ((α.app W).hom s * f)) :
    (α.app (X.basicOpen s)).hom.IsIntegralElem
      ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le s))).op).hom f) := by
  have e1 : (Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le s))).op).hom.comp (α.app W).hom =
      (α.app (X.basicOpen s)).hom.comp (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.naturality]; rfl
  have h1 := h.map (Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le s))).op).hom
  rw [e1, map_mul] at h1
  have h2 := isIntegralElem_of_comp _ _ h1
  have e2 := RingHom.congr_fun e1 s
  simp only [RingHom.comp_apply] at e2
  rw [e2] at h2
  obtain ⟨u, hu⟩ : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom s) :=
    X.toRingedSpace.isUnit_res_basicOpen s
  have h3 := RingHom.IsIntegralElem.mul _ ((α.app (X.basicOpen s)).hom.isIntegralElem_map (x := ↑u⁻¹)) h2
  rwa [← _root_.mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, _root_.one_mul] at h3

theorem intElem_basicOpen_of_fibre_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens), IsAffineOpen W → ∀ (U : M.S.Opens), IsAffineOpen U → W ≤ G.hom ⁻¹ᵁ U → ∀ (f : Γ(Y, α ⁻¹ᵁ W)) (x ζ : G.left), x ∈ W → G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → (∃ c : Γ(G.left, W), ζ ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f)) → ∃ c : Γ(G.left, W), x ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f) := by
  intro R _ _ _ _ M G hG _ _ Y α t hpb W hW U hU hWU f x ζ hx hζ hsp ⟨c, hc, hint⟩
  have hYa := isAffineOpen_preimage_genericBaseChange R M G Y α t hpb W hW
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI : IsNoetherianRing Γ(M.S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom c ^ n * f) := by
    haveI := hW.isLocalization_basicOpen c
    letI : Algebra Γ(Y, α ⁻¹ᵁ W) Γ(Y, α ⁻¹ᵁ G.left.basicOpen c) :=
      (Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom.toAlgebra
    haveI : IsLocalization.Away ((α.app W).hom c) Γ(Y, α ⁻¹ᵁ G.left.basicOpen c) :=
      hYa.isLocalization_of_eq_basicOpen _ (homOfLE (α.preimage_mono (G.left.basicOpen_le c)))
        (Scheme.preimage_basicOpen α c)
    refine intElem_pow_mul_of_away (α.app W).hom c (Rt := Γ(G.left, G.left.basicOpen c))
      (St := Γ(Y, α ⁻¹ᵁ G.left.basicOpen c)) (α.app (G.left.basicOpen c)).hom ?_ f hint
    show (α.app (G.left.basicOpen c)).hom.comp (G.left.presheaf.map (homOfLE (G.left.basicOpen_le c)).op).hom =
      (Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom.comp (α.app W).hom
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.naturality]; rfl

  have hζW : ζ ∈ W := G.left.basicOpen_le c hc
  obtain ⟨p, rfl⟩ : x ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hx
  obtain ⟨p₀, rfl⟩ : ζ ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hζW
  have hmem : ∀ (P : PrimeSpectrum Γ(G.left, W)) (s : Γ(G.left, W)),
      hW.fromSpec P ∈ G.left.basicOpen s ↔ s ∉ P.asIdeal := fun P s => by
    change P ∈ hW.fromSpec ⁻¹ᵁ G.left.basicOpen s ↔ _
    rw [hW.fromSpec_preimage_basicOpen]
    rfl
  have hsq : ∀ P : PrimeSpectrum Γ(G.left, W), G.hom (hW.fromSpec P) =
      hU.fromSpec (PrimeSpectrum.comap (algebraMap Γ(M.S, U) Γ(G.left, W)) P) := fun P => by
    have := IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hW hWU
    exact (congrArg (fun φ : Spec Γ(G.left, W) ⟶ M.S => φ P) this).symm
  have hcomap : ∀ P Q : PrimeSpectrum Γ(G.left, W), G.hom (hW.fromSpec P) = G.hom (hW.fromSpec Q) ↔
      P.asIdeal.comap (algebraMap Γ(M.S, U) Γ(G.left, W)) =
        Q.asIdeal.comap (algebraMap Γ(M.S, U) Γ(G.left, W)) := fun P Q => by
    rw [hsq, hsq]
    exact hU.fromSpec.isOpenEmbedding.injective.eq_iff.trans PrimeSpectrum.ext_iff
  haveI := PrimeSpectrum.isPrime p₀
  haveI := PrimeSpectrum.isPrime p
  obtain ⟨s, hs, h⟩ := FibreReg.isIntegral_pushout_of_fibre (A := Γ(M.S, U))
    (K := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)) (PrimeSpectrum.asIdeal p₀) (PrimeSpectrum.asIdeal p)
    ((hcomap p₀ p).1 hζ) (fun P hP e => by
      have h1 := hsp _ ((hcomap ⟨P, hP⟩ p).2 e)
      exact (PrimeSpectrum.le_iff_specializes p₀ ⟨P, hP⟩).2
        (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 h1)) f (c ^ n)
    (fun h => (hmem p₀ c).1 hc ((PrimeSpectrum.isPrime p₀).mem_of_pow_mem n h))
    (by rw [map_pow]; exact hn)
  exact ⟨s, (hmem p s).2 hs, intElem_basicOpen_of_mul α W f s h⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemNearFibreOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralElem_near_fibre_of_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens), IsAffineOpen W → ∀ (U : M.S.Opens), IsAffineOpen U → W ≤ G.hom ⁻¹ᵁ U → ∀ (f : Γ(Y, α ⁻¹ᵁ W)) (x ζ : G.left), x ∈ W → G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → (∃ c : Γ(G.left, W), ζ ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f)) → ∃ c : Γ(G.left, W), x ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f) := by
  first | exact @GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic | exact GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic | (intros; apply GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem chart_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chart_res_app {X Y : Scheme.{0}} (α : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE (α.preimage_mono h)).op).hom ((α.app U).hom x) =
      (α.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]; rfl

theorem isIntegralElem_of_square {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (a : A →+* C) (b : B →+* D) (h : g.comp a = b.comp f) {x : B}
    (hx : f.IsIntegralElem x) : g.IsIntegralElem (b x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map a, hp.map a, ?_⟩
  rw [Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂, hpx, map_zero]

theorem intAt_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X) :
    IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W →
      ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem
        ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  intro hint j W hW hWa hζW
  obtain ⟨j', W', hW', hζW', hW'a, hint'⟩ := hint
  obtain ⟨c, hcle, hζc⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨ζ, hζW, hζW'⟩ hζW
  refine ⟨c, hζc, ?_⟩
  have hBW : X.basicOpen c ≤ W := hcle.trans inf_le_left
  have hBW' : X.basicOpen c ≤ W' := hcle.trans inf_le_right
  have hBV : α ⁻¹ᵁ X.basicOpen c ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) ⊓
      LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j') :=
    le_inf ((α.preimage_mono hBW).trans (locInt_le_chart L α j W hW))
      ((α.preimage_mono hBW').trans (locInt_le_chart L α j' W' hW'))
  have hBjj : X.basicOpen c ≤ L.U j ⊓ L.U j' := le_inf (hBW.trans hW) (hBW'.trans hW')
  have key := congrArg (Y.presheaf.map (homOfLE hBV).op).hom (s.compat (fun _ => j) (fun _ => j'))
  erw [chart_res_res, map_mul, chart_res_res] at key
  have ht : (Y.presheaf.map (homOfLE hBV).op).hom
      ((LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))).g (fun _ => j) (fun _ => j')).val =
      (α.app (X.basicOpen c)).hom (((X.presheaf.map (homOfLE hBjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k) := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, res, pullU, Units.coe_map, map_pow]
    congr 1
    erw [Units.coe_map, Units.coe_map]
    erw [chart_res_res, ← chart_res_app α hBjj]
    rfl
  have hj' : (α.app (X.basicOpen c)).hom.IsIntegralElem
      ((Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (chartVal L α s j' W' hW')) :=
    isIntegralElem_of_square (α.app W').hom (α.app (X.basicOpen c)).hom (X.presheaf.map (homOfLE hBW').op).hom
      (Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (RingHom.ext fun x => (chart_res_app α hBW' x).symm) hint'
  rw [chartVal] at hj' ⊢
  erw [chart_res_res] at hj' ⊢
  erw [key, ht]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hj'

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_integral_of_integral_at_point : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X), IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W → ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  first | exact @GlobalTheory.Mum.intAt_chart | exact GlobalTheory.Mum.intAt_chart | (intros; apply GlobalTheory.Mum.intAt_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfIntegralAtFibreGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_intAt_fibreGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k) (x ζ : G.left), G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → IntAt L α s ζ → IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hgen hint
  have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := G.hom x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := L.U j ⊓ G.hom ⁻¹ᵁ U) ⟨hj, hxU⟩
  have hζW : ζ ∈ W := (hgen x rfl).mem_open W.isOpen hxW
  have hWj : W ≤ L.U j := fun z hz => (hWle hz).1
  have hWU : W ≤ G.hom ⁻¹ᵁ U := fun z hz => (hWle hz).2
  obtain ⟨c', hxc', hc'⟩ := GlobalTheory.T.isIntegralElem_near_fibre_of_generic_point R M G hsm hqc hgi Y α t hpb W hW U hU hWU (chartVal L α s j W hWj) x ζ hxW hζ hgen
    (GlobalTheory.T.exists_basicOpen_integral_of_integral_at_point L α k s ζ hint j W hWj hW hζW)
  refine ⟨j, G.left.basicOpen c', (G.left.basicOpen_le c').trans hWj, hxc', hW.basicOpen c', ?_⟩
  convert hc' using 1
  simp only [chartVal]
  erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfIntegralAtFibreGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_integral_at_fibre_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k) (x ζ : G.left), G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → IntAt L α s ζ → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_intAt_fibreGeneric | exact GlobalTheory.Mum.intAt_of_intAt_fibreGeneric | (intros; apply GlobalTheory.Mum.intAt_of_intAt_fibreGeneric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_setOf_intAt {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) {k : ℕ} (s : SecK L α k) :
    IsOpen {x : X | IntAt L α s x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨j, W, hW, hx, hWa, hint⟩
  exact ⟨W, fun x' hx' => ⟨j, W, hW, hx', hWa, hint⟩, W.isOpen, hx⟩

theorem exists_fibre_generic {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyIrreducible f] (y : S) :
    ∃ ζ : X, f ζ = y ∧ ∀ z, f z = y → ζ ⤳ z := by
  refine ⟨f.fiberι y (genericPoint (f.fiber y)), ?_, ?_⟩
  · have : f.fiberι y (genericPoint (f.fiber y)) ∈ Set.range (f.fiberι y) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range (f.fiberι y) := by rw [Scheme.Hom.range_fiberι]; exact hz
    exact (genericPoint_specializes z').map (f.fiberι y).continuous

theorem exists_specializes_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R)
    (y : M.S) : ∃ y₀, y ⤳ y₀ ∧ M.π y₀ = closedPoint R := by
  haveI := M.proper
  have hc : IsClosed (M.π '' closure {y}) := M.π.isClosedMap _ isClosed_closure
  have hm : M.π y ∈ M.π '' closure {y} := ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (M.π y)).mem_closed hc hm
  exact ⟨y₀, specializes_iff_mem_closure.2 hy₀, e⟩

end GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hcl x
  haveI := hsm; haveI := hgi
  by_contra hx
  obtain ⟨ζ, hζ, hζg⟩ := exists_fibre_generic G.hom (G.hom x)
  obtain ⟨y₀, hy₀, hy₀c⟩ := exists_specializes_closedPoint M (G.hom ζ)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, G.hom g₀ = y₀ := by
    obtain ⟨g₀, hg₀, -⟩ := exists_fibre_generic G.hom y₀
    exact ⟨g₀, hg₀⟩
  obtain ⟨g, hg, hgg₀⟩ := Flat.generalizingMap G.hom (show G.hom ζ ⤳ G.hom g₀ from hg₀ ▸ hy₀)
  have hζg' : ζ ⤳ g := hζg g (hgg₀.trans hζ)
  have hnζ : ¬ IntAt L α s ζ := fun h => hx (GlobalTheory.T.integral_of_integral_at_fibre_generic_point R M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hζg h)
  have hclosed : IsClosed {z : G.left | ¬ IntAt L α s z} := (isOpen_setOf_intAt L α s).isClosed_compl
  have : ¬ IntAt L α s g₀ := (hζg'.trans hg).mem_closed hclosed hnζ
  exact this (hcl g₀ (by rw [hg₀, hy₀c]))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_closedFibre | exact GlobalTheory.Mum.intAt_of_closedFibre | (intros; apply GlobalTheory.Mum.intAt_of_closedFibre <;> assumption)
end
