module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapMulIdealSheaf
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Principalise

theorem comap_mul_idealSheaf : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (I J : X.IdealSheafData),
    (I * J).comap f = I.comap f * J.comap f := by
  intro X X' f I J
  have h : ∀ y : X', ∃ (U : X.affineOpens) (A : X'.affineOpens), y ∈ A.1 ∧ A.1 ≤ f ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ f ⁻¹ᵁ U from hyU) (f ⁻¹ᵁ U).isOpen
    exact ⟨⟨U, hU⟩, ⟨A, hA⟩, hyA, hAU⟩
  choose U A hyA hAU using h
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, comapIdealAffine _ f (U y) (A y) (hAU y),
      comapIdealAffine _ f (U y) (A y) (hAU y), comapIdealAffine _ f (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

end GlobalTheory.Principalise
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapInfSupPowEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrict
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.MapComapIso

theorem map_eq_comap_inv {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (K : X.IdealSheafData) :
    K.map f = K.comap (inv f) := by
  apply le_antisymm
  · calc K.map f = (K.map f).comap (inv f ≫ f) := by simp
      _ = ((K.map f).comap f).comap (inv f) := by rw [Scheme.IdealSheafData.comap_comp]
      _ ≤ K.comap (inv f) :=
          Scheme.IdealSheafData.comap_mono (inv f) ((Scheme.IdealSheafData.map_gc f).l_u_le K)
  · calc K.comap (inv f) ≤ ((K.comap (inv f)).comap f).map f :=
          (Scheme.IdealSheafData.map_gc f).le_u_l _
      _ = (K.comap (f ≫ inv f)).map f := by rw [Scheme.IdealSheafData.comap_comp]
      _ = K.map f := by simp

theorem map_comap_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    (I.comap f).map f = I := by
  rw [map_eq_comap_inv, ← Scheme.IdealSheafData.comap_comp]
  simp

theorem map_comap_ideal_eq_of_isIso_restrict :
    ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) →
      ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U →
        ((τ.comap π).map π).ideal V = τ.ideal V := by
  intro W W' π U hq hiso τ V hVU
  have hpb := (isPullback_morphismRestrict π U).flip
  have hres : ((τ.comap π).map π).comap U.ι = τ.comap U.ι := by
    rw [GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' U (π ⁻¹ᵁ U) π U.ι (π ⁻¹ᵁ U).ι (π ∣_ U) hpb inferInstance hq (τ.comap π),
      ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp,
      map_comap_of_isIso]
  have hle : V.1 ≤ Scheme.Hom.opensRange U.ι := by rw [Scheme.Opens.opensRange_ι]; exact hVU
  let V' : U.toScheme.affineOpens := ⟨U.ι ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion U.ι hle⟩
  have himg : (⟨U.ι ''ᵁ V'.1, (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).2 V'.2⟩ :
      W.affineOpens) = V := by
    apply Subtype.ext
    change U.ι ''ᵁ U.ι ⁻¹ᵁ V.1 = V.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion ((τ.comap π).map π) U.ι V'
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion τ U.ι V'
  rw [hres, h2] at h1
  have h3 := Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso U.ι V'.1).inv).2 h1
  have h4 : ∀ A B : W.affineOpens, A = B →
      ((τ.comap π).map π).ideal A = τ.ideal A → ((τ.comap π).map π).ideal B = τ.ideal B := by
    rintro A B rfl h; exact h
  exact h4 _ V himg h3.symm

end GlobalTheory.MapComapIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrictStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict : ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U → ((τ.comap π).map π).ideal V = τ.ideal V := by
  first | exact @GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | exact GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | (intros; apply GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSupPowEqOfTorsionArtinRees
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSupPowEqOfTorsionArtinRees
namespace GlobalTheory

theorem inf_sup_pow_eq_of_torsion : ∀ (B : Type) [CommRing B] [IsNoetherianRing B]
    (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  intro B _ _ K τ τ' hle htor
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian τ' : τ'.FG)
  have hrad : K ≤ (τ.colon (s : Set B)).radical := by
    intro f hf
    have hm : ∀ b ∈ s, ∃ m : ℕ, f ^ m * b ∈ τ := fun b hb =>
      htor b (hs ▸ Submodule.subset_span hb) f hf
    choose! m hm using hm
    refine ⟨∑ b ∈ s, m b, ?_⟩
    rw [Submodule.mem_colon]
    intro b hb
    have hb' : b ∈ s := hb
    have hle' : m b ≤ ∑ b ∈ s, m b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb'
    rw [smul_eq_mul, ← Nat.sub_add_cancel hle', pow_add, mul_assoc]
    exact τ.mul_mem_left _ (hm b hb')
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian K)
  have hKm : K ^ m * τ' ≤ τ := by
    rw [Ideal.mul_le]
    intro r hr t ht
    have hr' := Submodule.mem_colon.mp (hm hr)
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem x hx => simpa [smul_eq_mul] using hr' x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact τ.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact τ.mul_mem_left a hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul K (M := B) (τ' : Submodule B B)
  refine ⟨c + m, fun k hk => ?_⟩
  have hAR : K ^ k ⊓ τ' ≤ τ := by
    have h := hc k (by omega)
    simp only [smul_eq_mul, Ideal.mul_top] at h
    rw [h]
    calc K ^ (k - c) * (K ^ c ⊓ τ') ≤ K ^ (k - c) * τ' := Ideal.mul_mono_right inf_le_right
      _ ≤ K ^ m * τ' := Ideal.mul_mono_left (Ideal.pow_le_pow_right (by omega))
      _ ≤ τ := hKm
  apply le_antisymm
  · rw [inf_comm, sup_inf_assoc_of_le _ hle]
    exact sup_le le_rfl hAR
  · exact le_inf hle le_sup_left

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSupPowEqOfTorsionArtinReesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  first | exact @GlobalTheory.inf_sup_pow_eq_of_torsion | exact GlobalTheory.inf_sup_pow_eq_of_torsion | (intros; apply GlobalTheory.inf_sup_pow_eq_of_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapInfSupPowEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W)
    (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData),
    (∀ x, x ∉ K.support → x ∈ U) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  intro W W' _ _ π U hqc hiso K τ hK
  let T : W.affineOpens := ⟨⊤, isAffineOpen_top W⟩
  haveI : IsNoetherianRing Γ(W, T.1) := IsLocallyNoetherian.component_noetherian T
  have hle : τ ≤ (τ.comap π).map π := Scheme.IdealSheafData.le_map_comap τ π
  have htor : ∀ b ∈ ((τ.comap π).map π).ideal T, ∀ f ∈ K.ideal T, ∃ m : ℕ, f ^ m * b ∈ τ.ideal T := by
    intro b hb f hf
    have hV : (W.affineBasicOpen f).1 ≤ U := by
      intro x hx
      by_contra hxU
      have hxK : x ∈ K.support := by_contra fun h => hxU (hK x h)
      rw [Scheme.IdealSheafData.mem_support_iff] at hxK
      exact (Scheme.mem_zeroLocus_iff W _ x).1 (hxK T) f hf hx
    have heq := GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict W W' π U hqc hiso τ (W.affineBasicOpen f) hV
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, ← Scheme.IdealSheafData.map_ideal_basicOpen] at heq
    have hloc := T.2.isLocalization_basicOpen f
    have hb' := Ideal.mem_map_of_mem (W.presheaf.map (homOfLE (W.basicOpen_le f)).op).hom hb
    rw [heq] at hb'
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) Γ(W, W.basicOpen f)
        (τ.ideal T) b).1 hb'
    exact ⟨m, hm⟩
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees Γ(W, T.1) (K.ideal T) (τ.ideal T) (((τ.comap π).map π).ideal T)
    (hle T) htor
  refine ⟨k₀, fun k hk => Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapInfSupPowEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  first | exact @GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq | exact GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq | (intros; apply GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInduction
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem eq_of_sup_baseIdeal_pow_eq {C : Type} [CommRing C] [IsNoetherianRing C] {J : Ideal C}
    (hJ : J ≤ Ideal.jacobson ⊥) {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of C)) [IsProper p]
    (a a' : V.IdealSheafData)
    (h : ∀ e : ℕ, a ⊔ baseIdeal p (J ^ (e + 1)) = a' ⊔ baseIdeal p (J ^ (e + 1))) : a = a' := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  refine le_antisymm ?_ ?_
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a a' inferInstance fun e => (h e) ▸ le_sup_left
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a' a inferInstance fun e => (h e).symm ▸ le_sup_left

theorem map_inf_eq_of_reductions : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  intro C _ _ J hJ W' π U hπ hU K τ hK
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.exists_map_comap_inf_sup_pow_eq (Spec (CommRingCat.of C)) W' π U inferInstance hU K τ hK
  refine ⟨k₀, fun k hk T' T'' h' h'' => ?_⟩
  have e' : T' = τ.comap π := by
    refine eq_of_sup_baseIdeal_pow_eq hJ π _ _ fun e => ?_
    rw [h' e, Scheme.IdealSheafData.comap_sup, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, Category.comp_id]
  have e'' : T'' = τ ⊔ K ^ k := by
    refine eq_of_sup_baseIdeal_pow_eq hJ (𝟙 _) _ _ fun e => ?_
    rw [h'' e, sup_right_comm]
  rw [e', e'']
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInductionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  first | exact @GlobalTheory.FormalAlg.map_inf_eq_of_reductions | exact GlobalTheory.FormalAlg.map_inf_eq_of_reductions | (intros; apply GlobalTheory.FormalAlg.map_inf_eq_of_reductions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem baseIdeal_sup {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (a b : Ideal R) : baseIdeal f (a ⊔ b) = baseIdeal f a ⊔ baseIdeal f b := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, baseIdeal_ideal, baseIdeal_ideal,
    Ideal.map_sup]

theorem idealSheaf_ext_top {X : Scheme.{0}} [IsAffine X] {I J : X.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Unit) (fun _ => ⟨⊤, isAffineOpen_top X⟩) iSup_const fun _ => h

theorem appLE_specMap_fromSpec {W : Scheme.{0}} (U : W.Opens) (hU : IsAffineOpen U) (C : Type) [CommRing C]
    (φ : Γ(W, U) →+* C) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U) :
    ((Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h).hom =
      (cst (𝟙 (Spec (CommRingCat.of C))) ⊤).comp φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have m1 : (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(W, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(W, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(W, U)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [m1, m2, m3]
  ext x
  simp only [cst, RingHom.comp_apply, rs_self]
  rfl

theorem specIdeal :
    (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  refine ⟨fun C _ => ⟨⟨fun a b hab => ?_, fun J => ?_⟩, fun a b => baseIdeal_sup _ a b⟩, fun W V C _ φ J => ?_⟩
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    have e := congrArg (fun I : (Spec (CommRingCat.of C)).IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩) hab
    simp only [baseIdeal_ideal] at e
    rw [← Ideal.comap_map_of_bijective _ hb (I := a), e, Ideal.comap_map_of_bijective _ hb]
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    refine ⟨(J.ideal ⟨⊤, isAffineOpen_top _⟩).comap (cst (𝟙 (Spec (CommRingCat.of C))) ⊤), idealSheaf_ext_top ?_⟩
    simp only [baseIdeal_ideal]
    exact Ideal.map_comap_of_surjective _ hb.2 _
  · have h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ V.1 :=
      fun x _ => V.2.range_fromSpec.subset ⟨_, rfl⟩
    refine idealSheaf_ext_top ?_
    rw [GlobalTheory.Principalise.comapIdealAffine J _ V ⟨⊤, isAffineOpen_top _⟩ h, baseIdeal_ideal, Ideal.map_map,
      appLE_specMap_fromSpec V.1 V.2 C φ h]

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculusStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus : (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  first | exact @GlobalTheory.FormalAlg.specIdeal | exact GlobalTheory.FormalAlg.specIdeal | (intros; apply GlobalTheory.FormalAlg.specIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapInfOfFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapInfOfFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FlatInf
open TensorProduct

theorem map_eq_baseChange {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (K : Ideal R) :
    Ideal.map (algebraMap R S) K =
      (K.baseChange S).map ((Algebra.TensorProduct.rid R S S).toLinearEquiv : S ⊗[R] R →ₗ[S] S) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Ideal.map]
  congr 1
  ext y
  simp [Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem map_inf_of_flat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (I J : Ideal R) : Ideal.map f (I ⊓ J) = Ideal.map f I ⊓ Ideal.map f J := by
  letI := f.toAlgebra
  haveI : Module.Flat R S := hf
  have e : f = algebraMap R S := rfl
  rw [e, map_eq_baseChange, map_eq_baseChange, map_eq_baseChange, GlobalTheory.baseChange_inf,
    Submodule.map_inf _ (Algebra.TensorProduct.rid R S S).toLinearEquiv.injective]

end GlobalTheory.FlatInf

namespace GlobalTheory.FlatInf

theorem comap_inf_of_flat : ∀ (W V : Scheme.{0}) (g : V ⟶ W), Flat g →
    ∀ a b : W.IdealSheafData, (a ⊓ b).comap g = a.comap g ⊓ b.comap g := by
  intro W V g hg a b
  haveI := hg
  have hU : ∀ y : V, ∃ U : W.affineOpens, g y ∈ U.1 := fun y => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show g y ∈ ((⊤ : W.Opens) : Set W) from trivial) (⊤ : W.Opens).isOpen
    exact ⟨⟨U, hU⟩, hyU⟩
  choose U hyU using hU
  have hA : ∀ y : V, ∃ A : V.affineOpens, y ∈ A.1 ∧ A.1 ≤ g ⁻¹ᵁ (U y).1 := fun y => by
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAle⟩ := V.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ ((g ⁻¹ᵁ (U y).1 : V.Opens) : Set V) from hyU y) (g ⁻¹ᵁ (U y).1).isOpen
    exact ⟨⟨A, hA⟩, hyA, hAle⟩
  choose A hyA hAU using hA
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply,
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
    exact map_inf_of_flat _ (g.flat_appLE (U y).2 (A y).2 (hAU y)) _ _

end GlobalTheory.FlatInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapInfOfFlatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_comap_inf_of_flat : ∀ (W V : Scheme.{0}) (g : V ⟶ W), Flat g → ∀ a b : W.IdealSheafData, (a ⊓ b).comap g = a.comap g ⊓ b.comap g := by
  first | exact @GlobalTheory.FlatInf.comap_inf_of_flat | exact GlobalTheory.FlatInf.comap_inf_of_flat | (intros; apply GlobalTheory.FlatInf.comap_inf_of_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicCompletionNoetherianFlatComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicCompletionNoetherianFlatComplete
namespace GlobalTheory.AdicPackage

theorem adicCompletion_package : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B),
    ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧
      IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  intro B _ _ I
  have fg : I.FG := IsNoetherian.noetherian I
  refine ⟨AdicCompletion I B, inferInstance, algebraMap B (AdicCompletion I B),
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I),
    AdicCompletion.isAdicComplete_self I fg, ?_⟩
  intro m a h
  refine le_antisymm ?_ Ideal.le_comap_map
  have key : ∀ y : B, (AdicCompletion.evalₐ I m) (algebraMap B (AdicCompletion I B) y) =
      Ideal.Quotient.mk (I ^ m) y := fun y => (AdicCompletion.evalₐ I m).commutes y
  have hle : a.map (algebraMap B (AdicCompletion I B)) ≤
      (a.map (Ideal.Quotient.mk (I ^ m))).comap (AdicCompletion.evalₐ I m) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [key]
    exact Ideal.mem_map_of_mem _ hy
  intro x hx
  rw [Ideal.mem_comap] at hx
  have h2 := hle hx
  rw [Ideal.mem_comap, key] at h2
  exact (Ideal.mem_quotient_iff_mem h).1 h2

end GlobalTheory.AdicPackage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicCompletionNoetherianFlatCompleteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B), ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧ IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  first | exact @GlobalTheory.AdicPackage.adicCompletion_package | exact GlobalTheory.AdicPackage.adicCompletion_package | (intros; apply GlobalTheory.AdicPackage.adicCompletion_package <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEqOfAdicCompatibleIdeals
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEq
namespace GlobalTheory.InfimumSupPowerIdeal

theorem iInf_sup_pow_eq (C : Type) [CommRing C] (J : Ideal C) (hJ : IsAdicComplete J C)
    (u : ℕ → Ideal C) (hu : ∀ e : ℕ, u e = u (e + 1) ⊔ J ^ (e + 1)) (e : ℕ) :
    (⨅ l : ℕ, u l) ⊔ J ^ (e + 1) = u e := by

  have hsm : ∀ m : ℕ, (J ^ m • ⊤ : Submodule C C) = J ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]

  have hanti : Antitone u := antitone_nat_of_succ_le fun k => by
    rw [hu k]; exact le_sup_left
  have hJle : ∀ k, J ^ (k + 1) ≤ u k := fun k => by
    rw [hu k]; exact le_sup_right
  apply le_antisymm
  · exact sup_le (iInf_le u e) (hJle e)
  · intro x hx

    have step : ∀ (k : ℕ) (a : u k), ∃ b : u (k + 1), (a : C) - b ∈ J ^ (k + 1) := by
      intro k a
      have ha : (a : C) ∈ u (k + 1) ⊔ J ^ (k + 1) := by rw [← hu k]; exact a.2
      obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 ha
      refine ⟨⟨b, hb⟩, ?_⟩
      have : (a : C) - b = c := by rw [← hbc]; ring
      rw [this]; exact hc
    choose g hg using step
    let s : ∀ n : ℕ, u (e + n) := fun n =>
      Nat.rec (motive := fun n => ↥(u (e + n))) ⟨x, hx⟩ (fun n a => g (e + n) a) n
    have hs0 : (s 0 : C) = x := rfl
    have hss : ∀ n, (s n : C) - s (n + 1) ∈ J ^ (e + n + 1) := fun n => hg (e + n) (s n)
    have hchain : ∀ m n, m ≤ n → (s m : C) - s n ∈ J ^ (e + m + 1) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have h1 : (s n : C) - s (n + 1) ∈ J ^ (e + m + 1) :=
          Ideal.pow_le_pow_right (by omega) (hss n)
        have hsum : (s m : C) - s (n + 1) = ((s m : C) - s n) + ((s n : C) - s (n + 1)) := by ring
        rw [hsum]; exact add_mem ih h1

    obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ.toIsPrecomplete (f := fun n => (s n : C)) (by
      intro m n hmn
      rw [hsm, SModEq.sub_mem]
      exact Ideal.pow_le_pow_right (by omega) (hchain m n hmn))
    have hL' : ∀ n, (s n : C) - L ∈ J ^ n := fun n => by
      have h := hL n
      rw [hsm, SModEq.sub_mem] at h
      exact h

    have hLu : L ∈ ⨅ l, u l := by
      rw [Submodule.mem_iInf]
      intro l
      have h1 : (s (l + 1) : C) ∈ u l := hanti (by omega : l ≤ e + (l + 1)) (s (l + 1)).2
      have h2 : (s (l + 1) : C) - L ∈ u l := hJle l (hL' (l + 1))
      have h3 := Submodule.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at h3

    have hxL : x - L ∈ J ^ (e + 1) := by
      have h1 : (s 0 : C) - s (e + 1) ∈ J ^ (e + 1) := by simpa using hchain 0 (e + 1) (by omega)
      have hsum : x - L = ((s 0 : C) - s (e + 1)) + ((s (e + 1) : C) - L) := by rw [hs0]; ring
      rw [hsum]; exact add_mem h1 (hL' (e + 1))
    exact Submodule.mem_sup.2 ⟨L, hLu, x - L, hxL, by ring⟩

end GlobalTheory.InfimumSupPowerIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEqOfAdicCompatibleIdeals
namespace GlobalTheory

theorem iInf_sup_pow_eq_of_compatible :
    ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C,
      (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first
  | exact @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
  | (apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEqOfAdicCompatibleIdealsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals : ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C, (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first | exact @GlobalTheory.iInf_sup_pow_eq_of_compatible | exact GlobalTheory.iInf_sup_pow_eq_of_compatible | (intros; apply GlobalTheory.iInf_sup_pow_eq_of_compatible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg

theorem affineFromSpec_comp_eq_specMap_cst {R : Type} [CommRing R] {W : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    V.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (cst f V.1)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) V.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem comap_idealSheaf_pow_eq {X Y : Scheme.{0}} (g : Y ⟶ X) (K : X.IdealSheafData) (k : ℕ) :
    (K ^ k).comap g = (K.comap g) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Scheme.IdealSheafData.comap_top g
  | succ n ih =>
    rw [pow_succ, pow_succ, GlobalTheory.Principalise.comap_mul_idealSheaf, ih]

theorem isIso_pullbackSnd_restrict_preimage {X Y S : Scheme.{0}} (π : X ⟶ S) (g : Y ⟶ S) (U : S.Opens)
    (h : IsIso (π ∣_ U)) : IsIso (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) := by
  have hEq : pullback.fst π g ⁻¹ᵁ π ⁻¹ᵁ U = pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U := by
    show (pullback.fst π g ≫ π) ⁻¹ᵁ U = (pullback.snd π g ≫ g) ⁻¹ᵁ U
    rw [pullback.condition]
  have L : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U).ι (π ⁻¹ᵁ U).ι (pullback.fst π g) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by simpa only [Scheme.Opens.opensRange_ι] using hEq)
  have s := L.paste_vert (IsPullback.of_hasPullback π g)
  have key : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) (π ∣_ U) (g ∣_ U) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict g U)
    · rw [morphismRestrict_ι, morphismRestrict_ι]
      exact s
    · rw [← cancel_mono U.ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
        Scheme.Hom.resLE_comp_ι_assoc, pullback.condition]
  exact key.isIso_snd_of_isIso h

theorem ideal_eq_of_reduces_affine : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t →
    ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) →
    ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  intro R _ I W W' _ f π U hπ hU K hK t ht V
  obtain ⟨hbc, hbs, -⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support
  obtain ⟨hbC, hloc⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus
  haveI : IsNoetherianRing Γ(W, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨C, _, φ, hCn, hφ, hC, hfaith⟩ := GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete Γ(W, V.1) (I.map (cst f V.1))
  haveI := hCn
  haveI := hπ
  have hJjac : (I.map (cst f V.1)).map φ ≤ Ideal.jacobson ⊥ := by
    haveI := hC
    exact IsAdicComplete.le_jacobson_bot _
  haveI hφF : Flat (Spec.map (CommRingCat.ofHom φ)) := AlgebraicGeometry.Flat.SpecMap_iff.mpr hφ
  have hOF : Flat V.2.fromSpec :=
    @HasRingHomProperty.of_isOpenImmersion @Flat RingHom.Flat _ _ _ _ RingHom.Flat.containsIdentities
      V.2.isOpenImmersion_fromSpec
  have hgF : Flat (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) :=
    MorphismProperty.comp_mem @Flat _ _ hφF hOF
  have F1 : ∀ X : W.IdealSheafData, X.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((X.ideal V).map φ) := fun X => hloc W V C φ X
  have F2 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).ideal V = (I.map (cst f V.1)) ^ (e + 1) := by
    intro e
    rw [baseIdeal_ideal, Ideal.map_pow]
  have F4 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, F2, Ideal.map_pow]
  have F5 : ∀ e : ℕ, ((t e).ideal V).map φ = ((t (e + 1)).ideal V).map φ ⊔ ((I.map (cst f V.1)).map φ) ^ (e + 1) := by
    intro e
    conv_lhs => rw [ht e]
    rw [← Ideal.map_pow, ← F2 e, ← Ideal.map_sup]
    rfl
  have F6 := GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals C ((I.map (cst f V.1)).map φ) hC (fun e => ((t e).ideal V).map φ) F5
  have F7 : ∀ e : ℕ, (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, ← (hbC C).2, F6 e]
  have F8 : ∀ e : ℕ, (baseIdeal (π ≫ f) (I ^ (e + 1))).comap
      (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) =
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    have hgf : (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ≫ f =
        Spec.map (CommRingCat.ofHom (φ.comp (cst f V.1))) := by
      rw [Category.assoc, affineFromSpec_comp_eq_specMap_cst, ← Spec.map_comp]
      rfl
    rw [hbc, ← Category.assoc, pullback.condition, Category.assoc, hgf, hbs, ← Ideal.map_map,
      Ideal.map_pow, Ideal.map_pow]
  have hKC : ∀ x, x ∉ (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)).support →
      x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U := by
    intro x hx
    refine hK _ (fun h => hx ?_)
    rw [Scheme.IdealSheafData.support_comap]
    exact h
  have hπC : IsProper (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := inferInstance
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction C ((I.map (cst f V.1)).map φ) hJjac _
    (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) _ hπC
    (isIso_pullbackSnd_restrict_preimage π _ U hU) _
    (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ)) hKC
  refine ⟨k₀, fun k hk T' T'' hT' hT'' e => ?_⟩
  have h1 : ∀ e : ℕ, T'.comap (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ⊔
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1))).comap
        (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := by
    intro e
    have hT'e : T' ⊔ baseIdeal (π ≫ f) (I ^ (e + 1)) = (t e).comap π := hT' e
    rw [← F8 e, ← Scheme.IdealSheafData.comap_sup, hT'e, ← F7 e,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, pullback.condition]
  have h2 : ∀ e : ℕ, T''.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⊔
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) ⊔
        (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ^ k := by
    intro e
    have hT''e : T'' ⊔ baseIdeal f (I ^ (e + 1)) = t e ⊔ K ^ k := hT'' e
    rw [← F4 e, ← Scheme.IdealSheafData.comap_sup, hT''e, Scheme.IdealSheafData.comap_sup, F7 e,
      comap_idealSheaf_pow_eq, F4 e]
  have hmain := hk₀ k hk _ _ h1 h2
  have hX : ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).comap
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) := by
    rw [Scheme.IdealSheafData.comap_sup, GlobalTheory.T.idealSheafData_comap_inf_of_flat _ _ _ hgF,
      GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' _ _ π _ (pullback.fst π _) (pullback.snd π _) (IsPullback.of_hasPullback π _) hgF
        inferInstance, hmain, F4 e, F7 e]
  rw [F1, F1] at hX
  have hX' := (hbC C).1.1 hX
  have hle1 : (I.map (cst f V.1)) ^ (e + 1) ≤ ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp le_sup_right V
  have hle2 : (I.map (cst f V.1)) ^ (e + 1) ≤ (t e).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp (ht.baseIdeal_le e) V
  calc ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V
      = ((((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V).map φ).comap φ := (hfaith _ _ hle1).symm
    _ = ((((t e).ideal V)).map φ).comap φ := by rw [hX']
    _ = (t e).ideal V := hfaith _ _ hle2

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_eq_of_reduction_agree_on_affineOpen : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W] (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) → ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  first | exact @GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | exact GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | (intros; apply GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubscheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I →
    ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  intro R _ I W f a hA t ht hp
  set ι := a.subschemeι with hι
  have hbase : ∀ J : Ideal R, (baseIdeal f J).comap ι = baseIdeal (ι ≫ f) J :=
    fun J => GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1 R W a.subscheme f ι J
  have hms := GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion a.subscheme W ι inferInstance
  let s : ℕ → a.subscheme.IdealSheafData := fun e => (t e).comap ι
  have hs : IsSystem (ι ≫ f) I s := fun e => by
    simp only [s]
    rw [ht e, Scheme.IdealSheafData.comap_sup, hbase]
  have hsp : ∀ e, IsProper ((s e).subschemeι ≫ ι ≫ f) := fun e => by
    have H : t e ≤ (s e).map ι := Scheme.IdealSheafData.le_map_comap _ _
    rw [← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι (s e) (t e) ι H,
      Category.assoc]
    haveI := hp e
    haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H) := by
      haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H ≫
          (t e).subschemeι) := by
        rw [Scheme.IdealSheafData.subschemeMap_subschemeι]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion _ (t e).subschemeι
    infer_instance
  obtain ⟨T₀, hT₀p, hT₀r⟩ := hA s hs hsp
  refine ⟨T₀.map ι, ?_, fun e => ?_⟩
  · let g := T₀.subschemeι ≫ ι
    have hk : (T₀.map ι).subschemeι.ker = g.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; rfl
    haveI := IsClosedImmersion.isIso_lift _ _ hk
    have hfac : (T₀.map ι).subschemeι =
        inv (IsClosedImmersion.lift (T₀.map ι).subschemeι g hk.le) ≫ g := by
      rw [IsIso.eq_inv_comp, IsClosedImmersion.lift_fac]
    rw [hfac, Category.assoc]
    haveI : IsProper (g ≫ f) := by simpa [g, Category.assoc] using hT₀p
    infer_instance
  · calc T₀.map ι ⊔ baseIdeal f (I ^ (e + 1))
        = (T₀ ⊔ (baseIdeal f (I ^ (e + 1))).comap ι).map ι := (hms T₀ _).1.symm
      _ = (s e).map ι := by rw [hbase, hT₀r e]
      _ = ((⊥ : a.subscheme.IdealSheafData) ⊔ (t e).comap ι).map ι := by rw [bot_sup_eq]
      _ = t e ⊔ a := by
        rw [(hms ⊥ (t e)).1, Scheme.IdealSheafData.map_bot, hι,
          Scheme.IdealSheafData.ker_subschemeι, sup_comm]

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubschemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraise_system_in_algebraising_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) → ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  first | exact @GlobalTheory.FormalAlg.alg_of_closedSubscheme | exact GlobalTheory.FormalAlg.alg_of_closedSubscheme | (intros; apply GlobalTheory.FormalAlg.alg_of_closedSubscheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImage
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem universallyClosed_of_jointly_surjective {A₁ A₂ X Z : Scheme.{0}} (g₁ : A₁ ⟶ X)
    (g₂ : A₂ ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x)
    (h₁ : UniversallyClosed (g₁ ≫ k)) (h₂ : UniversallyClosed (g₂ ≫ k)) :
    UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c₁ := h₁.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₁).paste_horiz H)
  have c₂ := h₂.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₂).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = (pullback.fst i₁ g₁ ≫ f') '' (pullback.fst i₁ g₁ ⁻¹' Zs) ∪
      (pullback.fst i₁ g₂ ≫ f') '' (pullback.fst i₁ g₂ ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov (i₁ x) with ⟨a, ha⟩ | ⟨a, ha⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact ⟨_, hz, by simp⟩
  rw [e]
  exact (c₁ _ (hZ.preimage (Scheme.Hom.continuous _))).union
    (c₂ _ (hZ.preimage (Scheme.Hom.continuous _)))

end GlobalTheory

namespace GlobalTheory

theorem isProper_map_inf_subschemeι : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W),
    IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) →
    IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  intro S W W' f π hsep hlft T' T'' h₁ h₂
  have hle₁ : T'.map π ⊓ T'' ≤ T'.map π := inf_le_left
  have hle₂ : T'.map π ⊓ T'' ≤ T'' := inf_le_right
  let g₁ := Scheme.IdealSheafData.subschemeMap T' (T'.map π ⊓ T'') π hle₁
  let g₂ := Scheme.IdealSheafData.inclusion hle₂
  have e₁ : g₁ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T'.subschemeι ≫ π ≫ f := by simp [g₁]
  have e₂ : g₂ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T''.subschemeι ≫ f := by simp [g₂]
  have huc₀ : UniversallyClosed ((T'.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc]; infer_instance
  have huc : UniversallyClosed (T'.subschemeι ≫ π) :=
    UniversallyClosed.of_comp_of_isSeparated _ f
  have hsupp : ((T'.map π).support : Set W) = Set.range (T'.subschemeι ≫ π) := by
    rw [Scheme.IdealSheafData.map, Scheme.Hom.support_ker]
    exact (T'.subschemeι ≫ π).isClosedMap.isClosed_range.closure_eq
  have hmul : T'.map π * T'' ≤ T'.map π ⊓ T'' := by
    intro U
    exact Ideal.mul_le_inf
  have hcov : ∀ x : (T'.map π ⊓ T'').subscheme, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x := by
    intro x
    have hx : (T'.map π ⊓ T'').subschemeι x ∈ (T'.map π ⊓ T'').support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hx' := Scheme.IdealSheafData.support_antitone hmul hx
    rw [Scheme.IdealSheafData.support_mul] at hx'
    have hinj := (T'.map π ⊓ T'').subschemeι.isClosedEmbedding.injective
    rcases hx' with hx' | hx'
    · rw [hsupp] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inl ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι]
    · rw [← Scheme.IdealSheafData.range_subschemeι] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inr ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
  have huc' : UniversallyClosed ((T'.map π ⊓ T'').subschemeι ≫ f) :=
    universallyClosed_of_jointly_surjective g₁ g₂ _ hcov (e₁ ▸ inferInstance) (e₂ ▸ inferInstance)
  exact { }

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImageStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_inf_ideal_sheaf_image : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W), IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) → IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  first | exact @GlobalTheory.isProper_map_inf_subschemeι | exact GlobalTheory.isProper_map_inf_subschemeι | (intros; apply GlobalTheory.isProper_map_inf_subschemeι <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStep
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_of_modification : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
    QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I →
    (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  intro R _ _ I W f hsep hlft hqc W' π U hπ hiso K hK hA' hAK t ht hp
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f

  have hsys' : IsSystem (π ≫ f) I (fun e => (t e).comap π) := fun e => by
    simp only
    rw [ht e, Scheme.IdealSheafData.comap_sup, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1]
  have hp' : ∀ e, IsProper (((t e).comap π).subschemeι ≫ π ≫ f) := fun e => by
    have h1 : ((t e).comap π).subschemeι ≫ π ≫ f =
        ((t e).comapIso π).hom ≫ pullback.snd π (t e).subschemeι ≫ (t e).subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [h1]
    infer_instance
  obtain ⟨T', hT'p, hT'r⟩ := hA' _ hsys' hp'

  have hcov : ∀ x : W, ∃ V : W.affineOpens, x ∈ (V.1 : Set W) := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : W.affineOpens => (V.1 : Set W))
    (fun V => V.1.2) (fun x _ => Set.mem_iUnion.2 (hcov x))
  choose k₀ hk₀ using GlobalTheory.T.idealSheaf_eq_of_reduction_agree_on_affineOpen R I W W' f π U hπ hiso K hK t ht
  let k := s.sup k₀
  obtain ⟨T'', hT''p, hT''r⟩ := GlobalTheory.T.algebraise_system_in_algebraising_closedSubscheme R I W f (K ^ k) (hAK k) t ht hp
  refine ⟨T'.map π ⊓ T'', GlobalTheory.T.isProper_inf_ideal_sheaf_image _ W W' f π hsep hlft T' T'' (by simpa using hT'p) hT''p, fun e => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := s) (fun V => V.1) ?_ fun V =>
    hk₀ V.1 k (Finset.le_sup V.2) T' T'' hT'r hT''r e
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hx⟩

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStepStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraisation_of_proper_modification_noetherian_step : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I → (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_modification | exact GlobalTheory.FormalAlg.alg_of_modification | (intros; apply GlobalTheory.FormalAlg.alg_of_modification <;> assumption)
end
