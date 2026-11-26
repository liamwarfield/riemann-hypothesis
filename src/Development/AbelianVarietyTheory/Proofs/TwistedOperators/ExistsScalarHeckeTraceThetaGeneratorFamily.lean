module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKerLatticeBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelSumEqCardTorsionMulTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelSumEqCardTorsionMulTrace
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSum

theorem sum_ker_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (p n : ℕ) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (e : Fin n ≃ transKer Xo.univ.t.G Ψ), IsHeckeIsog p (transKer Xo.univ.t.G Ψ) Ψ → IsThGen x' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → (Nat.card {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1} : Z.presheaf.stalk z) * sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (e j).1).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (e j).1).left) z J := by
  intro E _ _ _ H Dw l Xo Ω _ _ x x' Ψ p n s s' β s₁ e hΨ _ hs' hβ hs Z r z J hJ
  have hG := abelianSchemeLaws_all.1.globalFns
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  obtain ⟨β', s₂, n', c, hβ', hs₂, hc, hv⟩ := isThetaTrace_iff.1 hs'
  obtain rfl := hs.unique hG hA hs₂
  have hst : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ≫ Xo.univ.t.act.act H.w0 ∈ transKer Xo.univ.t.G Ψ := by
    intro a ha
    have := Xo.univ.t.act.hom H.w0
    refine (hΨ.2.2.2.1 _).1 ?_
    have h1 : (lift (𝟙 (Over.mk x)) a).left ≫ Ψ =
        (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := (hΨ.2.2.2.1 a).2 ha
    show (lift (𝟙 (Over.mk x)) (a ≫ Xo.univ.t.act.act H.w0)).left ≫ Ψ =
      (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left
    rw [← lift_whiskerLeft, Over.comp_left, Category.assoc, hΨ.2.1.2.2 H.w0, reassoc_of% h1, ← Over.comp_left,
      lift_whiskerLeft, MonObj.one_comp]
  let Φ : (Over.mk x ⟶ Xo.univ.t.G) → Z.presheaf.stalk z := fun b =>
    ((val β (r ≫ (translT Xo.univ.t.G b).left) z J)⁻¹).val *
      sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G b).left) z J
  have hΦ : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ^ p = 1 → ∀ b, Φ (a * b) = Φ b := fun a ha hp b =>
    GlobalTheory.ThetaTransport.term_transl hΨ.2.1 hβ.2.1 hs hst r z hJ a ha hp b
  have h1 : sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ i, Φ (c i) :=
    (hv Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => by
      simp only [Φ]; rw [hβ'.val_unique hG hA hβ _ z hJ])
  have : Finite (transKer Xo.univ.t.G Ψ) := Finite.of_equiv _ e
  letI := Fintype.ofFinite (transKer Xo.univ.t.G Ψ)
  let T := {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1}
  have : Finite T := Finite.of_injective (fun q : T => (⟨q.1, q.2.1⟩ : transKer Xo.univ.t.G Ψ))
    (fun a b h => Subtype.ext (congrArg (fun q : transKer Xo.univ.t.G Ψ => q.1) h))
  letI := Fintype.ofFinite T
  have bij : Function.Bijective fun q : T × Fin n' =>
      (⟨q.1.1 * c q.2, (transKer Xo.univ.t.G Ψ).mul_mem q.1.2.1 (hc.1 _)⟩ : transKer Xo.univ.t.G Ψ) := by
    constructor
    · rintro ⟨a, i⟩ ⟨b, j⟩ h
      have h' : a.1 * c i = b.1 * c j := congrArg Subtype.val h
      obtain rfl : i = j := (hc.2 _ ((transKer Xo.univ.t.G Ψ).mul_mem a.2.1 (hc.1 i))).unique
        (by simpa using a.2.2) (by rw [h']; simpa using b.2.2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
    · intro d
      obtain ⟨i, hi, -⟩ := hc.2 d d.2
      exact ⟨(⟨d * (c i)⁻¹, (transKer Xo.univ.t.G Ψ).mul_mem d.2 ((transKer Xo.univ.t.G Ψ).inv_mem (hc.1 i)), hi⟩, i),
        Subtype.ext (by simp)⟩
  have h2 : ∑ j, Φ (e j).1 = ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 := Equiv.sum_comp e (fun d => Φ d.1)
  have h3 : ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 = ∑ q : T × Fin n', Φ (q.1.1 * c q.2) :=
    (Fintype.sum_bijective _ bij _ _ fun q => rfl).symm
  have h4 : ∑ q : T × Fin n', Φ (q.1.1 * c q.2) = ∑ q : T × Fin n', Φ (c q.2) :=
    Finset.sum_congr rfl fun q _ => hΦ _ q.1.2.1 q.1.2.2 _
  show _ = ∑ j, Φ (e j).1
  rw [h2, h3, h4, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, Nat.card_eq_fintype_card]

end GlobalTheory.KernelSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelSumEqCardTorsionMulTraceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_sum_eq_card_torsion_mul_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (p n : ℕ) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (e : Fin n ≃ transKer Xo.univ.t.G Ψ), IsHeckeIsog p (transKer Xo.univ.t.G Ψ) Ψ → IsThGen x' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → (Nat.card {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1} : Z.presheaf.stalk z) * sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (e j).1).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (e j).1).left) z J := by
  first | exact @GlobalTheory.KernelSum.sum_ker_eq_card_mul | exact GlobalTheory.KernelSum.sum_ker_eq_card_mul | (intros; apply GlobalTheory.KernelSum.sum_ker_eq_card_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedMulPullbackCommutesBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedMulPullbackCommutesBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeExBC

theorem isMulPull_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm p s s' s₁ hc hv h
  obtain ⟨hx, h₁, h₂⟩ := hc
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hx.symm
  have hpm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [h₂, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [h₁, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨s'', hs''⟩ := exists_pullRel Xo.univ.t.PP.L 1 (σ ▷ Xo.univ.t.G) (whiskerRight_snd σ Xo.univ.t.G) s
  have e : s'' = s' := GlobalTheory.ThetaTrace.sec_ext (sec_ext_val (L := Xo.univ.t.PP.L)
    (φ := fun _ : Fin 1 => (snd (Over.mk x₁) Xo.univ.t.G).left) Xo.univ.t.PP.isLB fun z J hJ =>
      (GlobalTheory.ThetaTraceBC.sv_of_pullRel hs'' _ z hJ).trans (by rw [← hpm]; exact (hv _ _ z J hJ).symm))
  subst e
  obtain ⟨s₁', hm, hr⟩ := GlobalTheory.ThetaTraceBC.isMulPull_pull σ hs'' h
  exact ⟨s₁', hm, fun Z r z J hJ => (GlobalTheory.ThetaTraceBC.sv_of_pullRel hr r z hJ).trans (by rw [hpm])⟩

end GlobalTheory.HeckeExBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedMulPullbackCommutesBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_mul_pullback_commutes_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeExBC.isMulPull_baseChange | exact GlobalTheory.HeckeExBC.isMulPull_baseChange | (intros; apply GlobalTheory.HeckeExBC.isMulPull_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRigidifiedThetaIsoBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRigidifiedThetaIsoBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaTraceBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ pm pm' k β hc hc' hΨ h0 hβ
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hc.1.symm
  let σ' : (Over.mk x₁' : Over Xo.X) ⟶ Over.mk x' := Over.homMk (spMap χ) hc'.1.symm
  have epm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc.2.1, ← Over.comp_left, whiskerRight_snd])
  have epm' : pm' = (σ' ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc'.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc'.2.1, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨β₁, h₁, hv⟩ := isRigIso_pull (σ := σ) (σ' := σ') rfl (by rw [← epm, ← epm']; exact hΨ) h0 hβ
  exact ⟨β₁, h₁, fun Z r z J hJ => by rw [hv r z hJ, ← epm]⟩

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRigidifiedThetaIsoBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidified_theta_iso_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeEx.exists_isRigIso_baseChange | exact GlobalTheory.HeckeEx.exists_isRigIso_baseChange | (intros; apply GlobalTheory.HeckeEx.exists_isRigIso_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValuePulledBackAlongGroupMap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValuePulledBackAlongGroupMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx.SvPull

theorem sv_pull_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x₁ : Sp T ⟶ Xo.X} (pm : Gx x₁ ⟶ Gx x) {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)}, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (hi : (PPx x₁).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ hi).hom (s.f i) = s'.f i) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo S T _ _ x x₁ pm s s' hsnd hf Z r z J hJ
  have hi0 : (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) ≤
      pm ⁻¹ᵁ (PPx x).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) := by
    intro y hy
    have h1 := Set.mem_iInter.1 hy 0
    change pm.base y ∈ (⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹'
      (Xo.univ.t.PP.L.U (J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) : Set _))
    refine Set.mem_iInter.2 fun _ => ?_
    simp only [Set.mem_preimage] at h1 ⊢
    rw [← Scheme.Hom.comp_apply, hsnd]
    exact h1
  have hz : r z ∈ (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) :=
    hJ.mem (fun _ : Fin 1 => (snd (Over.mk x₁) Xo.univ.t.G).left) r
  dsimp only [sv]
  rw [sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hsnd])]
  show gs r z ((PPx x₁).U _) (s'.f _) = _
  rw [← hf _ hi0, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res r z hi0 hz,
    gs_pull r pm z _ (hi0 hz)]
  rfl

end GlobalTheory.HeckeEx.SvPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValuePulledBackAlongGroupMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_pulled_back_along_group_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x₁ : Sp T ⟶ Xo.X} (pm : Gx x₁ ⟶ Gx x) {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)}, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (hi : (PPx x₁).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ hi).hom (s.f i) = s'.f i) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeEx.SvPull.sv_pull_eq | exact GlobalTheory.HeckeEx.SvPull.sv_pull_eq | (intros; apply GlobalTheory.HeckeEx.SvPull.sv_pull_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslationCommutesCanonicalBaseChangeMap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslationCommutesCanonicalBaseChangeMap
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem translT_comp_isCan : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm c c₁ h hc
  have hw : pm ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = (Over.mk x₁ ⊗ Xo.univ.t.G).hom := by
    rw [← Over.w (snd (Over.mk x) Xo.univ.t.G), ← Over.w (snd (Over.mk x₁) Xo.univ.t.G), ← Category.assoc, h.2.1]
  let P : Over.mk x₁ ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm hw
  let Φ : Over.mk x₁ ⟶ Over.mk x := Over.homMk (spMap χ) h.1.symm
  have hPf : P ≫ fst (Over.mk x) Xo.univ.t.G = fst (Over.mk x₁) Xo.univ.t.G ≫ Φ :=
    Over.OverMorphism.ext (by simpa [P, Φ] using h.2.2)
  have hPs : P ≫ snd (Over.mk x) Xo.univ.t.G = snd (Over.mk x₁) Xo.univ.t.G :=
    Over.OverMorphism.ext (by simpa [P] using h.2.1)
  have hΦ : Φ ≫ c = c₁ := Over.OverMorphism.ext (by simpa [Φ] using hc.symm)
  have key : translT Xo.univ.t.G c₁ ≫ P = P ≫ translT Xo.univ.t.G c := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hPf, translT, translT, lift_fst, lift_fst_assoc]
      exact hPf.symm
    · rw [Category.assoc, Category.assoc, hPs, translT, translT, lift_snd, lift_snd, translPt, translPt,
        comp_lift_assoc, reassoc_of% hPf, hPs, hΦ]
  have := congrArg CommaMorphism.left key
  simpa [P] using this

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslationCommutesCanonicalBaseChangeMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_commutes_canonical_baseChange_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := by
  first | exact @GlobalTheory.HeckeEx.translT_comp_isCan | exact GlobalTheory.HeckeEx.translT_comp_isCan | (intros; apply GlobalTheory.HeckeEx.translT_comp_isCan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalPointThetaGeneratorNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalPointThetaGeneratorNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNZ

theorem exists_ratPt_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := by
  intro E _ _ _ H Dw l Xo Ω _ _ x₁ s hs
  have hnz := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo Ω x₁ s hs
  obtain ⟨q, i, -, hqi⟩ := hnz (IsLocalRing.closedPoint Ω)
  have := Xo.univ.t.semi.smooth
  have : Smooth (fst (Over.mk x₁) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x₁ Xo.univ.t.G.hom)
    infer_instance
  have : JacobsonSpace ↥(Over.mk x₁).left := inferInstanceAs (JacobsonSpace (PrimeSpectrum Ω))
  have : JacobsonSpace ↥(Gx x₁) := LocallyOfFiniteType.jacobsonSpace (fst (Over.mk x₁) Xo.univ.t.G).left
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints ⟨q, hqi⟩
    ((Gx x₁).basicOpen (s.f i)).isOpen.isLocallyClosed
  have hyc' : IsClosed ({y} : Set (Gx x₁)) := hyc
  refine ⟨pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc',
    pointOfClosedPoint_comp _ y hyc', fun z J hJ => ?_⟩
  set w := pointOfClosedPoint (fst (Over.mk x₁) Xo.univ.t.G).left y hyc'
  have hwz : w z = y := pointOfClosedPoint_apply _ y hyc' z
  let φ : Fin 1 → (Gx x₁ ⟶ Xo.univ.t.G.left) := fun _ => (snd (Over.mk x₁) Xo.univ.t.G).left
  have hi : w z ∈ LB.wchart Xo.univ.t.PP.L φ i := by
    rw [hwz]; exact Scheme.basicOpen_le _ _ hy
  have hj := hJ.mem φ w
  show sval s w z J ≠ 0
  rw [sval_of s w z J (fun k => J (w ≫ φ k)) (fun k => rfl), sec_trans s w z hj hi]
  have hU : IsUnit (gs w z (LB.wchart Xo.univ.t.PP.L φ i) (s.f i)) := by
    have hb : z ∈ (Sp Ω).basicOpen ((w.app _).hom (s.f i)) := by
      rw [← Scheme.preimage_basicOpen]
      show w z ∈ (Gx x₁).basicOpen (s.f i)
      rw [hwz]; exact hy
    convert ((Sp Ω).mem_basicOpen _ z hi).1 hb using 1
    exact gs_eq w z _ hi _
  exact ((Units.isUnit _).mul hU).ne_zero

end GlobalTheory.ThetaNZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalPointThetaGeneratorNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalPoint_thetaGenerator_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := by
  first | exact @GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero | exact GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero | (intros; apply GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChartPulledBackFunctionNeZeroOfValue
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChartPulledBackFunctionNeZeroOfValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem exists_appLE_ne_zero_of_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t₀ z J hJ hne
  refine ⟨fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left), ?_, ?_⟩
  · intro y _
    have hy : y = z := Subsingleton.elim _ _
    subst hy
    exact hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
  · intro hi
    have hz : w z ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) :=
      hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) w
    apply hne
    rw [sv, sval_of t₀ w z J (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) (fun _ => rfl)]
    erw [gs_eq w z _ hz]
    have hle : (⊤ : (Sp Ω).Opens) ≤ w ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
        (fun _ => J (w ≫ (snd (Over.mk x) Xo.univ.t.G).left)) := by
      intro y _
      have hy : y = z := Subsingleton.elim _ _
      subst hy
      exact hz
    rw [← TopCat.Presheaf.germ_res_apply (Sp Ω).presheaf (homOfLE hle) z trivial]
    refine (congrArg ((Sp Ω).presheaf.germ ⊤ z trivial).hom ?_).trans (map_zero _)
    exact hi

end GlobalTheory.HeckeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChartPulledBackFunctionNeZeroOfValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_pulledBack_function_ne_zero_of_value : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := by
  first | exact @GlobalTheory.HeckeEx.exists_appLE_ne_zero_of_sv_ne_zero | exact GlobalTheory.HeckeEx.exists_appLE_ne_zero_of_sv_ne_zero | (intros; apply GlobalTheory.HeckeEx.exists_appLE_ne_zero_of_sv_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKernelOfGeometricFibresReducedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKernelOfGeometricFibresReducedBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem mem_transKer_of_geometric
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G)
    (hΨ : Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hk : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
      IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) :
    a ∈ transKer Xo.univ.t.G Ψ := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.t.semi.separated
  have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x Xo.univ.t.G.hom)
    infer_instance
  have : IsSeparated (fst (Over.mk x') Xo.univ.t.G).left := by
    show IsSeparated (pullback.fst x' Xo.univ.t.G.hom)
    infer_instance
  have : IsReduced (Over.mk x).left := (affine_isReduced_iff _).2 ‹IsReduced T›
  have : IsReduced (Gx x) := GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
  have hT : ∀ {Y : Scheme.{0}} (y : Y ⟶ Xo.X) (c : Over.mk y ⟶ Xo.univ.t.G),
      (translT Xo.univ.t.G c).left ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y) Xo.univ.t.G).left :=
    fun y c => by rw [← Over.comp_left, translT, lift_fst]
  rw [mem_transKer]
  refine hom_ext_of_geometric_points (Gx x) (Gx x') (Sp T) (fst (Over.mk x') Xo.univ.t.G).left _ _
    (by rw [Category.assoc, hΨ, hT]) fun Ω _ _ q => ?_
  let φ : CommRingCat.of T ⟶ CommRingCat.of Ω := Spec.preimage (q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
  let χ : T →+* Ω := φ.hom
  have hχ : spMap χ = q ≫ (fst (Over.mk x) Xo.univ.t.G).left := Spec.map_preimage _
  obtain ⟨Ψ₁, pm, pm', hp, hp', hc, h1⟩ :=
    exists_isFib χ (x₁ := spMap χ ≫ x) (x₁' := spMap χ ≫ x') rfl rfl Ψ hΨ
  obtain ⟨b, hb, hba⟩ := hk Ω χ _ _ Ψ₁ ⟨pm, pm', hp, hp', hc, h1⟩
  let q₁ : Sp Ω ⟶ Gx (spMap χ ≫ x) := ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift (spMap χ ≫ x) (𝟙 _)
    (q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (by rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_w x, ← Category.assoc, ← hχ, Category.id_comp])
  have hq₁ : q₁ ≫ pm = q := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_ext x _ _ ?_ ?_
    · rw [Category.assoc, hp.2.2, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_fst, Category.id_comp, hχ]
    · rw [Category.assoc, hp.2.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_snd]
  let pmO : Over.mk (spMap χ ≫ x) ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm (by
    rw [← Over.w (fst (Over.mk x) Xo.univ.t.G), ← Over.w (fst (Over.mk (spMap χ ≫ x)) Xo.univ.t.G),
      ← Category.assoc, hp.2.2]
    rfl)
  let φo : Over.mk (spMap χ ≫ x) ⟶ Over.mk x := Over.homMk (spMap χ) rfl
  have hb' : b = φo ≫ a := Over.OverMorphism.ext hba
  have hpf : pmO ≫ fst (Over.mk x) Xo.univ.t.G = fst _ Xo.univ.t.G ≫ φo := Over.OverMorphism.ext hp.2.2
  have hps : pmO ≫ snd (Over.mk x) Xo.univ.t.G = snd _ Xo.univ.t.G := Over.OverMorphism.ext hp.2.1
  have tp : ∀ {Y : Over Xo.X} (c : Y ⟶ Xo.univ.t.G),
      translPt Xo.univ.t.G c = (fst Y Xo.univ.t.G ≫ c) * snd Y Xo.univ.t.G := fun _ => rfl
  have key : translT Xo.univ.t.G b ≫ pmO = pmO ≫ translT Xo.univ.t.G a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, translT, lift_fst, lift_fst_assoc, hpf]
    · simp only [Category.assoc, translT, lift_snd, lift_snd_assoc, hps, tp, MonObj.comp_mul, reassoc_of% hpf, hb']
  have keyL : (translT Xo.univ.t.G b).left ≫ pm = pm ≫ (translT Xo.univ.t.G a).left :=
    congrArg (fun f => f.left) key
  rw [← hq₁, Category.assoc, Category.assoc, ← reassoc_of% keyL, ← hc, reassoc_of% (mem_transKer.1 hb)]

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKernelOfGeometricFibresReducedBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_of_geometric_fibres_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G), Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) → a ∈ transKer Xo.univ.t.G Ψ := by
  first | exact @GlobalTheory.HeckeEx.mem_transKer_of_geometric | exact GlobalTheory.HeckeEx.mem_transKer_of_geometric | (intros; apply GlobalTheory.HeckeEx.mem_transKer_of_geometric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PullConstantToPointEqRingImage
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PullConstantToPointEqRingImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullConst

theorem pull_const_apply : ∀ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {Y : Scheme.{0}} (q : Y ⟶ Sp T) (U : Y.Opens) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U), w ≫ q = spMap χ → ∀ a : T, (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  intro T Ω _ _ χ Y q U w h hwq a
  have key : q.appLE ⊤ U le_top ≫ w.appLE U ⊤ h = (w ≫ q).appTop :=
    (Scheme.Hom.appLE_comp_appLE w q ⊤ U ⊤ le_top h).trans
      (Scheme.Hom.appLE_eq_app (f := w ≫ q) (U := ⊤))
  have k1 : (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) =
      (w ≫ q).appTop.hom (toΓ T a) := by
    have := congrArg (fun g => g.hom (toΓ T a)) key
    simpa only [CommRingCat.comp_apply] using this
  refine k1.trans ?_
  rw [hwq]
  have h3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ)
  have h4 := congrArg (fun g => g.hom a) h3
  simp only [CommRingCat.comp_apply] at h4
  exact h4.symm

end GlobalTheory.PullConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PullConstantToPointEqRingImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_constant_to_point_eq_ring_image : ∀ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {Y : Scheme.{0}} (q : Y ⟶ Sp T) (U : Y.Opens) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U), w ≫ q = spMap χ → ∀ a : T, (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  first | exact @GlobalTheory.PullConst.pull_const_apply | exact GlobalTheory.PullConst.pull_const_apply | (intros; apply GlobalTheory.PullConst.pull_const_apply <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PulledBackLocalFunctionEqMulOfValues
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PulledBackLocalFunctionEqMulOfValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx

theorem gs_appLE_top {X Y : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) (hi : ⊤ ≤ w ⁻¹ᵁ U) (z : Y) (a : Γ(X, U)) :
    gs (𝟙 Y) z ⊤ ((w.appLE U ⊤ hi).hom a) = gs w z U a := by
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res (𝟙 Y) z hi trivial,
    gs_pull (𝟙 Y) w z U (hi trivial), Category.id_comp]

theorem appLE_eq_mul_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (α : Ω), (∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t w z J = gs (𝟙 (Sp Ω)) z ⊤ (toΓ Ω α) * sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J) → ∀ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t.f i) = toΓ Ω α * (w.appLE _ ⊤ hi).hom (t₀.f i) := by
  intro E _ _ _ H Dw l Xo T Ω _ _ x k w t t₀ α h i hi
  apply fn_ext
  intro z _
  have hw : w z ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i := hi trivial
  have hc : ∀ a b, (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) a =
      (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) b → i a = i b := fun a b _ =>
    congrArg i (Subsingleton.elim a b)
  obtain ⟨J, hJ, hJi⟩ := exists_good Xo.univ.t.PP.L Xo.univ.t.PP.isLB z
    (fun q => w ≫ (snd (Over.mk x) Xo.univ.t.G).left) i hc (fun q => Set.mem_iInter.1 hw q)
  have e := h z J hJ
  unfold sv at e
  rw [sval_of t w z J i hJi, sval_of t₀ w z J i hJi] at e
  rw [gs_appLE_top, gs_mul (𝟙 (Sp Ω)) z (⊤ : (Sp Ω).Opens) (show (𝟙 (Sp Ω) : Sp Ω ⟶ Sp Ω) z ∈ (⊤ : (Sp Ω).Opens) from trivial),
    gs_appLE_top]
  exact e

end GlobalTheory.HeckeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PulledBackLocalFunctionEqMulOfValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBack_local_function_eq_mul_of_values : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (α : Ω), (∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t w z J = gs (𝟙 (Sp Ω)) z ⊤ (toΓ Ω α) * sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J) → ∀ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t.f i) = toΓ Ω α * (w.appLE _ ⊤ hi).hom (t₀.f i) := by
  first | exact @GlobalTheory.HeckeEx.appLE_eq_mul_of_sv | exact GlobalTheory.HeckeEx.appLE_eq_mul_of_sv | (intros; apply GlobalTheory.HeckeEx.appLE_eq_mul_of_sv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamily
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeScal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem exists_sums {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {p n : ℕ}
    {σ : Fin n → (Over.mk x ⟶ Xo.univ.t.G)} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))}
    (hβ : β.IsGen) (hσ : ∀ j, σ j ∈ transKer Xo.univ.t.G Ψ)
    (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (s₀ : LB.Sec (PPx x')) :
    ∃ t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
        sv Xo.univ.t.G Xo.univ.t.PP t r z J = (val β r z J).val *
          ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (σ j)).left) z J)⁻¹).val *
            sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (σ j)).left) z J ∧
        sv Xo.univ.t.G Xo.univ.t.PP t₀ r z J =
          sv Xo.univ.t.G Xo.univ.t.PP s₀ (r ≫ Ψ) z J * (val β r z J).val := by
  obtain ⟨t₀, ht₀⟩ := exists_isCarried (A := Xo.univ.t.G) (L := Xo.univ.t.PP) hβ s₀
  choose U hc hU using fun j => exists_isDescLift (L := Xo.univ.t.PP) hβ (hσ j)
  choose F hF using fun j => exists_isActOf (U j) s₁
  let t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x)) :=
    SecM.toSec Xo.univ.t.G (∑ j, SecM.ofSec Xo.univ.t.G (F j))
  have ht : ∀ i, t.f i = ∑ j, (F j).f i := fun i => by
    show (∑ j, SecM.ofSec Xo.univ.t.G (F j) : SecM _ _ _ _).1 i = _
    rw [Submodule.coe_sum, Finset.sum_apply]; rfl
  refine ⟨t, t₀, fun Z r z J hJ => ⟨?_, ht₀.val r z hJ⟩⟩
  rw [sv_sum ht r z hJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [act_val (hF j) r z hJ, (hU j).val r z hJ, hc j, Units.val_mul]
  ring

theorem card_tors_mul {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {P : Ideal (𝓞 E)} {p i n : ℕ}
    {C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)} (hp : 0 < p) (hC : Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i C)
    (e : Fin n ≃ C) : Nat.card {a // a ∈ C ∧ a ^ p = 1} * Ideal.absNorm P ^ i = n := by
  haveI : Finite C := Finite.of_equiv _ e
  obtain ⟨k, r, hr⟩ := exists_isRepsModTors C p
  have h1 := hr.card
  have h2 := card_reps hp hC hr
  rw [Nat.card_congr e.symm, Nat.card_fin] at h1
  rw [h1, h2]

theorem card_tors_pos {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {p : ℕ}
    {C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)} [Finite C] : 0 < Nat.card {a // a ∈ C ∧ a ^ p = 1} := by
  haveI : Finite {a // a ∈ C ∧ a ^ p = 1} :=
    Finite.of_injective (fun a => (⟨a.1, a.2.1⟩ : C)) (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)
  exact Nat.card_pos_iff.2 ⟨⟨⟨1, C.one_mem, one_pow p⟩⟩, inferInstance⟩

end GlobalTheory.HeckeScal

namespace GlobalTheory.HeckeScal

theorem rigIso_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := GlobalTheory.T.exists_rigidified_theta_iso_base_change

theorem mulPull_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := GlobalTheory.T.normalized_mul_pullback_commutes_base_change

theorem sv_of_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x₁ : Sp T ⟶ Xo.X} (pm : Gx x₁ ⟶ Gx x) {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)}, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (hi : (PPx x₁).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ hi).hom (s.f i) = s'.f i) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J := GlobalTheory.T.section_value_pulled_back_along_group_map

theorem translT_comp_can : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := GlobalTheory.T.translation_commutes_canonical_baseChange_map

theorem exists_ratPt_sv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := GlobalTheory.T.exists_rationalPoint_thetaGenerator_ne_zero

theorem appLE_eq_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (α : Ω), (∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t w z J = gs (𝟙 (Sp Ω)) z ⊤ (toΓ Ω α) * sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J) → ∀ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t.f i) = toΓ Ω α * (w.appLE _ ⊤ hi).hom (t₀.f i) := GlobalTheory.T.pulledBack_local_function_eq_mul_of_values

theorem appLE_ne_zero_of_sv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [Field Ω] {x : Sp T ⟶ Xo.X} {k : ℤ} (w : Sp Ω ⟶ Gx x) (t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP t₀ w z J ≠ 0 → ∃ (i : (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).ι) (hi : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U i), (w.appLE _ ⊤ hi).hom (t₀.f i) ≠ 0 := GlobalTheory.T.exists_chart_pulledBack_function_ne_zero_of_value

theorem appLE_toΓ : ∀ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {Y : Scheme.{0}} (q : Y ⟶ Sp T) (U : Y.Opens) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U), w ≫ q = spMap χ → ∀ a : T, (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := GlobalTheory.T.pull_constant_to_point_eq_ring_image

end GlobalTheory.HeckeScal

namespace GlobalTheory.HeckeScal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem absNorm_pow_pos {P : Ideal (𝓞 E)} {p i : ℕ} (h : admitted l P p) : 0 < Ideal.absNorm P ^ i := by
  refine pow_pos (Nat.pos_of_ne_zero fun h0 => ?_) _
  rw [Ideal.absNorm_eq_zero_iff] at h0
  have hp := h.2.2.2.1
  rw [h0, Ideal.mem_bot, Nat.cast_eq_zero] at hp
  exact h.2.2.1.ne_zero hp

theorem fibre {c : Coeff l} {P : Ideal (𝓞 E)} {p i n : ℕ} {T : Type} [CommRing T] [Algebra c.F T]
    {y : FrPt Xo c T} {x' : Sp T ⟶ Xo.X} {Ψ : Gx y.x ⟶ Gx x'} {σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)}
    {s₀ : LB.Sec (PPx x')} (hadm : admitted l P p) (hfam : IsHeckeFam P p i Ψ) (hlist : IsListed Ψ σ)
    (hgen : SecGen x' s₀) {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))}
    (hβ : IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β)
    {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x))}
    (hs₁ : IsMulPull Xo.univ.t.G Xo.univ.t.PP p y.s s₁)
    {t t₀ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x))}
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx y.x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
        sv Xo.univ.t.G Xo.univ.t.PP t r z J = (val β r z J).val *
          ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (σ j)).left) z J)⁻¹).val *
            sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (σ j)).left) z J ∧
        sv Xo.univ.t.G Xo.univ.t.PP t₀ r z J =
          sv Xo.univ.t.G Xo.univ.t.PP s₀ (r ≫ Ψ) z J * (val β r z J).val)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω)
    (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')) (hFr : FrMap χ y y₁)
    (hΨ₁ : IsFib χ.toRingHom Ψ Ψ₁) (hth : IsThGen x₁' s')
    (htr : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') :
    n / Ideal.absNorm P ^ i ≠ 0 ∧ ∃ (α' : Ω) (s₀₁ : LB.Sec (PPx x₁')), SecBC χ.toRingHom 1 x' x₁' s₀ s₀₁ ∧
      (∀ j, s'.f j = scal x₁' α' j * s₀₁.f j) ∧
      (∀ w : Sp Ω ⟶ Gx y.x, w ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = spMap χ.toRingHom →
        ∀ j (hj : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).U j),
          (w.appLE _ ⊤ hj).hom (t.f j) =
            toΓ Ω (((n / Ideal.absNorm P ^ i : ℕ) : Ω) * α') * (w.appLE _ ⊤ hj).hom (t₀.f j)) ∧
      ∃ (j : (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).ι) (w : Sp Ω ⟶ Gx y.x) (hj : ⊤ ≤ w ⁻¹ᵁ (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).U j),
        w ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = spMap χ.toRingHom ∧ (w.appLE _ ⊤ hj).hom (t₀.f j) ≠ 0 := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hp : 0 < p := hadm.2.2.1.pos
  obtain ⟨-, -, pm, pms, pmf, pmv⟩ := hFr
  obtain ⟨pm₁, pm', hpm, hpm', hc, hf⟩ := id hΨ₁
  obtain rfl : pm = pm₁ := GlobalTheory.HeckeFrCompare.gx_ext (by rw [pmf, hpm.2.2]) (by rw [pms, hpm.2.1])
  have hsy := sv_of_pull pm pms pmv
  obtain ⟨hker, hisog⟩ := hfam.2.2.2.2 Ω χ.toRingHom y₁.x x₁' Ψ₁ hΨ₁
  obtain ⟨e, he⟩ := hlist Ω χ.toRingHom y₁.x x₁' Ψ₁ hΨ₁
  obtain ⟨β₁, hβ₁, hvβ⟩ := rigIso_baseChange χ.toRingHom hpm hpm' hc hf hβ
  obtain ⟨s₁₁, hs₁₁, hvs⟩ := mulPull_baseChange χ.toRingHom hpm hsy hs₁
  have heps := GlobalTheory.T.heckeKernel_sum_eq_card_torsion_mul_trace E H Dw l Xo Ω y₁.x x₁' Ψ₁ p n y₁.s s' β₁ s₁₁ e hisog hth htr hβ₁ hs₁₁
  haveI : Finite (transKer Xo.univ.t.G Ψ₁) := Finite.of_equiv _ e
  have hm := card_tors_mul hp hker e
  have hmpos := card_tors_pos (C := transKer Xo.univ.t.G Ψ₁) (p := p)
  have hmeq : Nat.card {a // a ∈ transKer Xo.univ.t.G Ψ₁ ∧ a ^ p = 1} = n / Ideal.absNorm P ^ i := by
    rw [← hm, Nat.mul_div_cancel _ (absNorm_pow_pos hadm)]

  obtain ⟨s₀₁, hs₀₁, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo T Ω χ.toRingHom 1 x' x₁' hpm'.1 s₀
  have hg₀₁ : SecGen x₁' s₀₁ := GlobalTheory.Frames.secGen_of_secNZ hB E H Dw l Xo Ω x₁' s₀₁
    (NonzeroGenerates.secNZ_pull hpm'.1 hs₀₁ (GlobalTheory.Frames.secNZ_of_secGen hB E H Dw l Xo T x' s₀ hgen))
  have hv₀ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁') (z : Z) (J), Good Xo.univ.t.PP.L z J →
      sv Xo.univ.t.G Xo.univ.t.PP s₀₁ r z J = sv Xo.univ.t.G Xo.univ.t.PP s₀ (r ≫ pm') z J := by
    obtain ⟨pmB, sB, fB, vB⟩ := hs₀₁
    obtain rfl : pmB = pm' := GlobalTheory.HeckeFrCompare.gx_ext (by rw [fB, hpm'.2.2]) (by rw [sB, hpm'.2.1])
    exact sv_of_pull pmB sB fun j hj => by
      have := vB j hj
      erw [NonzeroGenerates.scal_one, _root_.one_mul] at this
      exact this
  obtain ⟨α', hα', -⟩ := hg₀₁ s'

  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx y₁.x) (z : Z) (J), Good Xo.univ.t.PP.L z J →
      sv Xo.univ.t.G Xo.univ.t.PP t (r ≫ pm) z J = ((n / Ideal.absNorm P ^ i : ℕ) : Z.presheaf.stalk z) *
        gs (r ≫ (fst (Over.mk y₁.x) Xo.univ.t.G).left) z ⊤ (toΓ Ω α') *
          sv Xo.univ.t.G Xo.univ.t.PP t₀ (r ≫ pm) z J := by
    intro Z r z J hJ
    obtain ⟨h1, h2⟩ := ht Z (r ≫ pm) z J hJ
    have hsum : ∑ j, ((val β ((r ≫ pm) ≫ (translT Xo.univ.t.G (σ j)).left) z J)⁻¹).val *
        sv Xo.univ.t.G Xo.univ.t.PP s₁ ((r ≫ pm) ≫ (translT Xo.univ.t.G (σ j)).left) z J =
        (Nat.card {a // a ∈ transKer Xo.univ.t.G Ψ₁ ∧ a ^ p = 1} : Z.presheaf.stalk z) *
          sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ₁) z J := by
      rw [heps Z r z J hJ]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e₁ : (r ≫ pm) ≫ (translT Xo.univ.t.G (σ j)).left = (r ≫ (translT Xo.univ.t.G (e j).1).left) ≫ pm := by
        rw [Category.assoc, Category.assoc, translT_comp_can χ.toRingHom (σ j) (e j).1 hpm (he j)]
      rw [e₁, ← hvβ _ _ z J hJ, ← hvs _ _ z J hJ]
    have hs' := sv_smul (A := Xo.univ.t.G) (L := Xo.univ.t.PP) (T := Over.mk x₁') (a := toΓ Ω α') hα' (r ≫ Ψ₁) z hJ
    have h0 : sv Xo.univ.t.G Xo.univ.t.PP s₀ ((r ≫ pm) ≫ Ψ) z J = sv Xo.univ.t.G Xo.univ.t.PP s₀₁ (r ≫ Ψ₁) z J := by
      rw [hv₀ _ _ z J hJ, Category.assoc, Category.assoc, hc]
    rw [h1, h2, hsum, hs', h0, hmeq, Category.assoc, hf]
    ring
  refine ⟨(Nat.pos_of_ne_zero (by rw [← hmeq]; exact hmpos.ne')).ne', α', s₀₁, hs₀₁, hα', ?_, ?_⟩
  · intro w hw j hj
    let b : Over.mk y₁.x ⟶ Xo.univ.t.G := Over.homMk (w ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) (by
      show (w ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) ≫ Xo.univ.t.G.hom = y₁.x
      rw [Category.assoc, GlobalTheory.HeckeFrCompare.snd_hom, reassoc_of% hw, hpm.1])
    have hw₁f : (lift (𝟙 (Over.mk y₁.x)) b).left ≫ (fst (Over.mk y₁.x) Xo.univ.t.G).left = 𝟙 _ :=
      GlobalTheory.HeckeFrCompare.lift_l_fst _ _
    have hw₁ : (lift (𝟙 (Over.mk y₁.x)) b).left ≫ pm = w := GlobalTheory.HeckeFrCompare.gx_ext
      (by rw [Category.assoc, hpm.2.2, reassoc_of% hw₁f]; exact hw.symm)
      (by rw [Category.assoc, hpm.2.1, GlobalTheory.HeckeFrCompare.lift_l_snd]; rfl)
    refine appLE_eq_of_sv w t t₀ _ (fun z J hJ => ?_) j hj
    rw [← hw₁, hv _ _ z J hJ, hw₁f, map_mul, gs_mul (𝟙 (Sp Ω)) z ⊤ trivial, map_natCast]
    congr 2
    rw [gs_eq (𝟙 (Sp Ω)) z ⊤ trivial, map_natCast, map_natCast]
  · obtain ⟨w', hw'f, hw'nz⟩ := exists_ratPt_sv_ne_zero (hg₀₁ : IsThGen x₁' s₀₁)
    let b' : Over.mk x₁' ⟶ Xo.univ.t.G := Over.homMk (w' ≫ (snd (Over.mk x₁') Xo.univ.t.G).left) (by
      show (w' ≫ (snd (Over.mk x₁') Xo.univ.t.G).left) ≫ Xo.univ.t.G.hom = x₁'
      rw [Category.assoc, GlobalTheory.HeckeFrCompare.snd_hom, reassoc_of% hw'f])
    obtain ⟨a, ha⟩ := hisog.2.2.1 b'
    have hb' : (lift (𝟙 (Over.mk x₁')) b').left = w' := GlobalTheory.HeckeFrCompare.gx_ext
      (by rw [GlobalTheory.HeckeFrCompare.lift_l_fst, hw'f]; rfl) (by rw [GlobalTheory.HeckeFrCompare.lift_l_snd]; rfl)
    have hr₁ : (lift (𝟙 (Over.mk y₁.x)) a).left ≫ Ψ₁ = w' := ha.trans hb'
    obtain ⟨z⟩ : Nonempty (Sp Ω) := ⟨show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩⟩
    choose I hI using fun ψ : Sp Ω ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (ψ z)
    have hJ : Good Xo.univ.t.PP.L z I := hI
    have hwq : ((lift (𝟙 (Over.mk y₁.x)) a).left ≫ pm) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
        spMap χ.toRingHom := by
      rw [Category.assoc, hpm.2.2, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc]; exact Category.id_comp _
    have hne : sv Xo.univ.t.G Xo.univ.t.PP t₀ ((lift (𝟙 (Over.mk y₁.x)) a).left ≫ pm) z I ≠ 0 := by
      rw [(ht _ _ z I hJ).2, Category.assoc, ← hc, ← Category.assoc, ← hv₀ _ _ z I hJ, hr₁]
      intro h0
      exact hw'nz z I hJ (by simpa using congrArg (· * ((val β ((lift (𝟙 (Over.mk y₁.x)) a).left ≫ pm) z I)⁻¹).val) h0)
    obtain ⟨j, hj, hne'⟩ := appLE_ne_zero_of_sv _ t₀ z I hJ hne
    exact ⟨j, _, hj, hwq, hne'⟩

end GlobalTheory.HeckeScal


open GlobalTheory.HeckeScal in
theorem GlobalTheory.HeckeScal.exists_scal_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i n : ℕ) (T : Type) [CommRing T] [IsReduced T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (s₀ : LB.Sec (PPx x')), admitted l P p → IsHeckeFam P p i Ψ → IsListed Ψ σ → SecGen x' s₀ → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁'), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → ∃ s', IsThGen x₁' s' ∧ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') → ∃ a : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → IsThGen x₁' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s' → SecBC χ.toRingHom a x' x₁' s₀ s' := by
  intro E _ _ _ H Dw l Xo c P p i n T _ _ _ y x' Ψ σ s₀ hadm hfam hlist hgen hex
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨hlin, -, -, ⟨β, hβ⟩, -⟩ := id hfam
  have hσ : ∀ j, σ j ∈ transKer Xo.univ.t.G Ψ := fun j =>
    GlobalTheory.T.mem_kernel_of_geometric_fibres_reduced_base E H Dw l Xo T y.x x' Ψ (σ j) hlin.1 fun Ω _ _ χ x₁ x₁' Ψ₁ hF => by
      obtain ⟨e, he⟩ := hlist Ω χ x₁ x₁' Ψ₁ hF
      exact ⟨(e j).1, (e j).2, he j⟩
  obtain ⟨s₁, hs₁⟩ := exists_isMulPull p y.s
  obtain ⟨t, t₀, ht⟩ := exists_sums hβ.2.1 hσ s₁ s₀
  have hsm : Smooth (fst (Over.mk y.x) Xo.univ.t.G).left := by
    have := Xo.univ.t.semi.smooth
    show Smooth (pullback.fst y.x Xo.univ.t.G.hom)
    infer_instance
  obtain ⟨a', ha'⟩ := GlobalTheory.T.ratio_localFunctions_geometricFibre_descends_base T (Gx y.x) (fst (Over.mk y.x) Xo.univ.t.G).left _
    (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk y.x)).U t.f t₀.f hsm fun Ω _ _ χ => by
      letI : Algebra c.F Ω := (χ.comp (algebraMap c.F T)).toAlgebra
      let χ' : T →ₐ[c.F] Ω := { χ with commutes' := fun _ => rfl }
      obtain ⟨y₁, hy₁⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c T Ω χ' y
      obtain ⟨Ψ₁, hΨ₁⟩ := exists_isFib (Xo := Xo) χ hy₁.1 rfl Ψ hlin.1
      obtain ⟨s', hs'g, hs'⟩ := hex Ω χ' y₁ (spMap χ ≫ x') Ψ₁ hy₁ hΨ₁
      obtain ⟨-, α', -, -, -, hval, j, w, hj, hw, hne⟩ :=
        fibre hadm hfam hlist hgen hβ hs₁ ht χ' y₁ _ Ψ₁ s' hy₁ hΨ₁ hs'g hs'
      exact ⟨_, fun j w h hw => hval w hw j h, j, w, hj, hw, hne⟩
  refine ⟨algebraMap c.F T ((n / Ideal.absNorm P ^ i : ℕ) : c.F)⁻¹ * a', ?_⟩
  intro Ω _ _ _ χ y₁ x₁' Ψ₁ s' hFr hΨ₁ hth htr
  obtain ⟨hm0, α', s₀₁, hbc, hα', hval, j, w, hj, hw, hne⟩ :=
    fibre hadm hfam hlist hgen hβ hs₁ ht χ y₁ x₁' Ψ₁ s' hFr hΨ₁ hth htr
  obtain ⟨pm, pm', hpm, hpm', -, -⟩ := hΨ₁
  have hφ : ∀ u : Ω, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (toΓ Ω u) = u := fun u => by
    show ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom u = u
    rw [Iso.inv_hom_id]; rfl
  have hχa : χ a' = ((n / Ideal.absNorm P ^ i : ℕ) : Ω) * α' := by
    have e1 := congrArg (fun f => (w.appLE _ ⊤ hj).hom f) (ha' j)
    simp only [map_mul] at e1
    rw [appLE_toΓ χ.toRingHom _ _ w hj hw a', hval w hw j hj] at e1
    have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom e1
    simp only [map_mul, hφ] at e2
    have hne' : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((w.appLE _ ⊤ hj).hom (t₀.f j)) ≠ 0 := by
      intro h0
      apply hne
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom h0
      rw [map_zero] at this
      rw [← this]
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).hom _
      rw [Iso.hom_inv_id]; rfl
    exact (mul_right_cancel₀ hne' e2).symm
  have hχ : χ (algebraMap c.F T ((n / Ideal.absNorm P ^ i : ℕ) : c.F)⁻¹ * a') = α' := by
    rw [map_mul, χ.commutes, hχa, ← _root_.mul_assoc, ← map_natCast (algebraMap c.F Ω), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm0), map_one, _root_.one_mul]
  exact (NonzeroGenerates.pull_mul_iff hpm'.1 hbc).2 fun j => by
    rw [hα' j]
    congr 2
    exact hχ.symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_heckeTrace_thetaGenerator_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i n : ℕ) (T : Type) [CommRing T] [IsReduced T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (s₀ : LB.Sec (PPx x')), admitted l P p → IsHeckeFam P p i Ψ → IsListed Ψ σ → SecGen x' s₀ → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁'), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → ∃ s', IsThGen x₁' s' ∧ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') → ∃ a : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → IsThGen x₁' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s' → SecBC χ.toRingHom a x' x₁' s₀ s' := by
  first | exact @GlobalTheory.HeckeScal.exists_scal_of_family | exact GlobalTheory.HeckeScal.exists_scal_of_family | (intros; apply GlobalTheory.HeckeScal.exists_scal_of_family <;> assumption)
end
