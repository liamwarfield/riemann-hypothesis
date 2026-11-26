module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MemPerpMapFlag
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Flag

variable {D : D7} {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)

theorem mapFlag_inv (F0 : FlagG (VS D) D.R.rS T) :
    Formalism.L2.SG.Saturated.mapFlag β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) = F0 := by
  have key : ∀ x, (β⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (β x) = x := fun x => β.symm_apply_apply x
  cases F0
  simp only [Formalism.L2.SG.Saturated.mapFlag, key]
  all_goals rfl

theorem stabF_conj (F0 : FlagG (VS D) D.R.rS T) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    β * γ * β⁻¹ ∈ stabF D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) := by
  simp only [stabF] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have hXa : ∀ j, (Formalism.L2.SG.Saturated.mapFlag β hβ F0).Xa j =
      (F0.Xa j).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    first
      | rfl
      | (simp only [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp]; rfl)
      | (simp only [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_image]; rfl)
      | simp [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_image, ← Set.range_comp]
  have hc : ((β * γ * β⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).comp
      (β : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (β : (VS D).V →ₗ[D.host.E] (VS D).V).comp (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    ext x
    show β (γ (β.symm (β x))) = β (γ x)
    rw [β.symm_apply_apply]
  refine ⟨mul_mem (mul_mem hβ h1) (inv_mem hβ), fun j => ?_, ?_⟩
  · rw [hXa j, ← Submodule.map_comp, hc, Submodule.map_comp, h2 j]
  · show β (γ (β.symm (β F0.z))) = β F0.z
    rw [β.symm_apply_apply, h3]

theorem stabF_conj_inv (F0 : FlagG (VS D) D.R.rS T) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ stabF D (Formalism.L2.SG.Saturated.mapFlag β hβ F0)) : β⁻¹ * γ * β ∈ stabF D F0 := by
  have h := stabF_conj β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) hγ
  rwa [mapFlag_inv, inv_inv] at h

end Flag

theorem RowRepsIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.RowRepsIso D := by
  have hL := LatIso_holds D
  intro β hβ T F0 what₂ hR
  obtain ⟨hrow, huniq⟩ := hR
  refine ⟨?_, ?_⟩
  · intro Λ hΛ
    obtain ⟨Λ0, h0, rfl⟩ := Finset.mem_image.1 hΛ
    exact Formalism.L2.SG.TermTieOf.rowLat_map hL β hβ F0 Λ0 (hrow Λ0 h0)
  · intro Λ hΛ
    have h0 : IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap β⁻¹ Λ) := by
      have h := Formalism.L2.SG.TermTieOf.rowLat_map hL β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) Λ hΛ
      rw [mapFlag_inv] at h
      exact h
    obtain ⟨M, ⟨hM, γ, hγ, hγM⟩, hU⟩ := huniq _ h0
    refine ⟨Formalism.HermitianLatticesTheory.gmap β M, ⟨Finset.mem_image_of_mem _ hM, β * γ * β⁻¹, stabF_conj β hβ F0 hγ, ?_⟩, ?_⟩
    · rw [gmap_mul, gmap_mul, gmap_inv_gmap, hγM, gmap_gmap_inv]
    · rintro N ⟨hN, γ', hγ', hγN⟩
      obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 hN
      have hM'M : M' = M := by
        refine hU M' ⟨hM', β⁻¹ * γ' * β, stabF_conj_inv β hβ F0 hγ', ?_⟩
        rw [gmap_mul, gmap_mul, hγN]
      rw [hM'M]

section Wb

variable {D : D7} {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
  (F0 : FlagG (VS D) D.R.rS T)

theorem perp_mapFlag :
    perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X =
      (perpS (VS D) F0.X).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have hb : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y := by
    intro x y
    first
      | exact hβ x y
      | exact LinearMap.congr_fun₂ hβ x y
      | exact Formalism.HermitianLatticesTheory.isom_apply hβ x y
      | exact Formalism.L2.SG.Saturated.isom_apply hβ x y
      | exact isom_apply hβ x y
  have hX : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X = F0.X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    first
      | rfl
      | (simp only [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp]; rfl)
      | (simp only [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_union,
          Set.image_singleton, ← Set.range_comp]; rfl)
      | simp [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp, Set.image_union]
  ext y
  rw [hX, Submodule.mem_map_equiv]
  simp only [perpS, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    have h1 := h (β x) (Submodule.mem_map_of_mem hx)
    rwa [← β.apply_symm_apply y, hb] at h1
  · intro h x hx
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    have h2 := hb x' (β.symm y)
    rw [β.apply_symm_apply] at h2
    exact h2.trans (h x' hx')

theorem mem_perp_mapFlag {y : (VS D).V} :
    y ∈ perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X ↔ β.symm y ∈ perpS (VS D) F0.X := by
  rw [perp_mapFlag β hβ F0, Submodule.mem_map_equiv]

def perpEq : ↥(perpS (VS D) F0.X) ≃ₗ[D.host.E] ↥(perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X) :=
  LinearEquiv.ofSubmodules β _ _ (perp_mapFlag β hβ F0).symm

theorem perpEq_map :
    Submodule.map (perpEq β hβ F0 : ↥(perpS (VS D) F0.X) →ₗ[D.host.E] ↥(perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X))
      (F0.X.comap (perpS (VS D) F0.X).subtype) =
      (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X.comap
        (perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X).subtype := by
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hxX, hfx⟩
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hxX
    show y ∈ _
    rw [Formalism.L2.SG.Pf.X_mapFlag β hβ F0, Submodule.mem_map]
    exact ⟨x.1, hxX, congrArg Subtype.val hfx⟩
  · intro hyX
    have hyX' : y ∈ F0.X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← Formalism.L2.SG.Pf.X_mapFlag β hβ F0]; exact hyX
    obtain ⟨x, hxX, rfl⟩ := (Submodule.mem_map).1 hyX'
    have hx0 : x ∈ perpS (VS D) F0.X := by
      have h := (mem_perp_mapFlag β hβ F0).1 hy
      have e : β.symm ((β : (VS D).V →ₗ[D.host.E] (VS D).V) x) = x := β.symm_apply_apply x
      rwa [e] at h
    exact ⟨⟨x, hx0⟩, hxX, Subtype.ext rfl⟩

def wbEquiv : WbQ D F0 ≃ WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) :=
  (Submodule.Quotient.equiv _ _ (perpEq β hβ F0) (perpEq_map β hβ F0)).toEquiv

theorem wbEquiv_mk (x : ↥(perpS (VS D) F0.X)) :
    wbEquiv β hβ F0 (Submodule.Quotient.mk x) = Submodule.Quotient.mk (perpEq β hβ F0 x) := rfl

theorem autLz_fwd {Λ : Submodule (𝓞 D.host.E) (VS D).V} {φ : WbQ D F0 → WbQ D F0} (hφ : φ ∈ autLz D F0 Λ) :
    (wbEquiv β hβ F0) ∘ φ ∘ (wbEquiv β hβ F0).symm ∈
      autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  obtain ⟨γ, hγ, hΛ, hφ⟩ := hφ
  refine ⟨β * γ * β⁻¹, stabF_conj β hβ F0 hγ, ?_, ?_⟩
  · rw [gmap_mul, gmap_mul, gmap_inv_gmap, hΛ]
  · intro x hx
    have hy0 : β.symm x.1 ∈ perpS (VS D) F0.X := (mem_perp_mapFlag β hβ F0).1 x.2
    have hy1 : γ (β.symm x.1) ∈ perpS (VS D) F0.X := by
      have h := (mem_perp_mapFlag β hβ F0).1 hx
      have key : β.symm ((β * γ * β⁻¹) x.1) = γ (β.symm x.1) := by
        show β.symm (β (γ (β.symm x.1))) = _
        exact β.symm_apply_apply _
      rwa [key] at h
    have e1 : (wbEquiv β hβ F0).symm (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨β.symm x.1, hy0⟩ := by
      rw [Equiv.symm_apply_eq, wbEquiv_mk]
      congr 1
      exact Subtype.ext (β.apply_symm_apply x.1).symm
    simp only [Function.comp_apply]
    rw [e1, hφ ⟨β.symm x.1, hy0⟩ hy1, wbEquiv_mk]
    congr 1

theorem autLz_bwd {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {ψ : WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) → WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0)}
    (hψ : ψ ∈ autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) :
    (wbEquiv β hβ F0).symm ∘ ψ ∘ (wbEquiv β hβ F0) ∈ autLz D F0 Λ := by
  obtain ⟨γ, hγ, hΛ, hψ⟩ := hψ
  refine ⟨β⁻¹ * γ * β, stabF_conj_inv β hβ F0 hγ, ?_, ?_⟩
  · rw [gmap_mul, gmap_mul, hΛ, gmap_inv_gmap]
  · intro x hx
    have hx1 : γ (β x.1) ∈ perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X := by
      rw [mem_perp_mapFlag β hβ F0]
      exact hx
    simp only [Function.comp_apply]
    rw [wbEquiv_mk, Equiv.symm_apply_eq, hψ (perpEq β hβ F0 x) hx1, wbEquiv_mk]
    congr 1
    exact Subtype.ext (show γ (β x.1) = β (β.symm (γ (β x.1))) from (β.apply_symm_apply _).symm)

def autEquiv (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    autLz D F0 Λ ≃ autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) where
  toFun φ := ⟨_, autLz_fwd β hβ F0 φ.2⟩
  invFun ψ := ⟨_, autLz_bwd β hβ F0 ψ.2⟩
  left_inv φ := Subtype.ext (funext fun x => by simp)
  right_inv ψ := Subtype.ext (funext fun x => by simp)

end Wb

theorem WRowIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.WRowIso D := by
  intro β hβ T F0 Λ
  simp only [Formalism.MainNotions.S.wRow]
  rw [Nat.card_congr (autEquiv β hβ F0 Λ).symm]

end Formalism.L2.SG.Pf.WittFlags
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJoint
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeVIndep
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.DataInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7}

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

def VIndepAt (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₁ h₁' →
      IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₂'))

end Formalism.L2.SG.Pf.Carrier
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
  {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def JointTensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ x : ∀ v, X.Vloc u' v,
      (X.piU u h⁻¹) ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.piU u' h' (X.tensU u' x))) =
        X.tensU u (fun v => eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (T (τ.symm v)).base (ν' (τ.symm v)) (m₀ (τ.symm v)) (f (τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd S.G.r S.g 1 (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p)))
            ((eQ v).symm (x v))))

theorem vJoint_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (hsc : 0 < sc) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (h2 : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) :
    VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ := by
  unfold JointTensorAt at h2
  unfold VJoint
  intro p w hpw hrep hpos x
  have hex : ∃ q : X.B.I.Ginf × X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' (gamW X u u' w) q.1 q.2 := by
    have hii : i0' = i0 := funext fun v => (hi v).symm
    rw [hii]
    obtain ⟨h, h', hh⟩ := dual_frame_at_places X u u' sc i0 hsc w hrep hpos
    exact ⟨(h, h'), hh⟩
  refine Eq.trans ?_ (h2 p w hpw hrep hpos hex.choose.1 hex.choose.2 hex.choose_spec x)
  unfold unscaledOperatorAtPointRepresentative unscaledFrameConjugatedOperator
  rw [if_pos hrep, dite_eq_left hex]
  rfl

private theorem sign_flip_involutive {K : Type} [Ring K] (r b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K) :
    Formalism.L2.SG.DataInst.signAux r b (Formalism.L2.SG.DataInst.signAux r b x) = x := by
  induction x generalizing b with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨s, t⟩ := a
    have hm : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1 : K) ^ n * t) = t := by
      intro n
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    simp only [Formalism.L2.SG.DataInst.signAux, hm, ih]

private theorem exists_pt_ptOfL_of_point (w : Point D.host.E (D.R.rS + 1)) :
    ∃ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptOfL (D := D) (D.R.rS + 1) p = some w := by
  refine ⟨Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w), ?_⟩
  have hs : Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w)) =
      Formalism.L2.S.ptList w := sign_flip_involutive _ _ _
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList
  split_ifs with h
  · congr 1
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext hs
  · exact (h (by rw [hs]; exact Formalism.L2.S.ptList_isPtL w)).elim

theorem vIndepAt_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hJT : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) : VIndepAt X u u' sc i0 i0' νq := by
  unfold JointTensorAt at hJT
  unfold VIndepAt
  intro w hrep hpos h₁ h₁' h₂ h₂' hf₁ hf₂
  obtain ⟨p, hp⟩ := exists_pt_ptOfL_of_point (D := D) w

  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on_range (X.81 u') fun x => ?_)
  have e1 := hJT p w hp hrep hpos h₁ h₁' hf₁ x
  have e2 := hJT p w hp hrep hpos h₂ h₂' hf₂ x
  exact e1.trans e2.symm

end Formalism.L2.SG.Pf.CarrierXAll
end
end
