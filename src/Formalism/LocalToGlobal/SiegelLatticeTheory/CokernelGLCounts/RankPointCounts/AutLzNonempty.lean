module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabKset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LiftMassCOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RhoTieCHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemLatGmap
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardAutLzGmap
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ind

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem inv_apply' (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) : (δ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) y = δ.symm y :=
  rfl

theorem xa_top : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp [Fin.is_lt]

theorem st_mul {γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (hδ : δ ∈ stabF D F0) :
    γ * δ ∈ stabF D F0 := by
  refine ⟨mul_mem hγ.1 hδ.1, fun j => ?_, ?_⟩
  · rw [kmap_mul, hδ.2.1 j, hγ.2.1 j]
  · show γ (δ F0.z) = F0.z
    rw [hδ.2.2, hγ.2.2]

theorem st_inv {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : γ⁻¹ ∈ stabF D F0 := by
  refine ⟨inv_mem hγ.1, fun j => ?_, ?_⟩
  · conv_lhs => rw [← hγ.2.1 j]
    rw [← kmap_mul, inv_mul_cancel, kmap_one]
  · show γ.symm F0.z = F0.z
    conv_lhs => rw [← hγ.2.2]
    exact γ.symm_apply_apply _

theorem stab_X_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ x ∈ F0.X := by
  rw [← xa_top] at hx ⊢
  rw [← hγ.2.1 D.R.rS]
  exact Submodule.mem_map_of_mem hx

theorem stab_perp_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 := hy _ (stab_X_mem F0 (st_inv F0 hγ) hx)
  have h2 := hγ.1 (γ⁻¹ x) y
  rw [inv_apply', LinearEquiv.apply_symm_apply] at h2
  rw [h2]
  exact h1

def ind {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 → WbQ D F0 :=
  Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
    ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (fun y hy => stab_perp_mem F0 hγ hy))
    (fun x hx => stab_X_mem F0 hγ hx)

theorem ind_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    ind F0 hγ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, stab_perp_mem F0 hγ x.2⟩ := rfl

theorem autLz_iff (Λ : Submodule (𝓞 D.host.E) (VS D).V) (φ : WbQ D F0 → WbQ D F0) :
    φ ∈ autLz D F0 Λ ↔ ∃ γ, ∃ hγ : γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ ∧ φ = ind F0 hγ := by
  constructor
  · rintro ⟨γ, hγ, hΛ, hφ⟩
    refine ⟨γ, hγ, hΛ, funext fun q => ?_⟩
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    exact (hφ x (stab_perp_mem F0 hγ x.2)).trans rfl
  · rintro ⟨γ, hγ, hΛ, rfl⟩
    exact ⟨γ, hγ, hΛ, fun x hx => rfl⟩

theorem ind_inv_cancel {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0) (q : WbQ D F0) :
    ind F0 (st_inv F0 hδ) (ind F0 hδ q) = q := by
  refine Submodule.Quotient.induction_on _ q (fun x => ?_)
  rw [ind_mk, ind_mk]
  congr 1
  apply Subtype.ext
  show δ⁻¹ (δ x.1) = x.1
  rw [inv_apply', LinearEquiv.symm_apply_apply]

theorem card_autLz_gmap {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card ↥(autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ)) = Nat.card ↥(autLz D F0 Λ) := by
  let c : (WbQ D F0 → WbQ D F0) → (WbQ D F0 → WbQ D F0) := fun φ => ind F0 hδ ∘ φ ∘ ind F0 (st_inv F0 hδ)
  have hc : Function.Injective c := by
    intro φ ψ hφψ
    funext q
    have h1 := congrFun hφψ (ind F0 hδ q)
    simp only [c, Function.comp, ind_inv_cancel] at h1
    have h2 := congrArg (ind F0 (st_inv F0 hδ)) h1
    rwa [ind_inv_cancel, ind_inv_cancel] at h2
  have hset : autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ) = c '' autLz D F0 Λ := by
    ext ψ
    rw [autLz_iff, Set.mem_image]
    constructor
    · rintro ⟨γ', hγ', hΛ', rfl⟩
      refine ⟨ind F0 (st_mul F0 (st_mul F0 (st_inv F0 hδ) hγ') hδ),
        (autLz_iff F0 Λ _).2 ⟨_, _, ?_, rfl⟩, ?_⟩
      · rw [gmap_mul', gmap_mul', hΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => ?_)
        simp only [c, Function.comp]
        rw [ind_mk, ind_mk, ind_mk, ind_mk]
        congr 1
        apply Subtype.ext
        show δ ((δ⁻¹ * γ' * δ) (δ⁻¹ x.1)) = γ' x.1
        show δ (δ⁻¹ (γ' (δ (δ⁻¹ x.1)))) = γ' x.1
        rw [inv_apply', inv_apply', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨γ, hγ, hΛ, rfl⟩ := (autLz_iff F0 Λ φ).1 hφ
      refine ⟨δ * γ * δ⁻¹, st_mul F0 (st_mul F0 hδ hγ) (st_inv F0 hδ), ?_, ?_⟩
      · rw [gmap_mul', ← gmap_mul' δ⁻¹ δ, inv_mul_cancel, gmap_one', gmap_mul', hΛ]
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => rfl)
  rw [hset]
  exact Nat.card_image_of_injective hc _

end Ind

end Formalism.L2.SG.RhoPf
end
end

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section W3

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fuX : (X.Fu u).X = Xs X := by
  rw [FlagG.X, X.Fu_e]
  rfl

theorem AH_stab {Λ : Submodule (𝓞 D.host.E) (VS D).V} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ AH X u Λ) : γ ∈ stabF D (X.Fu u) := by
  obtain ⟨hi, he, -, hz, -⟩ := hγ
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact he a
  · show γ (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact hz

def indA (Λ : Submodule (𝓞 D.host.E) (VS D).V) (γ : ↥(AH X u Λ)) : WbQ D (X.Fu u) → WbQ D (X.Fu u) :=
  ind (X.Fu u) (AH_stab X u γ.2)

theorem prV_perp (v : (VS D).V) : prV X v ∈ perpS (VS D) (X.Fu u).X := by
  intro x hx
  rw [fuX] at hx
  exact hT_Xs_prV X hx v

theorem prV_fix (w : (VS D).V) (he : ∀ a, (VS D).hT (X.eX a) w = 0) (hf : ∀ a, (VS D).hT (X.fY a) w = 0) :
    prV X w = w := by
  rw [prV_apply]
  simp [he, hf]

theorem prV_of_fix (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    prV X (g (prV X v)) = g (prV X v) := by
  have h1 : ∀ a, (VS D).hT (X.eX a) (g (prV X v)) = 0 := fun a => by
    rw [← hge a, hgi, hT_e_prV]
  have h2 : ∀ a, (VS D).hT (X.fY a) (g (prV X v)) = 0 := fun a => by
    rw [← hgf a, hgi, hT_f_prV]
  exact prV_fix X _ h1 h2

theorem fix_sub_prV (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    g (v - prV X v) = v - prV X v := by
  rw [sub_prV_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, hge, hgf]

theorem indA_inj (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Function.Injective (indA X u Λ) := by
  intro γ γ' hγγ
  obtain ⟨hi, he, hf, -, -⟩ := γ.2
  obtain ⟨hi', he', hf', -, -⟩ := γ'.2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  have hq := congrFun hγγ (Submodule.Quotient.mk ⟨prV X y, prV_perp X u y⟩)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hq
  rw [Submodule.Quotient.eq] at hq
  have hd : γ.1 (prV X y) - γ'.1 (prV X y) ∈ Xs X := by
    rw [← fuX X u]
    exact hq
  have h0 := prV_Xs X hd
  rw [map_sub, prV_of_fix X γ.1 hi he hf, prV_of_fix X γ'.1 hi' he' hf', sub_eq_zero] at h0
  calc γ.1 y = γ.1 (y - prV X y) + γ.1 (prV X y) := by rw [← map_add (f := _), sub_add_cancel]
    _ = γ'.1 (y - prV X y) + γ'.1 (prV X y) := by
        rw [fix_sub_prV X γ.1 he hf, fix_sub_prV X γ'.1 he' hf', h0]
    _ = γ'.1 y := by rw [← map_add (f := _), sub_add_cancel]

theorem mem_lat_gmap (h : Hfin X u) {γ0 : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hΛ : Formalism.HermitianLatticesTheory.gmap γ0 (lat X u h) = lat X u h) :
    (∀ y ∈ latOf X u h, γ0 y ∈ latOf X u h) ∧ (∀ y ∈ latOf X u h, γ0.symm y ∈ latOf X u h) := by
  constructor
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap, LinearEquiv.symm_apply_apply]
    exact hy
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap] at hy
    exact hy

theorem autLz_range (h : Hfin X u) : autLz D (X.Fu u) (lat X u h) = Set.range (indA X u (lat X u h)) := by
  ext φ
  rw [autLz_iff]
  constructor
  · rintro ⟨γ0, hγ0, hΛ, rfl⟩
    have hinv : γ0⁻¹ ∈ stabF D (X.Fu u) := st_inv (X.Fu u) hγ0
    let γ : (VS D).V ≃ₗ[D.host.E] (VS D).V := LinearEquiv.ofLinear (gW X γ0) (gW X γ0⁻¹)
      (LinearMap.ext fun y => gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y)
      (LinearMap.ext fun y => gW_gW X u hinv hγ0 (fun w => LinearEquiv.symm_apply_apply γ0 w) y)
    have hm := mem_lat_gmap X u h hΛ
    have hAH : γ ∈ AH X u (lat X u h) := by
      refine ⟨fun x y => gW_isom X u hγ0 x y, fun a => gW_e X a, fun a => gW_f X a, stabilizer_fix_anisotropic X u hγ0, ?_⟩
      ext y
      rw [mem_gmap]
      constructor
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        have := gW_mem X u h h hm.1 hy
        have e : gW X γ0 (γ.symm y) = y := gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y
        rwa [e] at this
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        exact gW_mem X u h h (fun w hw => hm.2 w hw) hy
    refine ⟨⟨γ, hAH⟩, ?_⟩
    funext q
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    show ind (X.Fu u) (AH_stab X u hAH) (Submodule.Quotient.mk x) = ind (X.Fu u) hγ0 (Submodule.Quotient.mk x)
    rw [ind_mk, ind_mk, Submodule.Quotient.eq]
    show gW X γ0 x.1 - γ0 x.1 ∈ (X.Fu u).X
    apply (show Xs X ≤ (X.Fu u).X from (fuX X u).ge)
    have hx : ∀ a, (VS D).hT (X.eX a) x.1 = 0 := fun a => x.2 _ (by rw [fuX X u]; exact eX_mem_Xs X a)
    have h1 := sub_prV_mem_Xs X hx
    have h2 := stab_Xs X u hγ0 h1
    have h3 := stab_perp X u hγ0 x.1
    have e : gW X γ0 x.1 - γ0 x.1 =
        (x.1 - prV X x.1) - γ0 (x.1 - prV X x.1) - (γ0 (prV X x.1) - prV X (γ0 (prV X x.1))) := by
      rw [gW_apply, map_sub]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) h3
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, AH_stab X u γ.2, γ.2.2.2.2.2, rfl⟩

theorem card_AH (h : Hfin X u) :
    Nat.card ↥(AH X u (lat X u h)) = Nat.card ↥(autLz D (X.Fu u) (lat X u h)) := by
  rw [autLz_range]
  exact (Nat.card_range_of_injective (indA_inj X u _)).symm

end W3

end Formalism.L2.SG.RhoPf
end
end

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem weight_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    ((Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) : ℕ) : ℝ)⁻¹ =
      wRow D (X.Fu u) (cls X u what₂ h) := by
  obtain ⟨-, δ, hδ, hδe⟩ := cls_spec hR hL h
  have e1 : Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) =
      Nat.card ↥(autLz D (X.Fu u) (cls X u what₂ h)) := by
    rw [show gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom = stabR X u h from rfl, card_stab, card_AH,
      ← hδe, card_autLz_gmap (X.Fu u) hδ]
  rw [e1]
  rfl

theorem massH_rows (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (hS : LatSurj X u) :
    Formalism.L2.SG.TypedSets.massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (Formalism.L2.SG.TypedSets.frameOf X u) =
      Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) what₂ := by
  rw [massH_eq]
  exact massCl_eq_sum (gamR X u) (kR X u) what₂ (cls X u what₂) (wRow D (X.Fu u))
    (fun h => (cls_spec hR hL h).1) (cls_rel hR hL hI) (cls_surj hR hL hS) (weight_eq X u what₂ hR hL)

end Final

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LatRowLat X u) (hI : Formalism.L2.SG.Pf.LatInj X u) (hS : Formalism.L2.SG.Pf.LatSurj X u) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  Formalism.L2.SG.RhoPf.massH_rows X u (Y.what₂ u) (Y.rowsOK u) hL hI hS

end Formalism.L2.SG.MassDataConc
end
end

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLz_nonempty {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (autLz D F0 Λ).Nonempty := by
  have h1 : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := ⟨one_mem _, fun j => kmap_one _, rfl⟩
  exact ⟨ind F0 h1, (autLz_iff F0 Λ _).2 ⟨1, h1, gmap_one' Λ, rfl⟩⟩

theorem massRows_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
  have hne : (Y.what₂ u).Nonempty := ⟨_, (cls_spec (Y.rowsOK u) (latRowLat X u) 1).1⟩
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_pos (fun Λ hΛ => ?_) hne
  haveI := Formalism.L2.SG.Pf.FibreCounting.autLz_finite (Y := Y) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) hΛ
  have hpos : 0 < Nat.card ↥(autLz D (X.Fu u) Λ) := by
    obtain ⟨φ, hφ⟩ := autLz_nonempty (X.Fu u) Λ
    haveI : Nonempty ↥(autLz D (X.Fu u) Λ) := ⟨⟨φ, hφ⟩⟩
    exact Nat.card_pos
  unfold Formalism.MainNotions.S.wRow
  exact inv_pos.2 (Nat.cast_pos.2 hpos)

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_closed {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  RhoTieC_holds X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.latRowLat X u) (Formalism.L2.SG.Pf.latInj X u)
    (Formalism.L2.SG.Pf.latSurj X u)

end Formalism.L2.SG.MassDataConc
