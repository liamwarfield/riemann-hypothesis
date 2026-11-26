module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.IsFixedConvMap
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.GmapInjective
noncomputable section

namespace PI.RepsIndep.Tr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem mem_gmap {γ : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ Formalism.HermitianLatticesTheory.gmap γ L ↔ γ.symm x ∈ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

theorem ap_mem_gmap {γ : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} {x : S.V} :
    γ x ∈ Formalism.HermitianLatticesTheory.gmap γ L ↔ x ∈ L := by
  rw [mem_gmap, LinearEquiv.symm_apply_apply]

theorem smul_symm (γ : S.V ≃ₗ[E] S.V) (s : 𝓞 E) (x : S.V) : γ.symm (s • x) = s • γ.symm x := by
  rw [← algebraMap_smul E s x, map_smul, algebraMap_smul]

theorem gmap_symm_gmap (γ : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ.symm (Formalism.HermitianLatticesTheory.gmap γ L) = L := by
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm, ap_mem_gmap]

theorem gmap_inf (γ : S.V ≃ₗ[E] S.V) (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap γ A ⊓ Formalism.HermitianLatticesTheory.gmap γ B := by
  ext x
  simp only [mem_gmap, Submodule.mem_inf]

theorem gmap_sup (γ : S.V ≃ₗ[E] S.V) (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap γ A ⊔ Formalism.HermitianLatticesTheory.gmap γ B := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.map_sup]

theorem gmap_span (γ : S.V ≃ₗ[E] S.V) (s : Set S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (Submodule.span (𝓞 E) s) = Submodule.span (𝓞 E) (γ '' s) := by
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_span]
  rfl

theorem coe_gmap (γ : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = γ '' (L : Set S.V) := by
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
  rfl

theorem gmap_toO (γ : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (toO S U) = toO S (U.map (γ : S.V →ₗ[E] S.V)) := by
  ext x
  rw [mem_gmap]
  simp only [toO, Submodule.restrictScalars_mem]
  rw [Submodule.mem_map_equiv]

theorem gmap_smul (γ : S.V ≃ₗ[E] S.V) (I : Ideal (𝓞 E)) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (I • L) = I • Formalism.HermitianLatticesTheory.gmap γ L := by
  simp only [Formalism.HermitianLatticesTheory.gmap]
  exact Submodule.map_smul'' _ _ _

theorem gmap_locS (γ : S.V ≃ₗ[E] S.V) (M : Submonoid (𝓞 E)) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.locS M L) = Formalism.HermitianLatticesTheory.locS M (Formalism.HermitianLatticesTheory.gmap γ L) := by
  ext x
  rw [mem_gmap]
  show (∃ s ∈ M, s • γ.symm x ∈ L) ↔ ∃ s ∈ M, s • x ∈ Formalism.HermitianLatticesTheory.gmap γ L
  simp only [mem_gmap, smul_symm]

theorem gmap_locP (γ : S.V ≃ₗ[E] S.V) (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.localization₂ p L) = Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.gmap γ L) :=
  gmap_locS γ p.primeCompl L

theorem spanE_gmap (γ : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    spanE S (Formalism.HermitianLatticesTheory.gmap γ M) = (spanE S M).map (γ : S.V →ₗ[E] S.V) := by
  rw [spanE, spanE, coe_gmap, Submodule.map_span]
  rfl

theorem iso_ap {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) :
    S.hT (γ x) (γ y) = S.hT x y :=
  hγ x y

theorem iso_symm {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) : γ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT :=
  (Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hγ

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orth_map {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U : Submodule E S.V) :
    orth S (U.map (γ : S.V →ₗ[E] S.V)) = (orth S U).map (γ : S.V →ₗ[E] S.V) := by
  ext v
  rw [Submodule.mem_map_equiv, mem_orth, mem_orth]
  constructor
  · intro h x hx
    have := h (γ x) (Submodule.mem_map_of_mem hx)
    rw [← iso_ap hγ x (γ.symm v), LinearEquiv.apply_symm_apply]
    simpa using this
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have := h x hx
    rw [← iso_ap hγ x (γ.symm v), LinearEquiv.apply_symm_apply] at this
    simpa using this

variable {r : ℕ}

def mapF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) : FlagG S r T where
  e := fun a => γ (F.e a)
  z := γ F.z
  e_indep := F.e_indep.map' (γ : S.V →ₗ[E] S.V) γ.ker
  e_iso a b := by rw [iso_ap hγ]; exact F.e_iso a b
  z_orth a := by rw [iso_ap hγ]; exact F.z_orth a
  z_norm := by rw [iso_ap hγ]; exact F.z_norm

def mapL {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) : LFlag S r T :=
  ⟨mapF γ hγ F.fl, γ F.zt⟩

theorem flag_ext {T : E} {F G : FlagG S r T} (he : F.e = G.e) (hz : F.z = G.z) : F = G := by
  cases F
  cases G
  dsimp only at he hz
  subst he hz
  rfl

theorem lflag_ext {T : E} {F G : LFlag S r T} (h : F.fl = G.fl) (hz : F.zt = G.zt) : F = G := by
  cases F
  cases G
  dsimp only at h hz
  subst h hz
  rfl

theorem mapL_symm {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    mapL γ.symm (iso_symm hγ) (mapL γ hγ F) = F := by
  apply lflag_ext
  · apply flag_ext
    · funext a
      simp [mapL, mapF]
    · simp [mapL, mapF]
  · simp [mapL]

theorem mapL_symm' {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ' : γ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : LFlag S r T) : mapL γ hγ (mapL γ.symm hγ' F) = F := by
  apply lflag_ext
  · apply flag_ext
    · funext a
      simp [mapL, mapF]
    · simp [mapL, mapF]
  · simp [mapL]

theorem fvec_mapF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (i : Fin (r + 1)) :
    (mapF γ hγ F).fvec i = γ (F.fvec i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [FlagG.fvec, mapF]

theorem frame_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (i : Fin (r + 1)) :
    frame (mapL γ hγ F) i = γ (frame F i) :=
  fvec_mapF hγ F.fl i

theorem Xa_mapF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) :
    (mapF γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.Xa, FlagG.Xa, Submodule.map_span, Set.image_image]
  rfl

theorem X_mapF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) :
    (mapF γ hγ F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.X, FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

theorem Zhat_mapF {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T)
    (F' : FlagG S r T') : Zhat (mapF γ hγ F) (mapF γ hγ F') = Zhat F F' := by
  ext a b
  show brS S ((mapF γ hγ F').fvec b) ((mapF γ hγ F).fvec a) = brS S (F'.fvec b) (F.fvec a)
  rw [fvec_mapF, fvec_mapF]
  exact iso_ap hγ _ _

end PI.RepsIndep.Tr
end
end

noncomputable section

namespace PI.RepsIndep.Tr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem Xsp_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapL γ hγ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) :=
  X_mapF hγ F.fl

theorem Xflag_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapL γ hγ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) :=
  Xa_mapF hγ F.fl j

theorem XLam_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) : XLam (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (XLam Λ F) := by
  simp only [XLam, Xsp_mapL hγ, gmap_inf, gmap_toO]

theorem Lrep_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) : Lrep (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (Lrep Λ F) := by
  simp only [Lrep, Xsp_mapL hγ, orth_map hγ, gmap_inf, gmap_toO]

theorem Lsub_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) : Lsub (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (Lsub Λ F) := by
  simp only [Lsub, Lrep_mapL hγ, Xsp_mapL hγ, orth_map hγ, gmap_inf, gmap_sup, gmap_toO]

theorem ModG_map {γ : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {x : S.V} (h : ModG S Λ g x) :
    ModG S (Formalism.HermitianLatticesTheory.gmap γ Λ) g (γ x) := by
  intro P hP
  have h1 := h P hP
  rw [← gmap_smul, ← gmap_locP, ap_mem_gmap]
  exact h1

theorem frameAct_map {γ : S.V ≃ₗ[E] S.V} {n : ℕ} (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E))
    (b : Fin n) : frameAct (fun i => γ (f i)) ξ b = γ (frameAct f ξ b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frameAct, map_sum, map_smul]

theorem frame_mapL' {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    frame (mapL γ hγ F) = fun i => γ (frame F i) :=
  funext (frame_mapL hγ F)

theorem AdmWit_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {g : ℕ} {F : LFlag S r T} {F' : LFlag S r T'} {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h : AdmWit Λ g F F' ξ) : AdmWit (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) (mapL γ hγ F') ξ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun b => ?_⟩
  simp only [frame_mapL' hγ, frameAct_map]
  rw [← map_sub]
  exact ModG_map (h3 b)

theorem IsLift_map {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {F : LFlag S r T} (h : IsLift Λ F) : IsLift (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨ap_mem_gmap.2 h1, by show γ F.zt = γ F.fl.z; rw [h2]⟩

theorem IsFixedConv_map {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {g : ℕ} {F : LFlag S r T} (h : IsFixedConv Λ g F) : IsFixedConv (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun P => ?_, fun c hc => h2 c ?_⟩
  · obtain ⟨c, hc0, hc1, hc2⟩ := h1 P
    refine ⟨c, hc0, hc1, ?_⟩
    rw [XLam_mapL hγ, ← gmap_locP, hc2, gmap_locP, gmap_span, ← Set.range_comp]
    simp only [Function.comp_def, map_smul]
    rfl
  · rw [Lsub_mapL hγ] at hc
    have h3 : γ (c • F.fl.z) ∈ Formalism.HermitianLatticesTheory.gmap γ (Lsub Λ F) := by
      rw [map_smul]
      exact hc
    exact ap_mem_gmap.1 h3

theorem UU_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') :
    UU (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) (mapL γ hγ F') = Formalism.HermitianLatticesTheory.gmap γ (UU Λ F F') := by
  simp only [UU, XLam_mapL hγ, gmap_sup, gmap_span, Set.image_singleton]
  rfl

theorem UUE_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') :
    UUE (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) (mapL γ hγ F') = (UUE Λ F F').map (γ : S.V →ₗ[E] S.V) := by
  rw [UUE, UUE, UU_map hγ, spanE_gmap]

theorem BLat_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') :
    BLat (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) (mapL γ hγ F') = Formalism.HermitianLatticesTheory.gmap γ (BLat Λ F F') := by
  simp only [BLat, UUE_map hγ, gmap_inf, gmap_toO]

theorem Mplus_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    Mplus (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) (mapL γ hγ F') ξ = Formalism.HermitianLatticesTheory.gmap γ (Mplus Λ g F F' ξ) := by
  simp only [Mplus, gmap_span, Set.image_union, Set.image_singleton, XLam_mapL hγ, coe_gmap,
    ← Set.range_comp]
  congr 3
  funext b
  simp only [Function.comp_apply, frame_mapL' hγ, frameAct_map, map_smul, map_sub]

theorem IsGeneric_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {g : ℕ} {F : LFlag S r T} {F' : LFlag S r T'} (h : IsGeneric Λ g F F') :
    IsGeneric (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) (mapL γ hγ F') := by
  obtain ⟨ξ, hξ, hP⟩ := h
  refine ⟨ξ, AdmWit_map hγ hξ, fun P => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · rw [BLat_map hγ, Mplus_map hγ, ← gmap_locP, ← gmap_locP, (hP P).1 hg]
  · rw [BLat_map hγ, UU_map hγ, ← gmap_locP, ← gmap_locP, (hP P).2 hg]

def conj (γ n : S.V ≃ₗ[E] S.V) : S.V ≃ₗ[E] S.V := γ.symm.trans (n.trans γ)

theorem conj_apply (γ n : S.V ≃ₗ[E] S.V) (x : S.V) : conj γ n x = γ (n (γ.symm x)) := rfl

theorem gmap_trans (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (a.trans b) L = Formalism.HermitianLatticesTheory.gmap b (Formalism.HermitianLatticesTheory.gmap a L) := by
  simp only [Formalism.HermitianLatticesTheory.gmap, ← Submodule.map_comp]
  rfl

theorem IsAutLam_conj {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {n : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ n) : IsAutLam S (Formalism.HermitianLatticesTheory.gmap γ Λ) (conj γ n) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, ?_⟩
  · rw [conj_apply, conj_apply, iso_ap hγ, iso_ap h1, iso_ap (iso_symm hγ)]
  · rw [conj, gmap_trans, gmap_trans, gmap_symm_gmap, h2]

theorem NLam_conj {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (h : n ∈ NLam Λ F) :
    conj γ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨IsAutLam_conj hγ h1, fun j x hx => ?_, fun x hx => ?_⟩
  · rw [Xflag_mapL hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, h2 j y hy, ?_⟩
    simp [conj_apply, map_sub]
  · rw [Xsp_mapL hγ, orth_map hγ] at hx
    rw [Xsp_mapL hγ]
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, h3 y hy, ?_⟩
    simp [conj_apply, map_sub]

end PI.RepsIndep.Tr
end
end

noncomputable section

namespace PI.RepsIndep.Tr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.UniformConstantsAndStatements

theorem cntCl_equiv {α : Type} (f g : α → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ a, f (g a) = a)
    (X Y : Set α) (R R' : α → α → Prop)
    (hX : ∀ a, f a ∈ Y ↔ a ∈ X) (hR : ∀ a b, R' (f a) (f b) ↔ R a b) :
    Cnt.cntCl Y R' = Cnt.cntCl X R := by
  have hinj : Function.Injective (fun O : Set α => f ⁻¹' O) := by
    intro O O' h
    ext y
    have := Set.ext_iff.mp h (g y)
    simpa only [Set.mem_preimage, hfg] using this
  have himg : (fun O : Set α => f ⁻¹' O) '' {O | ∃ a ∈ Y, O = {b | b ∈ Y ∧ R' a b}} =
      {O | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} := by
    ext O
    constructor
    · rintro ⟨O', ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨g y, (hX (g y)).mp (by rw [hfg]; exact hy), ?_⟩
      ext c
      rw [← hfg y]
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hX, hR, hgf]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨{b | b ∈ Y ∧ R' (f a) b}, ⟨f a, (hX a).mpr ha, rfl⟩, ?_⟩
      ext c
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hX, hR]
  unfold Cnt.cntCl
  rw [← himg, hinj.injOn.encard_image]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem XS_map {T : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F : FlagG (VS D) D.R.rS T) : XS D (mapF γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (XS D F) := by
  unfold XS Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨x • F.e a, ⟨a, x, hx, rfl⟩, by simp [mapF]⟩
  · rintro ⟨_, ⟨a, x, hx, rfl⟩, rfl⟩
    exact ⟨a, x, hx, by simp [mapF]⟩

theorem FrameOK_map {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F' : LFlag (D.sp.Y 0) D.R.rS T'} (h : FrameOK D Λ F') :
    FrameOK D (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F') := by
  unfold FrameOK at h ⊢
  refine ⟨IsFixedConv_map hγ h.1, ?_⟩
  rw [XLam_mapL hγ, h.2]
  exact (XS_map hγ F'.fl).symm

end PI.RepsIndep.Tr

namespace PI.RepsIndep

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.UniformConstantsAndStatements

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end PI.RepsIndep
