module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueIsometryFixingBothFramesOfFrameAdapt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatible
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GdatIota
open Formalism.L2.SG.Pf GlobalTheory.StabCnt

variable {D : D7} {T T' : D.host.E}

theorem mem_gmap' (φ : GV D) (M : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap φ M ↔ φ.symm x ∈ M := by
  rw [← gmap_apply_mem φ M, LinearEquiv.apply_symm_apply]

theorem xlam_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    XLam (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (XLam M A) := by
  rw [XLam, XLam, gmap_inf', gmap_toO, adapt_xsp h]

theorem lrep_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lrep (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lrep M A) := by
  rw [Lrep, Lrep, gmap_inf', gmap_toO, adapt_orth h]

theorem lsub_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lsub M A) := by
  rw [Lsub, Lsub, lrep_adapt h, gmap_inf', gmap_sup', gmap_toO, gmap_toO, adapt_xsp h, adapt_orth h]

theorem ngx_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {A' B' : LFlag (D.sp.Y 0) D.R.rS T'} {φ : GV D} (h : Adapt φ A B)
    (h' : Adapt φ A' B') (M : LV D) (n : ℕ) :
    NgX (Formalism.HermitianLatticesTheory.gmap φ M) n B B' = Formalism.HermitianLatticesTheory.gmap φ (NgX M n A A') := by
  rw [NgX, NgX, gmap_sup', gmap_sup', gmap_ideal_smul, xlam_adapt h, xlam_adapt h']

theorem aut_lrep {F : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  have := lrep_adapt hA.1 M
  rw [hA.2] at this
  rw [← gmap_apply_mem A (Lrep M F) x, ← this]

theorem aut_lrep_symm {F : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A.symm x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  rw [← aut_lrep hA (A.symm x), LinearEquiv.apply_symm_apply]

theorem lsub_eq {F : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {A h : GV D} (hA : A ∈ Aut0 F M) (hh : Adapt h F F)
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F) : Lsub (Formalism.HermitianLatticesTheory.gmap h M) F = Lsub M F := by
  rw [lsub_adapt hh]
  ext y
  rw [mem_gmap']
  constructor
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    have hy2 : y ∈ orth (VS D) (Xsp F) := by
      have := mem_of_map_eq (adapt_orth hh) hy'
      rwa [LinearEquiv.apply_symm_apply] at this
    refine ⟨?_, hy2⟩
    have e2 : y = A l + ((h l - A l) + h ξ) := by
      have : y = h (l + ξ) := by rw [e, LinearEquiv.apply_symm_apply]
      rw [this, map_add (f := _)]; abel
    rw [e2]
    exact Submodule.add_mem_sup ((aut_lrep hA l).2 hl)
      (show _ ∈ Xsp F from add_mem (hc l hl.2) (mem_of_map_eq (adapt_xsp hh) hξ))
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    refine ⟨?_, symm_mem_of_map_eq (adapt_orth hh) hy'⟩
    have hm := (aut_lrep_symm hA l).2 hl
    have h1 := hc _ hm.2
    rw [LinearEquiv.apply_symm_apply] at h1
    have e2 : h.symm y = A.symm l + h.symm (ξ - (h (A.symm l) - l)) := by
      rw [← e]; simp only [map_add (f := _), map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [e2]
    exact Submodule.add_mem_sup hm
      (show _ ∈ Xsp F from symm_mem_of_map_eq (adapt_xsp hh) (sub_mem (show ξ ∈ Xsp F from hξ) h1))

theorem ngx_shift {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'} {M : LV D} {n : ℕ}
    {l m l' m' : (VS D).V} (hl : l ∈ Lrep M F) (hm : m ∈ Lrep M F) (hl' : l' ∈ Lrep M F') (hm' : m' ∈ Lrep M F')
    (h1 : l - m ∈ Xsp F) (h2 : l' - m' ∈ Xsp F') (h : m - m' ∈ NgX M n F F') : l - l' ∈ NgX M n F F' := by
  have e : l - l' = (m - m') + (l - m) - (l' - m') := by abel
  rw [e]
  refine sub_mem (add_mem h ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨M.sub_mem hl.1 hm.1, h1⟩)
  · exact Submodule.mem_sup_right ⟨M.sub_mem hl'.1 hm'.1, h2⟩

theorem gdat_iff {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'} {M : LV D} {A A' h : GV D}
    (hA : A ∈ Aut0 F M) (hA' : A' ∈ Aut0 F' M) (hh : Adapt h F F) (hh' : Adapt h F' F')
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F)
    (hc' : ∀ x ∈ orth (VS D) (Xsp F'), h x - A' x ∈ Xsp F') :
    gdat F F' (Formalism.HermitianLatticesTheory.gmap h M) = gdat F F' M ↔
      ∀ x' ∈ Lrep M F', ∀ l ∈ Lrep M F,
        (l - x' ∈ NgX M (gS D) F F' ↔ A l - A' x' ∈ NgX M (gS D) F F') := by
  have hG : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - A' l' ∈ Xsp F' ∧ p.2 - A l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := by
    intro p
    show (∃ l' ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F', ∃ l ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F, p.1 - l' ∈ Xsp F' ∧
      p.2 - l ∈ Xsp F ∧ l - l' ∈ NgX (Formalism.HermitianLatticesTheory.gmap h M) (gS D) F F') ↔ _
    rw [lrep_adapt hh, lrep_adapt hh', ngx_adapt hh hh']
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := h.surjective l'
      obtain ⟨m, rfl⟩ := h.surjective l
      rw [gmap_apply_mem] at hl hl'
      rw [← map_sub, gmap_apply_mem] at h3
      refine ⟨m', hl', m, hl, ?_, ?_, h3⟩
      · simpa using add_mem h1 (hc' m' hl'.2)
      · simpa using add_mem h2 (hc m hl.2)
    · rintro ⟨m', hl', m, hl, h1, h2, h3⟩
      refine ⟨h m', (gmap_apply_mem _ _ _).2 hl', h m, (gmap_apply_mem _ _ _).2 hl, ?_, ?_, ?_⟩
      · simpa using sub_mem h1 (hc' m' hl'.2)
      · simpa using sub_mem h2 (hc m hl.2)
      · rw [← map_sub, gmap_apply_mem]; exact h3
  have hG0 : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' M).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - l' ∈ Xsp F' ∧ p.2 - l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := fun p => Iff.rfl
  constructor
  · intro he x' hx' l hl
    have hx2 := (aut_lrep hA' x').2 hx'
    have hl2 := (aut_lrep hA l).2 hl
    constructor
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' M).2.2 := by
        rw [← he, hG]
        exact ⟨x', hx', l, hl, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG0 _).1 this
      exact ngx_shift hl2 hm hx2 hm' h2 h1 h3
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 := by
        rw [he, hG0]
        exact ⟨A' x', hx2, A l, hl2, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG _).1 this
      have h1' := symm_mem_of_map_eq (adapt_xsp hA'.1) h1
      have h2' := symm_mem_of_map_eq (adapt_xsp hA.1) h2
      simp only [map_sub, LinearEquiv.symm_apply_apply] at h1' h2'
      exact ngx_shift hl hm hx' hm' h2' h1' h3
  · intro hR
    refine Prod.ext (lsub_eq hA hh hc) (Prod.ext (lsub_eq hA' hh' hc') ?_)
    ext p
    rw [hG, hG0]
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      exact ⟨A' l', (aut_lrep hA' l').2 hl', A l, (aut_lrep hA l).2 hl, h1, h2, (hR l' hl' l hl).1 h3⟩
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := A'.surjective l'
      obtain ⟨m, rfl⟩ := A.surjective l
      rw [aut_lrep hA'] at hl'
      rw [aut_lrep hA] at hl
      exact ⟨m', hl', m, hl, h1, h2, (hR m' hl' m hl).2 h3⟩

theorem aut_conj {A B : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {g b : GV D} (hg : Adapt g A B) (hb : b ∈ Aut0 A M) :
    g * b * g⁻¹ ∈ Aut0 B (Formalism.HermitianLatticesTheory.gmap g M) := by
  refine ⟨?_, (conj_gmap g b M).2 hb.2⟩
  rw [mul_assoc]
  exact adapt_mul (adapt_mul (adapt_inv hg) hb.1) hg

theorem gdat_iff_iotaCompat : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h b₁ b₂ : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → b₁ ∈ Aut0 F0 lam → b₂ ∈ Aut0 F0' lam' → h ∈ H0 F F' → (∀ x ∈ orth (VS D) (Xsp F), h x - (g * b₁ * g⁻¹) x ∈ Xsp F) → (∀ x ∈ orth (VS D) (Xsp F'), h x - (g * γ * b₂ * γ⁻¹ * g⁻¹) x ∈ Xsp F') → (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ ↔ IotaCompat lam F0 (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') (b₁ * γ * b₂⁻¹ * γ⁻¹) (gS D)) := by
  intro D T T' F0 F F0' F' lam lam' Λ γ g h b₁ b₂ hγ hlam hg hg' hΛ hb₁ hb₂ hh hc hc'
  have hγa : Adapt γ F0' (mapLF γ F0') := adapt_mapLF hγ
  have hc₂ : γ * b₂ * γ⁻¹ ∈ Aut0 (mapLF γ F0') lam := by
    have := aut_conj hγa hb₂
    rwa [hlam] at this
  have hA := aut_conj hg hb₁
  have hA' := aut_conj hg' hc₂
  have e1 : g * γ * b₂ * γ⁻¹ * g⁻¹ = g * (γ * b₂ * γ⁻¹) * g⁻¹ := by group
  rw [e1] at hc'
  subst hΛ
  rw [gdat_iff hA hA' (frameAdaptedIsometry_of_fixing_both_frames hh).1 (frameAdaptedIsometry_of_fixing_both_frames hh).2 hc hc', lrep_adapt hg, lrep_adapt hg', ngx_adapt hg hg']
  have hi : b₁ * γ * b₂⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁.1.1 hγ) (Subgroup.inv_mem _ hb₂.1.1)
  have hβ : Adapt (b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹)) (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') :=
    adapt_mul (adapt_mul (adapt_inv hγa) hb₂.1) (adapt_mapLF hi)
  have e2 : b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹) = b₁ := by group
  rw [e2] at hβ
  have hN := ngx_adapt hb₁.1 hβ lam (gS D)
  rw [hb₁.2] at hN
  have e3 : b₁ * γ * b₂⁻¹ * γ⁻¹ = b₁ * (γ * b₂ * γ⁻¹)⁻¹ := by group
  unfold IotaCompat
  rw [hN, e3]
  generalize γ * b₂ * γ⁻¹ = c at hc₂ ⊢
  have e4 : ∀ x, (b₁ * c⁻¹) (c x) = b₁ x := fun x => by
    change b₁ (c.symm (c x)) = _
    rw [LinearEquiv.symm_apply_apply]
  constructor
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := c.surjective x'
    obtain ⟨m, rfl⟩ := b₁.surjective l
    rw [aut_lrep hc₂] at hx'
    rw [aut_lrep hb₁] at hl
    have := H (g y) ((gmap_apply_mem _ _ _).2 hx') (g m) ((gmap_apply_mem _ _ _).2 hl)
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem] at this
    rw [e4, ← map_sub, gmap_apply_mem]
    exact this.symm
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := g.surjective x'
    obtain ⟨m, rfl⟩ := g.surjective l
    rw [gmap_apply_mem] at hx' hl
    have := H (c y) ((aut_lrep hc₂ y).2 hx') (b₁ m) ((aut_lrep hb₁ m).2 hl)
    rw [e4, ← map_sub, gmap_apply_mem] at this
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem]
    exact this.symm

end GlobalTheory.GdatIota
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatibleStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerDatum_stable_iff_identifications_compatible : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h b₁ b₂ : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → b₁ ∈ Aut0 F0 lam → b₂ ∈ Aut0 F0' lam' → h ∈ H0 F F' → (∀ x ∈ orth (VS D) (Xsp F), h x - (g * b₁ * g⁻¹) x ∈ Xsp F) → (∀ x ∈ orth (VS D) (Xsp F'), h x - (g * γ * b₂ * γ⁻¹ * g⁻¹) x ∈ Xsp F') → (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ ↔ IotaCompat lam F0 (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') (b₁ * γ * b₂⁻¹ * γ⁻¹) (gS D)) := by
  first | exact @GlobalTheory.GdatIota.gdat_iff_iotaCompat | exact GlobalTheory.GdatIota.gdat_iff_iotaCompat | (intros; apply GlobalTheory.GdatIota.gdat_iff_iotaCompat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStabiliserFromAdaptedPair
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LsubGmapOfMapXspEq
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

private theorem orth_map_isom_eq_map_orth (D : D7) (φ : GV D) (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (U : Submodule D.host.E (VS D).V) :
    Formalism.MainNotions.S.Lat.orth (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) =
      (Formalism.MainNotions.S.Lat.orth (VS D) U).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have hi : ∀ x y, (VS D).hT (φ x) (φ y) = (VS D).hT x y := hφ
  ext v
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv
    refine (Submodule.mem_map).2 ⟨φ.symm v, ?_, by simp⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have h1 := hv (φ x) (Submodule.mem_map_of_mem hx)
    rw [← hi x (φ.symm v)]
    simpa using h1
  · intro hv x hx
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_map).1 hv
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_map).1 hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hw
    simp only [LinearEquiv.coe_coe]
    rw [hi]
    exact hw y hy

private theorem toO_map_eq_toO_map (D : D7) (φ : GV D) (U : Submodule D.host.E (VS D).V) :
    (Formalism.MainNotions.S.Lat.toO (VS D) U).map
              ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
      Formalism.MainNotions.S.Lat.toO (VS D) (U.map (φ : (VS D).V →ₗ[D.host.E] (VS D).V)) := by
  ext v
  simp only [Formalism.MainNotions.S.Lat.toO, Submodule.mem_map, Submodule.restrictScalars_mem,
    LinearMap.coe_restrictScalars]

theorem lsub_gmap_of_map_Xsp_eq :
    ∀ (D : D7) (T : D.host.E) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T) (φ : GV D) (M : LV D),
      φ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (Xsp F₁).map (φ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F₂ →
      Lsub (Formalism.HermitianLatticesTheory.gmap φ M) F₂ = Formalism.HermitianLatticesTheory.gmap φ (Lsub M F₁) := by
  intro D T F₁ F₂ φ M hφ hX
  have hinj : Function.Injective
      ((φ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := φ.injective
  unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_inf _ hinj, Submodule.map_sup, Submodule.map_inf _ hinj,
    toO_map_eq_toO_map, toO_map_eq_toO_map, ← orth_map_isom_eq_map_orth D φ hφ, hX]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStabiliserFromAdaptedPair
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7}

theorem onto_gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem onto_gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem onto_side {T : D.host.E} {A B : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {G h : GV D}
    (hG : Adapt G A B) (hh : Adapt h B B)
    (hL : Lsub (Formalism.HermitianLatticesTheory.gmap h (Formalism.HermitianLatticesTheory.gmap G M)) B = Lsub (Formalism.HermitianLatticesTheory.gmap G M) B)
    (hs : ∀ σ, Adapt σ A A → Lsub (Formalism.HermitianLatticesTheory.gmap σ M) A = Lsub M A →
      ∃ n ∈ NRat A, Formalism.HermitianLatticesTheory.gmap (n * σ) M = M) :
    ∃ n ∈ NRat A, n * (G⁻¹ * h * G) ∈ Aut0 A M ∧
      ∀ x ∈ orth (VS D) (Xsp B), h x - (G * (n * (G⁻¹ * h * G)) * G⁻¹) x ∈ Xsp B := by
  have hGi : Adapt G⁻¹ B A := adapt_inv hG
  have hσ : Adapt (G⁻¹ * h * G) A A := by
    have h2 : Adapt (G⁻¹ * (h * G)) A A := adapt_mul (adapt_mul hG hh) hGi
    rwa [mul_assoc]
  have hGiso : G ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hG.1
  have hmap : (Xsp A).map (G : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B := adapt_xsp hG

  have hinj : ∀ X Y : LV D, Formalism.HermitianLatticesTheory.gmap G X = Formalism.HermitianLatticesTheory.gmap G Y → X = Y := by
    intro X Y hXY
    have hXY' := congrArg (Formalism.HermitianLatticesTheory.gmap G⁻¹) hXY
    rwa [← onto_gmap_mul, ← onto_gmap_mul, inv_mul_cancel, onto_gmap_one, onto_gmap_one] at hXY'
  have e : G * (G⁻¹ * h * G) = h * G := by group
  have hLσ : Lsub (Formalism.HermitianLatticesTheory.gmap (G⁻¹ * h * G) M) A = Lsub M A := by
    apply hinj
    rw [← lsub_gmap_of_map_Xsp_eq D T A B G _ hGiso hmap, ← lsub_gmap_of_map_Xsp_eq D T A B G M hGiso hmap,
      ← onto_gmap_mul, e, onto_gmap_mul]
    exact hL
  obtain ⟨n, hn, hnM⟩ := hs _ hσ hLσ
  refine ⟨n, hn, ?_, ?_⟩
  · have hA : Adapt (n * (G⁻¹ * h * G)) A A := adapt_mul hσ (adapt_nrat hn)
    show Adapt _ A A ∧ Formalism.HermitianLatticesTheory.gmap _ M = M
    exact ⟨hA, hnM⟩
  · intro x hx

    obtain ⟨-, -, hm3⟩ := nrat_conj hG hn
    have hhx : h x ∈ orth (VS D) (Xsp B) := mem_of_map_eq (adapt_orth hh) hx
    have e' : G * (n * (G⁻¹ * h * G)) * G⁻¹ = G * n * G⁻¹ * h := by group
    rw [e']
    show h x - (G * n * G⁻¹) (h x) ∈ Xsp B
    rw [← neg_sub]
    exact neg_mem (hm3 (h x) hhx)

theorem stab_onto : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → (∀ σ, Adapt σ F0 F0 → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam) F0 = Lsub lam F0 → ∃ n ∈ NRat F0, Formalism.HermitianLatticesTheory.gmap (n * σ) lam = lam) → (∀ σ, Adapt σ F0' F0' → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam') F0' = Lsub lam' F0' → ∃ n ∈ NRat F0', Formalism.HermitianLatticesTheory.gmap (n * σ) lam' = lam') → h ∈ stabL F F' Λ → ∃ b, GlobalTheory.StabCnt.InB F0 F0' lam lam' γ b ∧ GlobalTheory.StabCnt.Corr F0 F F0' F' γ g b h := by
  intro D T T' F0 F F0' F' lam lam' Λ γ g h hγ hlam hg hg' hΛ hs hs' hstab
  obtain ⟨hH0, hdat⟩ := hstab
  have hL1 : Lsub (Formalism.HermitianLatticesTheory.gmap h Λ) F = Lsub Λ F := congrArg Prod.fst hdat
  have hL2 : Lsub (Formalism.HermitianLatticesTheory.gmap h Λ) F' = Lsub Λ F' := congrArg (fun p => p.2.1) hdat
  obtain ⟨hhF, hhF'⟩ := frameAdaptedIsometry_of_fixing_both_frames hH0
  have hgγ : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have e2 : Formalism.HermitianLatticesTheory.gmap (g * γ) lam' = Λ := by rw [onto_gmap_mul, hlam, hΛ]
  obtain ⟨n, hn, hb1, hx1⟩ := onto_side (M := lam) hg hhF (by rw [← hΛ]; exact hL1) hs
  obtain ⟨n', hn', hb2, hx2⟩ := onto_side (M := lam') hgγ hhF' (by rw [e2]; exact hL2) hs'

  have key : n * (g⁻¹ * h * g) * γ * (n' * ((g * γ)⁻¹ * h * (g * γ)))⁻¹ = n * γ * n'⁻¹ := by group
  have e3 : g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * γ⁻¹ * g⁻¹ =
      g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * (g * γ)⁻¹ := by group
  have hx2' : ∀ x ∈ orth (VS D) (Xsp F'),
      h x - (g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * γ⁻¹ * g⁻¹) x ∈ Xsp F' := by
    rw [e3]; exact hx2
  have hI := (GlobalTheory.T.innerDatum_stable_iff_identifications_compatible D T T' F0 F F0' F' lam lam' Λ γ g h (n * (g⁻¹ * h * g))
    (n' * ((g * γ)⁻¹ * h * (g * γ))) hγ hlam hg hg' hΛ hb1 hb2 hH0 hx1 hx2').mp hdat
  have e4 : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) = 1 := by group
  have hF : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) ∈ NRat F := by rw [e4]; exact nrat_one F
  have hF' : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) ∈ NRat F' := by rw [e4]; exact nrat_one F'
  have hKey : KeyEq F0 F0' lam γ (n * (g⁻¹ * h * g) * γ * (n' * ((g * γ)⁻¹ * h * (g * γ)))⁻¹) :=
    ⟨⟨n, hn, n'⁻¹, nrat_inv hn', key⟩, hI⟩
  refine ⟨(n * (g⁻¹ * h * g), n' * ((g * γ)⁻¹ * h * (g * γ))), ?_, ?_⟩
  · exact ⟨hb1, hb2, hKey⟩
  · exact ⟨hH0, n, hn, n'⁻¹, nrat_inv hn', key, hF, hF'⟩

end GlobalTheory.StabCnt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStabiliserFromAdaptedPairStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerDatumStabiliser_from_adapted_pair : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → (∀ σ, Adapt σ F0 F0 → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam) F0 = Lsub lam F0 → ∃ n ∈ NRat F0, Formalism.HermitianLatticesTheory.gmap (n * σ) lam = lam) → (∀ σ, Adapt σ F0' F0' → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam') F0' = Lsub lam' F0' → ∃ n ∈ NRat F0', Formalism.HermitianLatticesTheory.gmap (n * σ) lam' = lam') → h ∈ stabL F F' Λ → ∃ b, GlobalTheory.StabCnt.InB F0 F0' lam lam' γ b ∧ GlobalTheory.StabCnt.Corr F0 F F0' F' γ g b h := by
  first | exact @GlobalTheory.StabCnt.stab_onto | exact GlobalTheory.StabCnt.stab_onto | (intros; apply GlobalTheory.StabCnt.stab_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardStabilizerInnerDatumRowDoubleCoset
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7} {T T' : D.host.E}

theorem mul_mem_isometriesFixingBothFrames {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'} {h k : GV D} (hh : h ∈ H0 F F')
    (hk : k ∈ H0 F F') : h * k ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hh.1 hk.1, fun a => by rw [le_mul_app, hk.2.1 a, hh.2.1 a],
    fun a => by rw [le_mul_app, hk.2.2 a, hh.2.2 a]⟩

theorem principalPolarisation_exists_unique_section (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') : (1 : GV D) ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun _ => rfl, fun _ => rfl⟩

theorem nlam_iff_nrat {F0 : LFlag (D.sp.Y 0) D.R.rS T} {lam : LV D} {b : GV D} (hb : b ∈ Aut0 F0 lam) :
    b ∈ NLam lam F0 ↔ b ∈ NRat F0 :=
  ⟨fun h => ⟨h.1.1, h.2.1, h.2.2⟩, fun h => ⟨⟨h.1, hb.2⟩, h.2.1, h.2.2⟩⟩

section Corr

variable {F0 F : LFlag (D.sp.Y 0) D.R.rS T} {F0' F' : LFlag (D.sp.Y 0) D.R.rS T'} {γ g : GV D}

theorem s_adapt (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
    {b₁ b₂ n n' : GV D} (hb1 : Adapt b₁ F0 F0) (hb2 : Adapt b₂ F0' F0') (hn : n ∈ NRat F0) (hn' : n' ∈ NRat F0')
    (he : b₁ * γ * b₂⁻¹ = n * γ * n') :
    Adapt (g * n⁻¹ * b₁ * g⁻¹) F F ∧ Adapt (g * n⁻¹ * b₁ * g⁻¹) F' F' ∧
      g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
  have e1 : n⁻¹ * b₁ = γ * n' * b₂ * γ⁻¹ := by
    calc n⁻¹ * b₁ = n⁻¹ * (b₁ * γ * b₂⁻¹) * b₂ * γ⁻¹ := by group
      _ = n⁻¹ * (n * γ * n') * b₂ * γ⁻¹ := by rw [he]
      _ = γ * n' * b₂ * γ⁻¹ := by group
  have hseq : g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
    calc g * n⁻¹ * b₁ * g⁻¹ = g * (n⁻¹ * b₁) * g⁻¹ := by group
      _ = g * (γ * n' * b₂ * γ⁻¹) * g⁻¹ := by rw [e1]
      _ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by group
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  refine ⟨adapt_mul (adapt_inv hg) (adapt_mul hb1 (adapt_mul (adapt_nrat (nrat_inv hn)) hg)), ?_, hseq⟩
  rw [hseq]
  exact adapt_mul (adapt_inv hG) (adapt_mul (adapt_mul hb2 (adapt_nrat hn')) hG)

theorem cong_mod {A0 A : LFlag (D.sp.Y 0) D.R.rS T} {a s μ n b : GV D} (ha : Adapt a A0 A) (hs : Adapt s A A)
    (hμ : μ ∈ NRat A) (hn : n ∈ NRat A0) (hb : Adapt b A0 A0) (hseq : s = a * (n * b) * a⁻¹) :
    ∀ x ∈ orth (VS D) (Xsp A), (s * μ⁻¹) x - (a * b * a⁻¹) x ∈ Xsp A := by
  intro x hx
  have e : (s * μ⁻¹) x - (a * b * a⁻¹) x = s (μ⁻¹ x - x) + a (n (b (a⁻¹ x)) - b (a⁻¹ x)) := by
    rw [hseq]
    simp only [le_mul_app, map_sub]
    abel
  rw [e]
  refine add_mem (mem_of_map_eq (adapt_xsp hs) ((nrat_inv hμ).2.2 x hx)) ?_
  refine mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ ?_)
  exact mem_of_map_eq (adapt_orth hb) (symm_mem_of_map_eq (adapt_orth ha) hx)

variable (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
  (hI : ∀ s, Adapt s F F → Adapt s F' F' → ∃! h, h ∈ H0 F F' ∧ h⁻¹ * s ∈ NRat F ∧ h⁻¹ * s ∈ NRat F')
include hγ hg hg'

include hI in
theorem corr_exists {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) :
    ∃ h, Corr F0 F F0' F' γ g b h := by
  obtain ⟨⟨n, hn, n', hn', he⟩, -⟩ := hb.2.2
  obtain ⟨hs1, hs2, -⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  obtain ⟨h, ⟨hh, h1, h2⟩, -⟩ := hI _ hs1 hs2
  exact ⟨h, hh, n, hn, n', hn', he, h1, h2⟩

include hI in
theorem corr_unique {b : GV D × GV D} (hb1 : Adapt b.1 F0 F0) (hb2 : Adapt b.2 F0' F0') {h k : GV D}
    (hh : Corr F0 F F0' F' γ g b h) (hk : Corr F0 F F0' F' γ g b k) : h = k := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', he2, k1, k2⟩ := hk
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb1 hb2 hn hn' he
  obtain ⟨-, -, hteq⟩ := s_adapt hγ hg hg' hb1 hb2 hm hm' he2
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have tF : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (g * b.1⁻¹) * (m * n⁻¹) * (g * b.1⁻¹)⁻¹ := by group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb1) hg) (nrat_mul hm (nrat_inv hn))
  have tF' : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F' := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) =
        ((g * γ) * b.2⁻¹) * (m'⁻¹ * n') * ((g * γ) * b.2⁻¹)⁻¹ := by rw [hseq, hteq]; group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb2) hG) (nrat_mul (nrat_inv hm') hn')
  obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
  have ek : k⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (k⁻¹ * (g * m⁻¹ * b.1 * g⁻¹)) * ((g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) := by group
  rw [hu h ⟨hh0, h1, h2⟩, hu k ⟨hk0, by rw [ek]; exact nrat_mul k1 tF, by rw [ek]; exact nrat_mul k2 tF'⟩]

theorem corr_mul {lam lam' : LV D} {b c : GV D × GV D} (hb : InB F0 F0' lam lam' γ b)
    (hc : InB F0 F0' lam lam' γ c) {h k : GV D} (hh : Corr F0 F F0' F' γ g b h)
    (hk : Corr F0 F F0' F' γ g c k) : Corr F0 F F0' F' γ g (b * c) (h * k) := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', hec, k1, k2⟩ := hk
  have hk1 := (frameAdaptedIsometry_of_fixing_both_frames hk0).1
  have hk2 := (frameAdaptedIsometry_of_fixing_both_frames hk0).2
  refine ⟨mul_mem_isometriesFixingBothFrames hh0 hk0, b.1 * m * b.1⁻¹ * n, nrat_mul (nrat_conj hb.1.1 hm) hn,
    n' * (b.2 * m' * b.2⁻¹), nrat_mul hn' (nrat_conj hb.2.1.1 hm'), ?_, ?_, ?_⟩
  · show b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = _
    calc b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = b.1 * (c.1 * γ * c.2⁻¹) * b.2⁻¹ := by group
      _ = b.1 * (m * γ * m') * b.2⁻¹ := by rw [hec]
      _ = b.1 * m * b.1⁻¹ * (b.1 * γ * b.2⁻¹) * (b.2 * m' * b.2⁻¹) := by group
      _ = b.1 * m * b.1⁻¹ * (n * γ * n') * (b.2 * m' * b.2⁻¹) := by rw [he]
      _ = _ := by group
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk1) h1) k1
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk2) h2) k2

theorem corr_stab {lam lam' Λ : LV D} (hγl : Formalism.HermitianLatticesTheory.gmap γ lam' = lam) (hΛ : Λ = Formalism.HermitianLatticesTheory.gmap g lam)
    {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D} (hh : Corr F0 F F0' F' γ g b h) :
    h ∈ stabL F F' Λ := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have hh' : h = (g * n⁻¹ * b.1 * g⁻¹) * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹))⁻¹ := by group
  refine ⟨hh0, (GlobalTheory.T.innerDatum_stable_iff_identifications_compatible D T T' F0 F F0' F' lam lam' Λ γ g h b.1 b.2 hγ hγl hg hg' hΛ hb.1 hb.2.1 hh0
    ?_ ?_).2 hb.2.2.2⟩
  · intro x hx
    rw [hh']
    exact cong_mod hg hs1 h1 (nrat_inv hn) hb.1.1 (by group) x hx
  · intro x hx
    rw [hh', show g * γ * b.2 * γ⁻¹ * g⁻¹ = (g * γ) * b.2 * (g * γ)⁻¹ by group]
    exact cong_mod hG hs2 h2 hn' hb.2.1.1 hseq x hx

include hI in
theorem corr_ker {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D}
    (hh : Corr F0 F F0' F' γ g b h) : h = 1 ↔ b.1 ∈ NLam lam F0 ∧ b.2 ∈ NLam lam' F0' := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  rw [nlam_iff_nrat hb.1, nlam_iff_nrat hb.2.1]
  constructor
  · rintro rfl
    rw [inv_one, one_mul] at h1 h2
    constructor
    · have c := nrat_conj (adapt_inv hg) h1
      have e : g⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) * g⁻¹⁻¹ = n⁻¹ * b.1 := by group
      rw [e] at c
      have := nrat_mul hn c
      rwa [mul_inv_cancel_left] at this
    · rw [hseq] at h2
      have c := nrat_conj (adapt_inv hG) h2
      have e : (g * γ)⁻¹ * ((g * γ) * (n' * b.2) * (g * γ)⁻¹) * (g * γ)⁻¹⁻¹ = n' * b.2 := by group
      rw [e] at c
      have := nrat_mul (nrat_inv hn') c
      rwa [inv_mul_cancel_left] at this
  · rintro ⟨c1, c2⟩
    have sF : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F := by
      have e : g * n⁻¹ * b.1 * g⁻¹ = g * (n⁻¹ * b.1) * g⁻¹ := by group
      rw [e]; exact nrat_conj hg (nrat_mul (nrat_inv hn) c1)
    have sF' : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F' := by
      rw [hseq]; exact nrat_conj hG (nrat_mul hn' c2)
    obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
    rw [hu h ⟨hh0, h1, h2⟩, hu 1 ⟨principalPolarisation_exists_unique_section F F', by rwa [inv_one, one_mul], by rwa [inv_one, one_mul]⟩]

end Corr

theorem card_of_hom {G : Type*} [Group G] {B : Subgroup (G × G)} {N N' : Subgroup G} (φ : B →* G) (S : Set G)
    (hR : ∀ h, h ∈ φ.range ↔ h ∈ S) (hK : ∀ b : B, φ b = 1 ↔ (b : G × G).1 ∈ N ∧ (b : G × G).2 ∈ N') :
    Nat.card S = (N.prod N').relIndex B := by
  have hker : φ.ker = (N.prod N').subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_prod, hK]
  have e1 : Nat.card S = Nat.card φ.range :=
    Nat.card_congr (Equiv.subtypeEquivRight fun h => (hR h).symm)
  rw [e1, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, Subgroup.relIndex, ← hker]
  rfl

theorem stab_card : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∀ (B : Subgroup (GV D × GV D)) (N N' : Subgroup (GV D)), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) → (N : Set (GV D)) = NLam t.lam (lf D (X.Fu u)) → (N' : Set (GV D)) = NLam t.lam' (lf D (X.Fu u')) → Nat.card (stabL F F' Λ) = (N.prod N').relIndex B := by
  intro D X Y u u' F F' w hZ hG t Λ hTG B N N' hB hN hN'
  obtain ⟨g, hg, hg', hΛ⟩ := hTG
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hg2 : Adapt g (mapLF t.lin (lf D (X.Fu u'))) F' := hg'
  have hI := GlobalTheory.T.existsUnique_isometryFixingBothFrames_of_frameAdapted D X Y u u' F F' w hZ hG
  have hB' : ∀ b, b ∈ B ↔ InB (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lam' t.lin b := hB
  have hf : ∀ b : B, ∃ h, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) h :=
    fun b => corr_exists hγ hg hg2 hI ((hB' b).1 b.2)
  let f : B → GV D := fun b => Classical.choose (hf b)
  have hfs : ∀ b : B, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) (f b) :=
    fun b => Classical.choose_spec (hf b)
  have hAd : ∀ b : B, Adapt (b : GV D × GV D).1 (lf D (X.Fu u)) (lf D (X.Fu u)) ∧
      Adapt (b : GV D × GV D).2 (lf D (X.Fu u')) (lf D (X.Fu u')) :=
    fun b => ⟨((hB' b).1 b.2).1.1, ((hB' b).1 b.2).2.1.1⟩
  let φ : B →* GV D := MonoidHom.mk' f fun b c =>
    corr_unique hγ hg hg2 hI (hAd (b * c)).1 (hAd (b * c)).2 (hfs (b * c))
      (corr_mul hγ hg hg2 ((hB' b).1 b.2) ((hB' c).1 c.2) (hfs b) (hfs c))
  refine card_of_hom φ _ (fun h => ⟨?_, fun hh => ?_⟩) (fun b => ?_)
  · rintro ⟨b, rfl⟩
    exact corr_stab hγ hg hg2 hγl hΛ ((hB' b).1 b.2) (hfs b)
  · have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 _ t.mem
    have hrow' : IsRowLat D (X.Fu u') t.lam' := (Y.rowsOK u').1 _ t.mem'
    obtain ⟨b, hbB, hbC⟩ := GlobalTheory.T.innerDatumStabiliser_from_adapted_pair D _ _ (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lam t.lam' Λ t.lin g h
      hγ hγl hg hg2 hΛ (fun σ hσ hL => GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu u) t.lam t.lam σ hrow hrow hσ hL)
      (fun σ hσ hL => GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu u') t.lam' t.lam' σ hrow' hrow' hσ hL) hh
    refine ⟨⟨b, (hB' b).2 hbB⟩, ?_⟩
    exact corr_unique hγ hg hg2 hI hbB.1.1 hbB.2.1.1 (hfs _) hbC
  · have hK := corr_ker hγ hg hg2 hI ((hB' b).1 b.2) (hfs b)
    show f b = 1 ↔ _
    rw [hK]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show _ ∈ (N : Set (GV D)); rw [hN]; exact h1
      · show _ ∈ (N' : Set (GV D)); rw [hN']; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : (b : GV D × GV D).1 ∈ (N : Set (GV D)) := h1
        rwa [hN] at this
      · have : (b : GV D × GV D).2 ∈ (N' : Set (GV D)) := h2
        rwa [hN'] at this

end GlobalTheory.StabCnt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardStabilizerInnerDatumRowDoubleCosetStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_stabilizer_innerDatum_rowDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∀ (B : Subgroup (GV D × GV D)) (N N' : Subgroup (GV D)), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) → (N : Set (GV D)) = NLam t.lam (lf D (X.Fu u)) → (N' : Set (GV D)) = NLam t.lam' (lf D (X.Fu u')) → Nat.card (stabL F F' Λ) = (N.prod N').relIndex B := by
  first | exact @GlobalTheory.StabCnt.stab_card | exact GlobalTheory.StabCnt.stab_card | (intros; apply GlobalTheory.StabCnt.stab_card <;> assumption)
end
