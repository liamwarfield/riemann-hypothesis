module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueIsLatticeUnimodular
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Glue

open GlobalTheory.LoopC.RowGlue

theorem glue_isLattice_unimodular : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → Submodule.IsLattice D.host.E (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := by
  intro D large₂ X _ L hL hU
  have H : IsHypFrame (VS D).hT X.eX X.fY := ⟨(VS D).herm, X.ee, X.ff, X.ef⟩
  have h0 : ∀ a, aaD D a ≠ 0 := fun a => zpow_ne_zero _ (ddS_ne_zero D)
  have hs : ∀ a, StarStable (aaD D a) := fun a => (ddS_stable D).zpow (ddS_ne_zero D) _
  have hmid : ∀ w ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)),
      Mid (VS D).hT X.eX X.fY w := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  refine ⟨Submodule.IsLattice.of_fg D.host.E (((sumS_fg _ _).sup (hL.fg.map _)).sup (sumS_fg _ _)), (H.unimodular_iff (A := fun a => aaD D a) (B := fun a => (aaD D a)⁻¹) hmid
      (fun a => inv_ne_zero (h0 a)) (fun a => (hs a).inv (h0 a)) (fun a => (inv_inv _).symm)).2 ?_⟩
  · intro w hw
    have key : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L ↔
        (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ L := by
      rw [show Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L = L from hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at key ⊢
    constructor
    · intro h
      exact ⟨⟨w, hw⟩, key.1 fun y hy => h y ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w', hw', e⟩ _ ⟨y, hy, rfl⟩
      have e' : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) = w' := Subtype.ext e.symm
      exact key.2 (e' ▸ hw') y hy

end GlobalTheory.RowsOrb.Glue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemGenusOfIsUnimodular
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.ExGenus

open Formalism.HermitianLatticesTheory

private theorem full_of_unimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hu : IsUnimodular h L) :
    Submodule.IsFullLattice K L := by
  letI := hL
  refine { span_eq_top := ?_ }
  let W := Submodule.span K (L : Set V)
  change W = ⊤
  by_contra hw
  let b := Module.finBasis K V
  let e : V ≃ₗ⋆[K] V := (b.equivFun.trans (starLinearEquiv K)).trans b.equivFun.symm
  let g : V →ₗ[K] Module.Dual K W :=
    (LinearMap.domRestrict' W).comp (h.comp e.toLinearMap)
  have hd : Module.finrank K (Module.Dual K W) < Module.finrank K V := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt hw
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hd)
  have hm (a : K) : a • e x ∈ L := by
    rw [← hu, dualBasic_mem_dual]
    intro y hy
    have hz : h (e x) y = 0 :=
      congrArg (fun f : Module.Dual K W => f ⟨y, Submodule.subset_span hy⟩)
        (LinearMap.mem_ker.mp hx)
    have hz' : h y (e x) = 0 := by
      exact hs.eq_iff.mp hz
    simp [LinearMap.map_smul, hz']
  let i : K →ₗ[𝓞 K] L :=
    ((LinearMap.toSpanSingleton K _ (e x)).restrictScalars (𝓞 K)).codRestrict L hm
  letI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL.fg
  letI : Module.Finite (𝓞 K) K := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective K (fun hzero => hx0 (e.map_eq_zero_iff.mp hzero))
      (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField K
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))


theorem mem_genus_of_isUnimodular : ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.TypeAsm.Std D large₂ → ∀ (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 := by
  intro D large₂ hS _ _ Λ hΛ hU
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := (GlobalTheory.TypeAsm.hostC D large₂ hS).1

  have hloc : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E L →
      (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT L ↔
        ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt (VS D).hT P L) :=
    fun L hL => (Formalism.HermitianLatticesTheory.locDual (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT (VS D).herm
      Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range L hL.fg).2
  have hΛfull := full_of_unimodular (VS D).hT (VS D).herm hΛ hU
  have hL0full := full_of_unimodular (VS D).hT (VS D).herm
    (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular
  refine ⟨hΛfull, fun P hP => ?_⟩

  exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt D.host.E (VS D).V (VS D).hT hCM (VS D).herm
    (VS D).nondeg (VS D).L0 Λ hL0full hΛfull P hP
    ((hloc _ (VS D).standardTuple_isLattice).1 (VS D).baseLattice_isUnimodular P hP) ((hloc Λ hΛ).1 hU P hP)

end GlobalTheory.RowsOrb.ExGenus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PartsOfLat
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Parts
open GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

theorem lsS_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ latSpanS aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  have hle : latSpanS aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, x, -, rfl⟩
    exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)
  exact hle hy

theorem Xsp_eq (u : D.what₂.Word) : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem XS_eq (u : D.what₂.Word) : XS D (X.Fu u) = latSpanS (fun a => aaD D a) X.eX := by
  simp only [XS, latSpanS, aaD, X.Fu_e]

theorem xlam_split (u : D.what₂.Word) (M : Submodule (𝓞 D.host.E) (VS D).V)
    (hM : ∀ x ∈ M, ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) :
    XLam (latSpanS (fun a => aaD D a) X.eX ⊔ M ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) =
      XS D (X.Fu u) := by
  rw [XS_eq]
  show _ ⊓ toO (VS D) (Xsp (lf D (X.Fu u))) = _
  rw [Xsp_eq]
  refine le_antisymm ?_ (le_inf (le_sup_left.trans le_sup_left) fun y hy => lsS_le _ _ hy)
  rintro y ⟨hyΛ, hyX⟩
  have hyX' : y ∈ Submodule.span D.host.E (Set.range X.eX) := hyX
  obtain ⟨y1, hy1, b, hb, rfl⟩ := Submodule.mem_sup.mp hyΛ
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp hy1
  have haX := lsS_le _ _ ha
  have hbY := lsS_le _ _ hb

  have hb0 : b = 0 := by
    have hpair : ∀ c, (VS D).hT (X.eX c) b = 0 := by
      intro c
      have h1 := orth_span (fun d => X.ee c d) hyX'
      have h2 := orth_span (fun d => X.ee c d) haX
      rw [map_add (f := _), map_add (f := _), h2, (hM m hm c).1, zero_add, zero_add] at h1
      exact h1
    rw [coord X.ef hbY]
    simp [hpair]
  subst hb0
  rw [add_zero] at hyX' ⊢

  have hmX : m ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have := Submodule.sub_mem _ hyX' haX
    rwa [add_sub_cancel_left] at this
  have hm0 : m = 0 := by
    rw [coord (dual_symm GlobalTheory.RowsOrb.Uniq.hh X.ef) hmX]
    simp [(hM m hm _).2]
  rw [hm0, add_zero]
  exact ha

theorem map_perp (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    ∀ x ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)), ∀ a,
      (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0 := by
  intro x hx a
  obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hx
  exact (GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 a

theorem lmap_eq (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L := by
  ext w
  rw [lmap_char X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) (fun a => aaD D a) (fun a => (aaD D a)⁻¹) X.ef (map_perp X L)
      rfl w]
  constructor
  · rintro ⟨l, hl, hP⟩
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hl
    have hfix : P (VS D).hT X.eX X.fY (w' : (VS D).V) = w' := by
      rw [P_apply]
      simp [((GlobalTheory.RowsOrb.mem_Wb X (w' : (VS D).V)).mp w'.2 _).2]
    have : w' = w := Subtype.ext (hfix.symm.trans hP)
    exact this ▸ hw'
  · intro hw
    refine ⟨(w : (VS D).V), Submodule.mem_map_of_mem hw, ?_⟩
    rw [P_apply]
    simp [((GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 _).2]

end GlobalTheory.RowsOrb.Parts


open GlobalTheory.RowsOrb.Parts in
theorem GlobalTheory.RowsOrb.parts_of_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), XLam (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) = XS D (X.Fu u) ∧ XLam (VS D).L0 (lf D (X.Fu u)) = XS D (X.Fu u) ∧ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L ∧ ∀ w : GlobalTheory.RowsOrb.Wb X, (w : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) → w ∈ L := by
  intro D X u L
  refine ⟨xlam_split X u _ (map_perp X L), ?_, lmap_eq X u L, ?_⟩
  · rw [X.Lam_split]
    exact xlam_split X u X.Lb X.Lb_perp
  · intro w hw
    rw [Lsub, Submodule.mem_inf] at hw
    have hX : toO (VS D) (Xsp (lf D (X.Fu u))) =
        GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
      rw [GlobalTheory.RowsOrb.Uniq.fixedFrameOfWord_isotropicSpan_eq, Xsp_eq]
    have hmem : w ∈ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
        L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
        latSpanS (fun a => (aaD D a)⁻¹) X.fY) :=
      (GlobalTheory.RowsOrb.mem_Lmap X u _ w).mpr ((sup_le_sup inf_le_left hX.le) hw.1)
    rwa [lmap_eq X u L] at hmem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGzLmap
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.StabAct

open GlobalTheory.RowsOrb GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

abbrev Xs : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX)

theorem P_X {x : (VS D).V} (hx : x ∈ Xs X) : P (VS D).hT X.eX X.fY x = 0 := by
  have hdY := dual_symm hh X.ef
  rw [P_apply, ← coord hdY hx, sub_self]

theorem P_Wb {w : (VS D).V} (hw : w ∈ Wb X) : P (VS D).hT X.eX X.fY w = w := by
  rw [P_apply]; simp [((mem_Wb X w).1 hw _).2]

theorem sub_proj_mem₂ (v : (VS D).V) : v - P (VS D).hT X.eX X.fY v ∈ Xs X := by
  rw [P_apply, sub_sub_cancel]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

theorem orth_e (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hδ : ∀ x y, (VS D).hT (δ x) (δ y) = (VS D).hT x y)
    (hX : ∀ x ∈ Xs X, δ.symm x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) (a : Fin D.R.rS) :
    (VS D).hT (X.eX a) (δ w) = 0 := by
  rw [← δ.apply_symm_apply (X.eX a), hδ]
  exact GlobalTheory.RowsOrb.Basic.hT_span_left X.eX w (fun b => ((mem_Wb X w).1 hw b).1)
    (hX _ (Submodule.subset_span ⟨a, rfl⟩))

variable (X)

def gl (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hS : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (δ w) = 0) :
    Wb X →ₗ[D.host.E] Wb X :=
  LinearMap.codRestrict (Wb X) (P (VS D).hT X.eX X.fY ∘ₗ δ ∘ₗ (Wb X).subtype)
    (fun w a => P_mem X.ee (dual_symm hh X.ef) (hS _ w.2) a)

theorem gl_inv (δ ε : (VS D).V →ₗ[D.host.E] (VS D).V) (hεδ : ∀ v, ε (δ v) = v)
    (hε : ∀ x ∈ Xs X, ε x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) :
    P (VS D).hT X.eX X.fY (ε (P (VS D).hT X.eX X.fY (δ w))) = w := by
  have e : P (VS D).hT X.eX X.fY (δ w) = δ w - (δ w - P (VS D).hT X.eX X.fY (δ w)) := by abel
  rw [e, map_sub, hεδ, map_sub, P_X X (hε _ (sub_proj_mem₂ X _)), sub_zero, P_Wb X hw]

def ge (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h1 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ w) = 0)
    (h2 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ.symm w) = 0)
    (hX : ∀ x ∈ Xs X, γ x ∈ Xs X) (hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X) : Wb X ≃ₗ[D.host.E] Wb X :=
  LinearEquiv.ofLinear (gl X (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1)
    (gl X ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) h2)
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.apply_symm_apply v) hX w.2))
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.symm_apply_apply v) hX' w.2))

theorem transport (u : D.what₂.Word) (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hX : ∀ x ∈ Xs X, δ x ∈ Xs X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {v : (VS D).V}
    (hv : v ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X) :
    P (VS D).hT X.eX X.fY (δ v) ∈
      Λ.map (δ.restrictScalars (𝓞 D.host.E)) ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv
  rw [GlobalTheory.RowsOrb.Basic.mem_XO] at hx
  refine Submodule.mem_sup.2 ⟨δ l, Submodule.mem_map_of_mem hl,
    δ x - (δ (l + x) - P (VS D).hT X.eX X.fY (δ (l + x))), ?_, ?_⟩
  · rw [GlobalTheory.RowsOrb.Basic.mem_XO]
    exact Submodule.sub_mem _ (hX x hx) (sub_proj_mem₂ X _)
  · rw [map_add (f := _)]; abel

end GlobalTheory.RowsOrb.StabAct


open GlobalTheory.RowsOrb.StabAct GlobalTheory.RowsOrb.Uniq in
theorem GlobalTheory.RowsOrb.exists_gz_lmap : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∀ γ ∈ stabF D (X.Fu u),
    ∃ g : GlobalTheory.RowsOrb.Gz X u, ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
      g • GlobalTheory.RowsOrb.Lmap X u Λ = GlobalTheory.RowsOrb.Lmap X u (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  intro D X u γ hγ
  obtain ⟨hiso, hXa, hz⟩ := hγ
  have hδ : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := hiso
  have hδ' : ∀ x y, (VS D).hT (γ.symm x) (γ.symm y) = (VS D).hT x y := fun x y => by
    rw [← hδ, γ.apply_symm_apply, γ.apply_symm_apply]
  have hXr : (X.Fu u).Xa D.R.rS = Xs X := by
    simp only [FlagG.Xa, HidaSetting.Fu_e]
    congr 1
    ext v
    simp
  have hmap := hXa D.R.rS
  rw [hXr] at hmap
  have hX : ∀ x ∈ Xs X, γ x ∈ Xs X := fun x hx => by
    rw [← hmap]; exact Submodule.mem_map_of_mem hx
  have hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X := fun x hx => by
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have h1 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ hδ hX' hw a
  have h2 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ.symm hδ' (fun x hx => by simpa using hX x hx) hw a
  have hz' : γ (X.zu u) = X.zu u := by rw [← HidaSetting.flagZVector]; exact hz
  let e := ge X γ h1 h2 hX hX'
  have he : ∀ w, ((e w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ w) := fun w => rfl
  have he' : ∀ w, ((e.symm w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ.symm w) := fun w => rfl
  have hi : e ∈ Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X) := by
    intro x y
    rw [GlobalTheory.RowsOrb.hb_apply, GlobalTheory.RowsOrb.hb_apply, he, he, P_apply, P_apply,
      P_iso hh X.ee (orth_e γ hδ hX' x.2) (orth_e γ hδ hX' y.2), hδ]
  have hs : (⟨e, hi⟩ : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X)) ∈ GlobalTheory.RowsOrb.Gz X u := by
    rw [MulAction.mem_stabilizer_iff]
    show e (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u
    apply Subtype.ext
    rw [he, GlobalTheory.RowsOrb.zb_coe, hz']
    exact P_Wb X (GlobalTheory.RowsOrb.zb X u).2
  refine ⟨⟨⟨e, hi⟩, hs⟩, fun Λ => ?_⟩
  have hback : (Formalism.HermitianLatticesTheory.gmap γ Λ).map
      (((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars
        (𝓞 D.host.E)) = Λ := by
    ext v
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hv
      exact ⟨γ v, ⟨v, hv, rfl⟩, by simp⟩
  show Formalism.HermitianLatticesTheory.gmap e (GlobalTheory.RowsOrb.Lmap X u Λ) = _
  ext w'
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := transport X u (γ : (VS D).V →ₗ[D.host.E] (VS D).V) hX Λ ((GlobalTheory.RowsOrb.mem_Lmap X u Λ w).1 hw)
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
  · intro hw'
    refine ⟨e.symm w', ?_, e.apply_symm_apply w'⟩
    have h := transport X u ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hX'
      (Formalism.HermitianLatticesTheory.gmap γ Λ) ((GlobalTheory.RowsOrb.mem_Lmap X u _ w').1 hw')
    rw [hback] at h
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowOfUnimodularLatticePrimitiveVector
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RowsOrb.exists_row_of_unimod : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) → ∃ Λ ∈ Y.what₂ u, ∃ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ = L := by
  intro D large₂ X Y u hStd L hL hU hprim
  obtain ⟨hlat, hun⟩ := GlobalTheory.RowsOrb.Glue.glue_isLattice_unimodular D large₂ X hStd L hL hU
  have hgen := GlobalTheory.RowsOrb.ExGenus.mem_genus_of_isUnimodular D large₂ hStd X u _ hlat hun
  obtain ⟨hx, hx0, hlm, hsub⟩ := GlobalTheory.RowsOrb.parts_of_lat D X u L
  have hzL : GlobalTheory.RowsOrb.zb X u ∈ L := by
    have h1 := (hprim 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rwa [one_smul] at h1
  have hzΛ : X.zu u ∈ latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact ⟨GlobalTheory.RowsOrb.zb X u, hzL, rfl⟩
  have hfix0 := (X.Fu_fixed u).2.2.2.1
  have hlf : (lf D (X.Fu u)) = (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) := by
    show (⟨X.Fu u, (X.Fu u).z⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS _) = _
    rw [X.flagZVector u]
  have hfix : FixedHyp D (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
    refine ⟨hlat, hun, ⟨?_, rfl⟩, ?_, ?_⟩
    · show (X.Fu u).z ∈ _
      rw [X.flagZVector u]; exact hzΛ
    · intro P
      rw [hx]
      rw [← hx0, hlf]
      exact hfix0 P
    · intro c hc
      have hc' : ((c • GlobalTheory.RowsOrb.zb X u : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) := by
        rw [Submodule.coe_smul, GlobalTheory.RowsOrb.zb_coe, ← X.flagZVector u]; exact hc
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((hprim c).1 (hsub _ hc'))
      exact ⟨o, ho⟩
  have hrow : IsRowLat D (X.Fu u) (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := ⟨hgen, hfix, hx⟩
  obtain ⟨Λ', ⟨hΛ', γ, hγ, hmap⟩, -⟩ := (Y.rowsOK u).2 _ hrow
  obtain ⟨g, hg⟩ := GlobalTheory.RowsOrb.exists_gz_lmap D X u γ hγ
  exact ⟨Λ', hΛ', g, by rw [hg, hmap, hlm]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowOfUnimodularLatticePrimitiveVectorStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_row_of_unimodular_lattice_primitive_vector : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) → ∃ Λ ∈ Y.what₂ u, ∃ g : GlobalTheory.RowsOrb.Gz X u, g • GlobalTheory.RowsOrb.Lmap X u Λ = L := by
  first | exact @GlobalTheory.RowsOrb.exists_row_of_unimod | exact GlobalTheory.RowsOrb.exists_row_of_unimod | (intros; apply GlobalTheory.RowsOrb.exists_row_of_unimod <;> assumption)
end
