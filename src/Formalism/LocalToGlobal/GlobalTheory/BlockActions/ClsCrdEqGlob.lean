module

public import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapPropertiesOfSymmetricForms

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.SelfDualPHolds
section -- merged from Formalism.LocalToGlobal.GlobalTheory.BlockActions.BrStmt
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ChiFinM (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U,
    (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)

def SelfDualP (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))

end Formalism.L2.GlobalTheoryTheory.Br
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem gramP_det_unit (D : D7) : IsUnit (gramP D).det := by
  let _ := D.host.cmStar
  unfold gramP
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.G.gram_det_unit D.sp.cm D.sp.X'

theorem isLat_dlP (D : D7) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)) (hM : Comp.IsLat M) :
    Comp.IsLat (Comp.dl (sigD D) (gramP D) M) := by
  have hL : Submodule.IsLattice D.host.E M := Submodule.IsLattice.of_fg _ (Module.Finite.iff_fg.1 hM.1)
  have hFull : Submodule.IsFullLattice D.host.E M := { hL with span_eq_top := hM.2 }
  obtain ⟨d, hd, hle⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramP D) (gramP_det_unit D) M hFull
  exact ⟨Module.Finite.iff_fg.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hd hle),
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramP D) M hL⟩

variable {D : D7} {u : D.what₂.Word}

theorem levelLattice_dual_eq_self (K : ClsPTied (D := D) u) : Comp.dl (sigD D) (gramP D) K.lev.Lb = K.lev.Lb := by
  have hS : dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) K.lev.Lb = (K.lev.Lb : Set _) := by
    ext y
    constructor
    · intro hy
      have h := K.lev.Lb_dual y hy
      simpa using h
    · intro hy
      exact K.lev.Lb_int y hy
  unfold Comp.dl
  rw [hS, Submodule.span_eq]

theorem classLattice_eq_globalLattice (K : ClsPTied (D := D) u) (c : (D.fm u).clsP) :
    K.lat c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
  ext x
  constructor
  · intro hx
    exact (K.y_lat c _).1 (latS_of_mem _ x hx)
  · intro hx
    exact latLocGlob _ _ _ (K.lat c) (K.lat_fin c) x ((K.y_lat c _).2 hx)

theorem selfDualP_of_formsTiedSym {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf) :
    SelfDualP Tf := by
  intro c
  have hLb : Comp.IsLat Tf.clsP.lev.Lb := ⟨Tf.clsP.lev.Lb_fin, Tf.clsP.lev.Lb_span⟩
  have h1 : Comp.dl (sigD D) (gramP D) (Tf.clsP.lat c) = Tf.clsP.lat c := by
    rw [classLattice_eq_globalLattice, ← Comp.glob_dl (sigD D) (gramP D) (isLat_dlP D) hLb _ (Tf.clsP.y c).2, levelLattice_dual_eq_self]
  rw [← Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_span_dualSet]
  exact congrArg (fun M : Submodule _ _ => (M : Set (Fin (D.R.N D.R.m - 1) → D.host.E))) h1

end Formalism.L2.GlobalTheoryTheory.Br
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem isLat_dlN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) (hM : Comp.IsLat M) :
    Comp.IsLat (Comp.dl (sigD D) (gramN D i hi) M) := by
  have hL : Submodule.IsLattice D.host.E M := Submodule.IsLattice.of_fg _ (Module.Finite.iff_fg.1 hM.1)
  have hFull : Submodule.IsFullLattice D.host.E M := { hL with span_eq_top := hM.2 }
  obtain ⟨d, hd, hle⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) M hFull
  exact ⟨Module.Finite.iff_fg.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hd hle),
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) M hL⟩

variable {D : D7} {u : D.what₂.Word}

theorem clsCrd_finite (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u i hi c) := by
  let _ := D.host.cmStar
  rw [Module.Finite.iff_fg]
  exact (D.clsLat_lat u i c).fg.map _

theorem clsCrd_eq_glob {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    clsCrd D u i hi c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
  ext x
  constructor
  · intro hx
    exact (K.y_lat c _).1 (latS_of_mem _ x hx)
  · intro hx
    exact latLocGlob _ _ _ _ (clsCrd_finite i hi c) x ((K.y_lat c _).2 hx)

theorem ld_eq_glob {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    Ld D u i hi c = Formalism.UG.CS.globLat (K.y c).1 (Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := by
  have hLb : Comp.IsLat K.lev.Lb := ⟨K.lev.Lb_fin, K.lev.Lb_span⟩
  show Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c) = _
  rw [clsCrd_eq_glob K c, Comp.glob_dl (sigD D) (gramN D i hi) (isLat_dlN D i hi) hLb _ (K.y c).2]

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem bc_val' {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL (Fin n) A) :
    ((bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map φ := rfl

theorem bc_incl_w (w : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin n) E) :
    bc (inclE (F := F) (w.adicCompletion F)) γ = bc (prV (E := E) w) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ) := by
  apply Units.ext
  rw [bc_val', bc_val', bc_val', Matrix.map_map, ← RingHom.coe_comp, Formalism.L2.G.Cmp.prV_incl]

theorem locDual (w : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ Formalism.UG.CS.globLat g Λ) :
    ((bc (prV (E := E) w) g)⁻¹ : GL (Fin n) (E ⊗[F] w.adicCompletion F)).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) Λ := by
  have h1 : ((g⁻¹ : GL (Fin n) _) : Matrix _ _ _) *ᵥ (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := hz
  have h2 := latS_prV w _ _ h1
  have e : ((bc (prV (E := E) w) g)⁻¹ : GL (Fin n) (E ⊗[F] w.adicCompletion F)).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (z a)) =
      fun j => prV (E := E) w ((((g⁻¹ : GL (Fin n) _) : Matrix _ _ _) *ᵥ
        (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a))) j) := by
    rw [← map_inv, bc_val']
    funext j
    rw [RingHom.map_mulVec]
    have hc : (⇑(prV (E := E) w) ∘ fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (z a) := by
      funext a
      exact RingHom.congr_fun (Formalism.L2.G.Cmp.prV_incl (E := E) w) (z a)
    rw [hc]
  rw [e]
  exact h2

theorem conj_step (w : HeightOneSpectrum (𝓞 F)) (Y κ : GL (Fin n) (E ⊗[F] w.adicCompletion F)) (γ : GL (Fin n) E)
    (h : bc (inclE (F := F) (w.adicCompletion F)) γ = Y * κ * Y⁻¹) (x : Fin n → E) :
    (Y⁻¹).val *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      κ.val *ᵥ ((Y⁻¹).val *ᵥ fun a => inclE (F := F) (w.adicCompletion F) (x a)) := by
  have em : (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      (bc (inclE (F := F) (w.adicCompletion F)) γ).val *ᵥ
        (fun a => inclE (F := F) (w.adicCompletion F) (x a)) := by
    funext a
    rw [bc_val']
    exact RingHom.map_mulVec _ _ _ a
  rw [em, h, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

theorem conj_stepA (w : HeightOneSpectrum (𝓞 F)) (Y κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ = Y * κ * Y⁻¹) (x : Fin n → E) :
    ((bc (prV (E := E) w) Y)⁻¹).val *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      (bc (prV (E := E) w) κ).val *ᵥ (((bc (prV (E := E) w) Y)⁻¹).val *ᵥ fun a => inclE (F := F) (w.adicCompletion F) (x a)) :=
  conj_step w _ _ γ (by rw [bc_incl_w, h, map_mul, map_mul, map_inv]) x

end Gen

theorem dualLoc_of {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (w : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c) :
    ((bc (prV (E := D.host.E) w) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (w.adicCompletion D.host.F) (z a)) ∈
      latS (F := D.host.F) (w.adicCompletion D.host.F) (intV D.host.E w)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  rw [ld_eq_glob K c] at hz
  exact locDual w (K.y c).1 _ z hz

end Formalism.L2.GlobalTheoryTheory.Br
