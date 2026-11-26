module

public import Formalism.LocalToGlobal.Columns.RecLevelStep

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.HxMemMap
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec}

theorem hx_hform (i : ℕ) (hi : i ≤ D.R.m) (x y : (D.sp.X i).V) :
    (D.sp.X i).hT x y = hform (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.crdN D i hi x) (CF.crdN D i hi y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) x y]
  unfold hform
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  exact Finset.sum_congr rfl fun b _ => rfl

variable (u : D.what₂.Word)

theorem hx_clsCrd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c = (D.clsLat u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := rfl

theorem hx_Ld_eq (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.Ld D u i hi c = (CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  have key : (((CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.clsCrd D u i hi c) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩ s ⟨y, hy, rfl⟩
      have := (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) x).1 hx y hy
      rw [hx_hform i hi] at this
      exact this
    · intro ht
      refine ⟨(CF.crdN D i hi).symm t, ?_, (CF.crdN D i hi).apply_symm_apply t⟩
      refine (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) _).2 fun y hy => ?_
      rw [hx_hform i hi, LinearEquiv.apply_symm_apply]
      exact ht (CF.crdN D i hi y) ⟨y, hy, rfl⟩
  show Submodule.span (𝓞 D.host.E) (dualSet _ _ _) = _
  rw [← key, Submodule.span_eq]

theorem hx_mem_map {i : ℕ} (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ M.map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) ↔ x ∈ M := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := (CF.crdN D i hi).injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

theorem hx_mem_Ld (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Ld D u i hi c ↔ x ∈ CH.Ld D u i c := by
  rw [hx_Ld_eq, hx_mem_map]

theorem hx_smul_Ld (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    I • CF.Ld D u i hi c = (I • CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_Ld_eq, Submodule.map_smul'']

theorem hx_Lk_eq (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c ⊔ I • CF.Ld D u i hi c = (CH.Lk D u I i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_smul_Ld, hx_clsCrd, ← Submodule.map_sup]

variable {u} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_mem_Lk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Lk A i hi v c ↔ x ∈ CH.Lk D u (A.Pv v) i c := by
  show CF.crdN D i hi x ∈ CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c ↔ _
  rw [hx_Lk_eq, hx_mem_map]

def hxLd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ ↥(CF.Ld D u i hi c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Ld u i hi c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def hxLk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    ↥(CH.Lk D u (A.Pv v) i c) →+ ↥(CF.Lk A i hi v c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Lk A i hi v c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)


open Classical in
def hxPr (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ (D.fm u).lv i v c :=
  if hi : i ≤ D.R.m then ((P i hi).pr v c).comp (hxLd i hi c) else 0


open Classical in
def hxPrk (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Lk D u (A.Pv v) i c) →+ (D.fm u).lk i v c :=
  if hi : i ≤ D.R.m then ((P i hi).prk v c).comp (hxLk A i hi v c) else 0

theorem hxPr_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = (P i hi).pr v c (hxLd i hi c z) := by
  unfold hxPr; rw [dite_eq_left hi]; rfl

theorem hxPrk_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = (P i hi).prk v c (hxLk A i hi v c z) := by
  unfold hxPrk; rw [dite_eq_left hi]; rfl

theorem hxPr_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPr A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).pr_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Ld u i hi c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPr_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPr_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c (r • z) = A.res v r • hxPr A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPr_eq A P i hi, hxPr_eq A P i hi, ← (P i hi).pr_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPr; rw [dite_eq_right hi]; simp

theorem hxPr_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Ld D u i c := by
  rw [hxPr_eq A P i hi, (P i hi).pr_ker, hx_smul_Ld]
  exact hx_mem_map hi _ z.1

theorem hx_fv_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    (D.fm u).fv i v c (hxPr A P i v c z) = 0 ↔ z.1 ∈ CH.Lk D u (A.Pv v) i c := by
  rw [hxPr_eq A P i hi, (P i hi).fv_ker]
  exact hx_mem_Lk A i hi v c z.1

theorem hxPrk_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPrk A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).prk_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Lk A i hi v c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPrk_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPrk_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c (r • z) = A.res v r • hxPrk A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPrk_eq A P i hi, hxPrk_eq A P i hi, ← (P i hi).prk_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPrk; rw [dite_eq_right hi]
    change (0 : (D.fm u).lk i v c) = A.res v r • 0
    exact (smul_zero _).symm

theorem hxPrk_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Lk D u (A.Pv v) i c := by
  rw [hxPrk_eq A P i hi, (P i hi).prk_ker]
  show CF.crdN D i hi z.1 ∈ A.Pv v • (CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c) ↔ _
  rw [hx_Lk_eq, ← Submodule.map_smul'']
  exact hx_mem_map hi _ z.1

theorem hx_te (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c))
    (hz : (D.fm u).fv i v c (hxPr A P i v c z) = 1)
    (h : ((D.mem u).A.T : D.host.E) • z.1 ∈ CH.Lk D u (A.Pv v) i c) :
    hxPrk A P i v c ⟨_, h⟩ = (D.fm u).te i v c := by
  rw [hxPr_eq A P i hi] at hz
  have e : CF.crdN D i hi (((D.mem u).A.T : D.host.E) • z.1) = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 := by
    rw [map_smul]
    show _ = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • CF.crdN D i hi z.1
    rw [Algebra.smul_def' , map_natCast] <;> rfl
  have h' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 ∈ CF.Lk A i hi v c := by
    rw [← e]; exact (hx_mem_Lk A i hi v c _).2 h
  rw [hxPrk_eq A P i hi, ← (P i hi).te v c (hxLd i hi c z) hz h']
  congr 1
  exact Subtype.ext e

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_Pv_max (v : (D.mem u).A.vT) : (A.Pv v).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)

def AtTSeen : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.E) (y : D.what₂.LL),
      D.what₂.embLL y = D.host.emb (D.eTau ((D.fm u).tauOf w v)).1 (x : D.host.E) →
      ((0 : WithTop ℤ) < D.what₂.places.val w y ↔
        x ∈ (if (D.fm u).seenP w then A.Pv v else Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v)))


variable (D u) in
def AtTDisc : Prop :=
  ∀ i, i ≤ D.R.m → ∀ c : (D.mem u).C.cls i,
    Nonempty ((CH.Ld D u i c ⧸ (D.clsLat u i c).comap (CH.Ld D u i c).subtype) ≃ₗ[𝓞 D.host.E]
      (𝓞 D.host.E ⧸ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}))


set_option maxHeartbeats 4000000 in
structure AtTMoves where

  upG : ∀ i v (c : (D.mem u).C.cls i), CH.Ld D u i c → CH.GX D i

  up_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : CH.Ld D u i c), (D.fm u).fv i v c (hxPr A P i v c y) = 1 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : ((D.mem u).A.T : D.host.E) • (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dnG : ∀ i v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) → CH.GX D i

  dn_tie : ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (CH.Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (D.clsLat u i c) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Lk D u (A.Pv v) i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = g (hxPrk A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dilG : ∀ i v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → CH.GX D i

  dil_tie : ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.HermitianLatticesTheory.gmap (dilG i v a c).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))


set_option maxHeartbeats 4000000 in
structure AtTXp where

  lattice₂ : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V

  levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0)

  clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ lattice₂

  z0 : (D.sp.X D.R.m).V
  cocycle_zero_mem_invariants : z0 ∈ Submodule.span D.host.E {D.sp.z}
  hermitianForm_lastCoordinateUniformizerVector_self : (D.sp.X D.R.m).hT z0 z0 = ((D.mem u).A.T : D.host.E)
  tilG : (D.fm u).clsP → CH.GX D D.R.m

  til_tie : ∀ c : (D.fm u).clsP,
    Formalism.HermitianLatticesTheory.gmap (tilG c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} ∧
    ∀ v (z : CH.Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E),
      (a : D.host.E) = (D.sp.X D.R.m).hT z0 ((tilG c).1 (z : (D.sp.X D.R.m).V)) →
      (D.fm u).fv D.R.m v _ (hxPr A P D.R.m v _ z) = A.res v a


set_option maxHeartbeats 4000000 in
def atTOf (eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal))
    (hF : ∀ v (a : 𝓞 D.host.F), eF v (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a)
    (hs : AtTSeen A) (hd : AtTDisc D u) (M : AtTMoves A P) (Xp : AtTXp A P) : CH.AtT D u A.eV eF where
  piU := A.piU
  piU_K := A.piU_K
  piU_norm := A.piU_norm
  piU_cong := A.piU_cong
  Pv := A.Pv
  Pv_max := hx_Pv_max A
  Pv_pi := A.res_pi
  Pv_over := fun v => Ideal.ext fun x => ((A.res_v v x).symm)
  res := A.res
  res_surj := A.res_surj
  res_ker := fun _ => rfl
  res_F := hF
  seen := hs
  disc := hd
  pr := hxPr A P
  pr_surj := hxPr_surj A P
  pr_smul := hxPr_smul A P
  pr_ker := hxPr_ker A P
  fv_ker := hx_fv_ker A P
  prk := hxPrk A P
  prk_surj := hxPrk_surj A P
  prk_smul := hxPrk_smul A P
  prk_ker := hxPrk_ker A P
  te_tie := hx_te A P
  upG := M.upG
  up_tie := M.up_tie
  dnG := M.dnG
  dn_tie := M.dn_tie
  dilG := M.dilG
  dil_tie := M.dil_tie
  lattice₂ := Xp.lattice₂
  levP := Xp.levP
  clsP := Xp.clsP
  z0 := Xp.z0
  cocycle_zero_mem_invariants := Xp.cocycle_zero_mem_invariants
  hermitianForm_lastCoordinateUniformizerVector_self := Xp.hermitianForm_lastCoordinateUniformizerVector_self
  tilG := Xp.tilG
  til_tie := Xp.til_tie

end Formalism.L2.Col
