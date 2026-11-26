module

public import Formalism.LocalToGlobal.GlobalTheory.MemIffOfLocBasisG
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkGLOBAL7Tied4
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.ClassesLevelZeroNonempty
section -- merged from Formalism.LocalToGlobal.GlobalTheory.ColValS
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Formalism.MainNotions.GlobalTheoryTheory.Inhab

def ColTieW {D : D7} {u : D.what₂.Word} (B : ColBase D u) : Prop :=
  Nonempty ((D.mem u).C.cls 0) ∧
  (∀ c, LatT (D.sp.X 0) (Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c)) ∧
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (nfAll ((D.fm u).lam 0)
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colTie_of_colTieW {D : D7} {u : D.what₂.Word} (B : ColBase D u) (h : ColTieW B) : ColTie B := by
  obtain ⟨h1, h2, co, hinj, hspan, hloc, hinf⟩ := h
  refine ⟨h1, h2, co, hinj, hspan, fun w γ hγ x => ?_, hinf⟩
  obtain ⟨γ0, hγ0, hx⟩ := hloc w
  rw [hx]
  exact forall_congr' fun c => mem_iff_of_locBasis D w ((D.fm u).lam 0) (B.Q c) (B.eQ c) (γ0 c) (γ c)
    (hγ0 c) (hγ c) (co x c)

theorem colTieW_of {D : D7} {u : D.what₂.Word} (B : ColBase D u) (h : ColTie B) : ColTieW B := by
  obtain ⟨h1, h2, co, hinj, hspan, hloc, hinf⟩ := h
  refine ⟨h1, h2, co, hinj, hspan, fun w => ?_, hinf⟩
  have hex : ∀ c τ, ∃ g, LocBasis D w (B.Q c τ) (B.eQ c τ) g := fun c τ =>
    Formalism.L2.GlobalTheoryTheory.TraceIntegrality.exists_locBasis w (B.Q c τ) (B.Q_good c τ) (B.eQ c τ)
  choose γ hγ using hex
  exact ⟨γ, hγ, hloc w γ hγ⟩

theorem colTieW_iff {D : D7} {u : D.what₂.Word} (B : ColBase D u) : ColTieW B ↔ ColTie B :=
  ⟨colTie_of_colTieW B, colTieW_of B⟩

theorem column_value_nonempty_iff (D : D7) (u : D.what₂.Word) :
    Nonempty (ColVal D u) ↔ ∃ B : ColBase D u, ColTieW B := by
  rw [ColVal_nonempty_iff]
  exact exists_congr fun B => (colTieW_iff B).symm

theorem column_value_of_tie_local_bases
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → adm3 D → ∀ u : D.what₂.Word, ∃ B : ColBase D u, ColTieW B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  intro D h1 h2 u
  exact (column_value_nonempty_iff D u).mpr (h D h1 h2 u)

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.LevelZeroClassLatticeIntegral
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def K0 (D : D7) : Coord D.sp.cm (D.sp.X 0) (Fin D.R.k) := ⟨D.sp.crd0, D.sp.gram0, D.sp.hermitianForm_base_coordinates⟩

theorem dualSub_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    flipTwoThree.dualSub S L = (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup := by
  ext x
  show (∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range) ↔ x ∈ Formalism.HermitianLatticesTheory.dual S.hT L
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  simp only [Submodule.mem_one, RingHom.mem_range]

theorem card_ringOfIntegers_quot_natCast_eq_pow (D : D7) (T : ℕ) :
    Nat.card (𝓞 D.host.E ⧸ Ideal.span {((T : ℕ) : 𝓞 D.host.E)}) = T ^ (2 * D.R.f) := by
  have h1 := Ideal.absNorm_span_singleton (((T : ℕ) : 𝓞 D.host.E))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
  rw [h1]
  have h2 : ((T : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (T : ℤ) := by simp
  rw [h2, Algebra.norm_algebraMap, RingOfIntegers.rank, Formalism.MainNotions.StandardLattice.finrank_host D]
  simp [Int.natAbs_pow]

end Formalism.L2.GlobalTheoryTheory

end
end

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem class_lattice_eq_global {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    (K0 D).lat (D.clsLat u 0 c) = globLat ((Lv u).y c).1 (Lv u).Lb :=
  eq_glob_of_hat ((K0 D).isLat_lat (D.clsLat_lat u 0 c)) _ (fun v => by exact (Lv u).y_lat c v)

theorem Lb_le_dl_lv {D : D7} (Lv : LevelData D) (u : D.what₂.Word) :
    (Lv u).Lb ≤ dl D.sp.cm.sig (K0 D).J (Lv u).Lb := by
  intro x hx
  exact Submodule.subset_span ((Lv u).Lb_int x hx)

theorem class_lattice_integral {D : D7} (Lv : LevelData D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    D.clsLat u 0 c ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c) := by
  have h1 : (K0 D).lat (D.clsLat u 0 c) ≤ (K0 D).lat (Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (D.clsLat u 0 c)) := by
    rw [(K0 D).lat_dual, class_lattice_eq_global Lv u c]
    exact le_trans (glob_mono _ (Lb_le_dl_lv Lv u)) (glob_dl_le _ _ _ _ (by exact ((Lv u).y c).2))
  intro x hx
  have h2 := h1 ⟨x, hx, rfl⟩
  rw [(K0 D).mem_lat] at h2
  simpa using h2

theorem latT_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    flipTwoThree.LatT (D.sp.X 0) (flipTwoThree.Tu D u ^ (2 * D.R.f)) (D.clsLat u 0 c) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [dualSub_eq]
    exact class_lattice_integral F.herm.base.lev0 u c hx
  · obtain ⟨e⟩ := (F.herm.atT u).disc 0 (Nat.zero_le _) c
    rw [dualSub_eq, AddSubgroup.relIndex, ← card_ringOfIntegers_quot_natCast_eq_pow D (flipTwoThree.Tu D u)]
    have := Nat.card_congr e.toEquiv
    have hT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
    rw [hT, ← this]
    rfl

theorem classes_level_zero_nonempty {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word) :
    Nonempty ((D.mem u).C.cls 0) := by
  obtain ⟨c, -⟩ := (F.herm.base.lev0 u).y_bij.2 (Quotient.mk'' 1)
  exact ⟨c⟩

def ColRest {D : D7} {u : D.what₂.Word} (B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u) : Prop :=
  ∃ co : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL),
    Function.Injective co ∧
    (∀ F, (∃ x, co x = F) ↔ ∀ c, F c ∈ flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0)) ∧
    (∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
      (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
      ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
        ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (co x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)) ∧
    ∀ (v : NumberField.InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (flipTwoThree.nfAll ((D.fm u).lam 0)
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))
          (flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (co x c)))).re

theorem colValOfTiedS_of_rest
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → flipTwoThree.adm3 D →
      ∀ u : D.what₂.Word, ∃ B : Formalism.MainNotions.GlobalTheoryTheory.Inhab.ColBase D u, ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  column_value_of_tie_local_bases fun D F h3 u => by
    obtain ⟨B, co, h1, h2, h3', h4⟩ := h D F h3 u
    exact ⟨B, classes_level_zero_nonempty F u, latT_of_sym F u, co, h1, h2, h3', h4⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_self_of_on {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (b : Module.Basis (Fin S.rank) E S.V) (hb : ∀ a a', S.hT (b a) (b a') = if a = a' then 1 else 0) (y : S.V) :
    S.hT y y = ∑ a, star (b.repr y a) * b.repr y a := by
  conv_lhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hb,
    smul_eq_mul, starRingEnd_apply]
  simp [mul_ite, Finset.sum_ite_eq]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem posFrame_of_std (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : PosFrame D := by
  obtain ⟨b, hb, -⟩ := h
  intro σ
  refine ⟨(b.toMatrix (D.sp.X 0).frame).map σ, ?_, ?_⟩
  · haveI := b.invertibleToMatrix (D.sp.X 0).frame
    have hu : IsUnit (σ (b.toMatrix (D.sp.X 0).frame).det) :=
      (Matrix.isUnit_det_of_invertible _).map σ
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  · intro y
    have hrepr : ∀ i, ((b.toMatrix (D.sp.X 0).frame).map σ *ᵥ
        fun j => σ ((D.sp.X 0).frame.repr y j)) i = σ (b.repr y i) := by
      intro i
      rw [← (D.sp.X 0).frame.toMatrix_mulVec_repr b y, RingHom.map_mulVec]
      rfl
    simp only [hrepr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT_self_of_on (D.sp.X 0) b hb y, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, host_emb_star, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem colBase_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) : ∃ B : ColBase D u, B.rho = rho :=
  ColBase_exists D u (posFrame_of_std D (F.herm.std.1 0 (Nat.zero_le _))) rho
    (fun c => (D.clsLat_lat u 0 c).span_eq_top)

theorem colValOfTiedS_of_rest'
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → Formalism.MainNotions.flipTwoThree.adm3 D → ∀ u : D.what₂.Word,
      ∃ rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL), ∀ B : ColBase D u, B.rho = rho → ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  refine colValOfTiedS_of_rest fun D F ha u => ?_
  obtain ⟨rho, hr⟩ := h D F ha u
  obtain ⟨B, hB⟩ := colBase_of_sym F u rho
  exact ⟨B, hr B hB⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
