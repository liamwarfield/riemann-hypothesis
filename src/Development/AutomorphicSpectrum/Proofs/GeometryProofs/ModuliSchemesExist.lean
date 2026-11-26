module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionSupNormFieldExtension

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliSchemesExist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem moduli_schemes_exist : N1ab := GlobalTheory.Moduli.moduli_scheme_exists

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightRight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightRight
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem phMu_eq_log_small_blocks_abelian : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  intro hG E _ _ _ _
  exact GlobalTheory.T.component_data_intersection_bound hG E

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightRightStatement
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_weight_right : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_log_small_blocks_abelian | exact GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_log_small_blocks_abelian | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_log_small_blocks_abelian <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleFieldExtMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleFieldExtMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

open GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.PullSec

variable {X X' : Scheme.{0}} {M : LB X} {M' : LB X'} {F : X' ⟶ X}

def IsMoved (w : LB.Iso M' (M.pull F)) (s : M.Sec) (s' : M'.Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : M.ι) (k : M'.ι), F (r z) ∈ M.U j → r z ∈ M'.U k →
    gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k)

theorem IsMoved.mem_nonzeroLocus {w : LB.Iso M' (M.pull F)} (hM : M.IsLB) (hM' : M'.IsLB) {s : M.Sec} {s' : M'.Sec}
    (h : IsMoved w s s') {y : X'} (hy : F y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus s' := by
  obtain ⟨j, hj⟩ := exists_chart hM (F y)
  obtain ⟨k, hk⟩ := exists_chart hM' y
  have u := (mem_nonzeroLocus_iff_pull s F y hj).1 hy
  have e := h X' (𝟙 X') y j k hj hk
  rw [Category.id_comp] at e
  rw [e] at u
  exact (mem_nonzeroLocus_iff_isUnit s' hk).2 ((Units.isUnit_units_mul _ _).1 u)

variable {R R' : Type} [CommRing R] [CommRing R'] {p : X ⟶ Sp R} {p' : X' ⟶ Sp R'}

theorem IsMoved.smul {w : LB.Iso M' (M.pull F)} (hM : M.IsLB) (c : R →+* R') (hc : F ≫ p = p' ≫ spMap c) (a : R)
    {s : KeyGen.SecMod p M} {s' t' : KeyGen.SecMod p' M'} (hs : IsMoved w s s') (ht : IsMoved w (a • s : KeyGen.SecMod p M) t') :
    t' = c a • s' := by
  refine KeyGen.SecMod.ext fun k => fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart hM (F y)
  have e₁ := hs X' (𝟙 X') y j k hj hy
  have e₂ := ht X' (𝟙 X') y j k hj hy
  have hj' : (𝟙 X' ≫ F) y ∈ M.U j := by rwa [Category.id_comp]
  have hy' : (𝟙 X') y ∈ M'.U k := hy
  have ec : cst ((𝟙 X' ≫ F) ≫ p) y a = cst (𝟙 X' ≫ p') y (c a) := by
    rw [Category.assoc, hc, ← Category.assoc, cst_comp]
  rw [KeyGen.smul_f, gs_mul _ y _ hj', gs_constFn p _ _ y hj', ec, e₁, mul_left_comm] at e₂
  rw [KeyGen.smul_f, gs_mul _ y _ hy', gs_constFn p' _ _ y hy']
  exact ((Units.isUnit _).mul_right_inj.1 e₂).symm

theorem exists_moved {w : LB.Iso M' (M.pull F)} (hw : PGen w) (hM : M.IsLB) (hM' : M'.IsLB) (s : M.Sec) :
    ∃ s' : M'.Sec, IsMoved w s s' :=
  sec_pull_down hw hM hM' s

theorem exists_lift {S S' Y Y' : Scheme.{0}} {φ : Y' ⟶ Y} {q' : Y' ⟶ S'} {q : Y ⟶ S} {f : S' ⟶ S}
    (h : IsPullback φ q' q f) (b' : S') (y : Y) (e : q y = f b') : ∃ y' : Y', q' y' = b' ∧ φ y' = y := by
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := f) y b' e
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← hz', ← Scheme.Hom.comp_apply, h.isoPullback_inv_snd]
  · rw [← hz, ← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.PullSec

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

open PullSec

theorem exists_pull_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D'), ∃ P : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) → SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), (∀ (a : 𝓞 L) s, P (a • s) = algebraMap (𝓞 L) (𝓞 L') a • P s) ∧ ∀ (s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (b' : Sp (𝓞 L')) (y : D.t.G.left), D.t.G.hom y = spMap (algebraMap (𝓞 L) (𝓞 L')) b' → y ∈ Out.nonzeroLocus (M := (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) s → ∃ y' : D'.t.G.left, D'.t.G.hom y' = b' ∧ y' ∈ Out.nonzeroLocus (M := (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (P s) := by
  intro E _ _ _ H L _ _ D L' _ _ _ D' m
  obtain ⟨w, gw, -, -⟩ := (isPullCubical_iff m.cm D.t.cub D'.t.cub).1 m.lin
  have hM : (PowB D.t.PP.L 1).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB D.t.PP.L D.t.PP.isLB _ _
  have hM' : (PowB D'.t.PP.L 1).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB D'.t.PP.L D'.t.PP.isLB _ _
  have hex := fun s : (PowB D.t.PP.L 1).Sec => exists_moved (pGen_powIso gw 1) hM hM' s
  choose P hP using hex
  refine ⟨P, fun a s => ?_, fun s b' y e hy => ?_⟩
  · exact IsMoved.smul (p := D.t.G.hom) (p' := D'.t.G.hom) hM (algebraMap (𝓞 L) (𝓞 L')) m.cart.1.w a (hP s) (hP (a • s))
  · obtain ⟨y', h₁, h₂⟩ := exists_lift m.cart.1 b' y e
    exact ⟨y', h₁, (hP s).mem_nonzeroLocus hM hM' (by rw [h₂]; exact hy)⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleFieldExtMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_module_field_ext_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D'), ∃ P : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) → SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), (∀ (a : 𝓞 L) s, P (a • s) = algebraMap (𝓞 L) (𝓞 L') a • P s) ∧ ∀ (s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (b' : Sp (𝓞 L')) (y : D.t.G.left), D.t.G.hom y = spMap (algebraMap (𝓞 L) (𝓞 L')) b' → y ∈ Out.nonzeroLocus (M := (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) s → ∃ y' : D'.t.G.left, D'.t.G.hom y' = b' ∧ y' ∈ Out.nonzeroLocus (M := (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (P s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec <;> assumption)
end
end
