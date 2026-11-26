module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleModelsIsoMemIntegralOfOhE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleModelsIsoMemIntegralOfOhE
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameTransport.IntSwap

theorem toFinE_mem_intAd {D : D7} {x : StandardLatticesGL3.AE D} (hx : x ∈ StandardLatticesGL3.OhE D) :
    GlobalTheory.BotFormula.toFinE D x ∈ Formalism.UG.intAd D.host.E := by
  have key : ∀ y : StandardLatticesGL3.AE D,
      (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)) y ∈
        AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ℚ ⊗[ℚ] D.host.E |
          ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf ℚ, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[ℚ] (o : D.host.E)} →
      GlobalTheory.BotFormula.toFinE D y ∈ Formalism.UG.intAd D.host.E := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).1 hy
  have hle : StandardLatticesGL3.OhE D ≤ (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      refine key _ (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, rfl⟩)
      exact (one_mem (v.adicCompletionIntegers ℚ) : _)
    · refine key _ (AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, ?_⟩)
      rfl
  exact hle hx

theorem swapAE_mem_intAf {D : D7} {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)}) :
    Lev.swapAE D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hle : AddSubgroup.closure {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} ≤
      (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup.comap (Lev.swapAE D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, o, rfl⟩
    have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        ((o : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) *
          ((1 : D.host.E) ⊗ₜ[D.host.F] (a : Formalism.L2.Herm.Af D.host.F)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    show Lev.swapAE D (a ⊗ₜ[D.host.F] (o : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
    rw [e]
    refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨(o : D.host.E), o, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
  exact hle hy

end GlobalTheory.FrameTransport.IntSwap

theorem GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D →
    GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D x hx
  have h1 := GlobalTheory.FrameTransport.IntSwap.toFinE_mem_intAd hx
  have h2 : GlobalTheory.BotFormula.toAfE D x ∈ AddSubgroup.closure
      {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E |
        ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F, ∃ o : 𝓞 D.host.E, z = a ⊗ₜ[D.host.F] (o : D.host.E)} := by
    refine (GlobalTheory.LFun.mem_int_iff _).2 fun P => ?_
    have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.BotFormula.toAfE D x) = GlobalTheory.BotFormula.toFinE D x :=
      (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _
    rw [e]
    exact h1 P
  exact GlobalTheory.FrameTransport.IntSwap.swapAE_mem_intAf h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleModelsIsoMemIntegralOfOhEStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D → GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | exact GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | (intros; apply GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoords
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameTransport

theorem colLat_inv_mulVec_int {K : Type} [Field K] [NumberField K] {n : ℕ} (fr : GL (Fin n) K)
    (x : Fin n → K) (hx : x ∈ colLat fr) : ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K := by
  let M : Submodule (𝓞 K) (Fin n → K) :=
    { carrier := {x | ∀ i, (fr⁻¹.val *ᵥ x) i ∈ Formalism.UG.intOE K}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : fr⁻¹.val *ᵥ (c • a) = (algebraMap (𝓞 K) K c) • (fr⁻¹.val *ᵥ a) := by
          rw [← Matrix.mulVec_smul, algebraMap_smul]
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem ⟨c, rfl⟩ (ha i) }
  have hle : colLat fr ≤ M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ i
    have hcol : (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j) = fr.val *ᵥ Pi.single j 1 := by
      rw [Matrix.mulVec_single_one]; rfl
    show (fr⁻¹.val *ᵥ (fun a : Fin n => (fr : Matrix (Fin n) (Fin n) K) a j)) i ∈ _
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : i = j
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  exact hle hx

theorem inclEAf_intOE_mem {D : D7} (e : D.host.E) (he : e ∈ Formalism.UG.intOE D.host.E) :
    inclEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)


set_option maxHeartbeats 1000000 in
theorem hatL_colLat_coord_int {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    ∀ i, ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  let S := Formalism.L2.Herm.intAf D.host.F D.host.E
  let P : Matrix (Fin n) (Fin n) (Lev.EAf D) := (Formalism.UG.bc (inclEAf D) fr)⁻¹.val
  have hP : P = (fr⁻¹.val).map (inclEAf D) := rfl
  let M : Submodule S (Fin n → Lev.EAf D) :=
    { carrier := {y | ∀ i, (P *ᵥ y) i ∈ S}
      add_mem' := fun {a b} ha hb i => by
        simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply] at ha hb ⊢
        exact add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c a ha i => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have : P *ᵥ (c • a) = (c : Lev.EAf D) • (P *ᵥ a) := by
          rw [← Matrix.mulVec_smul]; rfl
        rw [this, Pi.smul_apply, smul_eq_mul]
        exact mul_mem c.2 (ha i) }
  have hle : Submodule.span S ((fun x : Fin n → D.host.E => fun i =>
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i)) '' (colLat fr : Set (Fin n → D.host.E))) ≤ M := by
    refine (Submodule.span_le (p := M)).2 ?_
    rintro _ ⟨x, hx, rfl⟩ i
    have h1 := colLat_inv_mulVec_int fr x hx i
    have h2 : (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i =
        inclEAf D ((fr⁻¹.val *ᵥ x) i) := by
      rw [hP, RingHom.map_mulVec]; rfl
    show (P *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))) i ∈ S
    rw [h2]
    exact inclEAf_intOE_mem _ h1
  exact hle hy

end GlobalTheory.FrameTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoordsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedColumnLattice_integral_frameCoords : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) → ∀ i, ((Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.hatL_colLat_coord_int | exact GlobalTheory.FrameTransport.hatL_colLat_coord_int | (intros; apply GlobalTheory.FrameTransport.hatL_colLat_coord_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeMapIdealMulTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeMapIdealMulTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HatIdealCarry

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def intOf (b : 𝓞 E) : Formalism.L2.Herm.intAf F E :=
  ⟨Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b),
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, rfl⟩)⟩

theorem incl_smul (b : 𝓞 E) (l : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((b • l) i)) =
      intOf (F := F) b • (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
  funext i
  show _ = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b) *
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)
  rw [← map_mul, Pi.smul_apply, Algebra.smul_def]

theorem incl_add (a b : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a + b) i)) =
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (a i)) +
        (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (b i)) := by
  funext i
  exact map_add _ (a i) (b i)

theorem mulVec_intSmul (M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (r : Formalism.L2.Herm.intAf F E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    M *ᵥ (r • v) = r • (M *ᵥ v) := by
  have e : r • v = (r : E ⊗[F] Formalism.L2.Herm.Af F) • v := rfl
  have e' : r • (M *ᵥ v) = (r : E ⊗[F] Formalism.L2.Herm.Af F) • (M *ᵥ v) := rfl
  rw [e, e', Matrix.mulVec_smul]

theorem intOf_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) {b : 𝓞 E} (hb : b ∈ 𝔪) (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  refine Submodule.span_induction
    (p := fun z _ => intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨b • x, Submodule.smul_mem_smul hb hx, ?_⟩
    exact incl_smul b x
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [smul_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem transportGen (uf : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L Λ : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := F) L → uf *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ)
    (𝔪 : Ideal (𝓞 E)) (y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • L)) : uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  have gen : ∀ w ∈ 𝔪 • L, uf *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (w i)) ∈
      Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro b hb l hl
      rw [incl_smul b l, mulVec_intSmul]
      exact intOf_smul_mem Λ 𝔪 hb _ (hL _ (Submodule.subset_span ⟨l, hl, rfl⟩))
    · intro a c ha hc
      rw [incl_add, Matrix.mulVec_add]
      exact Submodule.add_mem _ ha hc
  refine Submodule.span_induction
    (p := fun y _ => uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨w, hw, rfl⟩
    exact gen w hw
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [mulVec_intSmul]; exact Submodule.smul_mem _ c ha

end Gen

theorem transport : ∀ {D : D7} {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L) → uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  fun uf L Λ hL 𝔪 y hy => transportGen uf.val L Λ hL 𝔪 y hy

end GlobalTheory.HatIdealCarry
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeMapIdealMulTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLatticeMap_idealMul_transport : ∀ {D : D7} {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L) → uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) := by
  first | exact @GlobalTheory.HatIdealCarry.transport | exact GlobalTheory.HatIdealCarry.transport | (intros; apply GlobalTheory.HatIdealCarry.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMulVecCompletedIdealMemCompletedIdealLattic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMulVecCompletedIdealMemCompletedIdealLattic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FrameColSmul

theorem colMul_mem_of_span {A : Type} [CommRing A] (S : Subring A) {ι : Type} (M : Submodule S (ι → A))
    (c : ι → A) (G : Set A) (hG : ∀ y ∈ G, (fun i => c i * y) ∈ M) (x : A)
    (hx : x ∈ Submodule.span S G) : (fun i => c i * x) ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero =>
    have : (fun i => c i * (0 : A)) = 0 := by funext i; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b) := by
      funext i; simp [mul_add]
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => c i * (r • a)) = r • (fun i => c i * a) := by
      funext i
      show c i * ((r : A) * a) = (r : A) * (c i * a)
      exact mul_left_comm _ _ _
    rw [this]; exact M.smul_mem r ha

theorem mulVec_eq_sum_col {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (w : Fin n → A) :
    P *ᵥ w = ∑ j, (fun i => P i j * w j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

theorem map_col_mul {E A : Type} [Field E] [NumberField E] [CommRing A] (φ : E →+* A) {n : ℕ}
    (c : Fin n → E) (b : 𝓞 E) :
    (fun i => φ (c i) * φ (b : E)) = fun i => φ ((b • c) i) := by
  funext i
  show _ = φ ((b : E) * c i)
  rw [map_mul, mul_comm]

theorem gen_mem {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (j : Fin n)
    (b : 𝓞 D.host.E) (hb : b ∈ 𝔪) :
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j) *
        GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  have hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr :=
    Submodule.subset_span ⟨j, rfl⟩
  have hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr :=
    Submodule.smul_mem_smul hb hcol
  rw [map_col_mul]
  exact Submodule.subset_span ⟨_, hm, rfl⟩

theorem mulVec_mem : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  intro D n fr 𝔪 w hw
  rw [mulVec_eq_sum_col]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _
    (by
      rintro _ ⟨b, hb, rfl⟩
      exact gen_mem fr 𝔪 j b hb) (w j) (hw j)

end GlobalTheory.FrameColSmul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMulVecCompletedIdealMemCompletedIdealLatticStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  first | exact @GlobalTheory.FrameColSmul.mulVec_mem | exact GlobalTheory.FrameColSmul.mulVec_mem | (intros; apply GlobalTheory.FrameColSmul.mulVec_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.FrameTransport.Cong

variable {D : D7}

theorem adSwap_mem_intAf (x : StandardLatticesGL3.AE D) (hx : x ∈ StandardLatticesGL3.OhE D) :
    adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE x hx

theorem adSwap_inc (e : D.host.E) : adSwap D (StandardLatticesGL3.inc D e) = inclEAf D e := by
  have h1 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ e) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  have h2 : GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e := by
    show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e)) = _
    rw [h1, RingEquiv.symm_apply_eq]
    show _ = GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e)
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e)) = _
  rw [h2]
  rfl

theorem intG_entries {n : ℕ} (k : StandardLatticesGL3.GA D n) (hk : k ∈ GlobalTheory.NormSum.intG D n) : StandardLatticesGL3.IntG D k.1 := by
  have hmul : ∀ a b : GL (Fin n) (StandardLatticesGL3.AE D), (∀ i j, a.val i j ∈ StandardLatticesGL3.OhE D) → (∀ i j, b.val i j ∈ StandardLatticesGL3.OhE D) →
      ∀ i j, (a * b).val i j ∈ StandardLatticesGL3.OhE D := fun a b ha hb i j => by
    rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l) (hb l j)
  let H : Subgroup (StandardLatticesGL3.GA D n) :=
    { carrier := {k | StandardLatticesGL3.IntG D k.1}
      mul_mem' := fun {a b} ha hb i j => by
        refine ⟨hmul a.1 b.1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j, ?_⟩
        have e : ((a * b : StandardLatticesGL3.GA D n) : GL (Fin n) (StandardLatticesGL3.AE D))⁻¹ = b.1⁻¹ * a.1⁻¹ := by
          rw [Subgroup.coe_mul, _root_.mul_inv_rev]
        rw [e]
        exact hmul _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
      one_mem' := fun i j => by
        have h1 : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) i j ∈ StandardLatticesGL3.OhE D := fun i j => by
          rw [Matrix.one_apply]
          split_ifs
          exacts [Subring.one_mem _, Subring.zero_mem _]
        exact ⟨h1 i j, by rw [Subgroup.coe_one, inv_one]; exact h1 i j⟩
      inv_mem' := fun {a} ha i j => by
        refine ⟨(ha i j).2, ?_⟩
        rw [Subgroup.coe_inv, inv_inv]
        exact (ha i j).1 }
  exact (Subgroup.closure_le H).2 (fun k hk => hk) hk

theorem hatL_colLat_int {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (i : Fin n) :
    ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.T.completedColumnLattice_integral_frameCoords fr y hy i

theorem col_mem_hatL {n : ℕ} (fr : GL (Fin n) D.host.E) (j : Fin n) :
    (fun i => inclEAf D (fr.val i j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) :=
  Submodule.subset_span ⟨fun a => fr.val a j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem eaf_mul_comm (a b : Lev.EAf D) : a * b = b * a := mul_comm a b

set_option maxHeartbeats 1000000 in
theorem hatL_colLat_of_int {n : ℕ} (fr : GL (Fin n) D.host.E) (z : Fin n → Lev.EAf D)
    (hz : ∀ i, z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  have e : (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z =
      ∑ j, (⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j)) := by
    funext i
    rw [Finset.sum_apply]
    show ∑ j, (Formalism.UG.bc (inclEAf D) fr).val i j * z j =
      ∑ j, ((⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j))) i
    exact Finset.sum_congr rfl fun j _ => eaf_mul_comm _ _
  exact (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) e).mpr
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (col_mem_hatL fr j))

theorem mul_mem_spanIncl (𝔪 : Ideal (𝓞 D.host.E)) (a z : Lev.EAf D)
    (ha : a ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))))
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    a * z ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have h3 := Submodule.smul_mem _ (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ha
  have e : (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • a = a * z := mul_comm z a
  exact e ▸ h3

theorem adSwap_hatId (𝔪 : Ideal (𝓞 D.host.E)) (c : StandardLatticesGL3.AE D) (hc : c ∈ SqNum.hatId D 𝔪) :
    adSwap D c ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have hle : SqNum.hatId D 𝔪 ≤ (Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))).toAddSubgroup.comap
        (adSwap D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 fun y hy => ?_
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    have e : adSwap D (StandardLatticesGL3.inc D (b : D.host.E) * s) = inclEAf D (b : D.host.E) * adSwap D s :=
      (map_mul (adSwap D) _ _).trans (congrArg (· * adSwap D s) (adSwap_inc _))
    exact (congrArg (fun v => v ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) e).mpr
      (mul_mem_spanIncl 𝔪 _ _ (Submodule.subset_span ⟨b, hb, rfl⟩) (adSwap_mem_intAf s hs))
  exact hle hc

theorem hatL_smul_colLat {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D)
    (hw : ∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) :=
  GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice fr 𝔪 w hw

theorem hatL_transport {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D) (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L)) :
    uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  GlobalTheory.T.completedLatticeMap_idealMul_transport uf L Λ h 𝔪 y hy

theorem frConj_val {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ ((Formalism.UG.bc (adSwap D) k).val *ᵥ
      ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [frConj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem bc_adSwap_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    (Formalism.UG.bc (adSwap D) k).val i j = adSwap D (k.val i j) := rfl

theorem GL_mulVec_inv {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P.val *ᵥ (P⁻¹.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem GL_inv_mulVec {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P⁻¹.val *ᵥ (P.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem frConj_sub {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y - y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ
      (((Formalism.UG.bc (adSwap D) k).val - 1) *ᵥ ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, GL_mulVec_inv (Formalism.UG.bc (inclEAf D) fr) y,
    frConj_val fr k y]

theorem bc_adSwap_sub_one_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    ((Formalism.UG.bc (adSwap D) k).val - 1) i j = adSwap D ((k.val - 1) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  exacts [(map_one (adSwap D)).symm, (map_zero (adSwap D)).symm]

theorem frConj_stab {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, k.val i j ∈ StandardLatticesGL3.OhE D) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  rw [frConj_val]
  refine hatL_colLat_of_int fr _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (by rw [bc_adSwap_apply]; exact adSwap_mem_intAf _ (hk i j))
    (hatL_colLat_int fr y hy j)

theorem frConj_stab_iff {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : StandardLatticesGL3.IntG D k) (y : Fin n → Lev.EAf D) :
    y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  refine ⟨frConj_stab fr k (fun i j => (hk i j).1) y, fun h => ?_⟩
  have h2 := frConj_stab fr k⁻¹ (fun i j => (hk i j).2) _ h
  have e : (frConj fr k⁻¹).val *ᵥ ((frConj fr k).val *ᵥ y) = y := by
    rw [map_inv]; exact GL_inv_mulVec _ y
  exact e ▸ h2

theorem frConj_cong {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, (k.val - 1) i j ∈ SqNum.hatId D 𝔪) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  rw [frConj_sub fr k y]
  refine hatL_smul_colLat fr 𝔪 _ fun i => ?_
  show (∑ j, ((Formalism.UG.bc (adSwap D) k).val - 1) i j * ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) j) ∈ _
  refine Submodule.sum_mem _ fun j _ => ?_
  have h4 := mul_mem_spanIncl 𝔪 _ _ (adSwap_hatId 𝔪 _ (hk i j)) (hatL_colLat_int fr y hy j)
  rw [bc_adSwap_sub_one_apply k i j]
  exact h4


set_option maxHeartbeats 1000000 in
theorem conj_mem_congLev : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  intro D V fr uf Λ hL 𝔪 k hk hc hU
  have hM : ∀ x, x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      uf⁻¹.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := fun x =>
    ((hL (uf⁻¹.val *ᵥ x)).trans (by rw [GL_mulVec_inv uf x])).symm
  have hg : ∀ x, (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x = uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x)) := by
    intro x
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hg' : ∀ x, uf⁻¹.val *ᵥ ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x) = (frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) := by
    intro x
    rw [hg x, GL_inv_mulVec]
  refine ⟨hU, fun x => ?_, fun x hx => ?_⟩
  · refine (hM x).trans ((frConj_stab_iff fr k.1 (intG_entries k hk) _).trans ?_)
    exact ((hM ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x)).trans
      (Iff.of_eq (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (hg' x)))).symm
  · have hy := (hM x).1 hx
    have h5 := hatL_transport uf (colLat fr) Λ (fun v hv => (hL v).1 hv) 𝔪 _ (frConj_cong fr 𝔪 k.1 hc _ hy)
    have e : uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) - uf⁻¹.val *ᵥ x) =
        (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x - x := by
      exact (Matrix.mulVec_sub uf.val _ _).trans (congrArg₂ HSub.hSub (hg x).symm (GL_mulVec_inv uf x))
    exact Eq.mp (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) e) h5

end GlobalTheory.FrameTransport.Cong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongrStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.FrameTransport.Cong.conj_mem_congLev | exact GlobalTheory.FrameTransport.Cong.conj_mem_congLev | (intros; apply GlobalTheory.FrameTransport.Cong.conj_mem_congLev <;> assumption)
end
