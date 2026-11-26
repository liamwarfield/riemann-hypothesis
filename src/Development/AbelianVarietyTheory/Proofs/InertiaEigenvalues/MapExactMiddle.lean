module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem exact_of_finrank_add {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (h0 : p ∘ₗ f = 0)
    (hd : Module.finrank K V = Module.finrank K U + Module.finrank K W) : Function.Exact f p := by
  rw [LinearMap.exact_iff]
  have hle : LinearMap.range f ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h0, LinearMap.zero_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at hrn
  have hrf := LinearMap.finrank_range_of_inj hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem finrank_add_of_exact {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (he : Function.Exact f p) :
    Module.finrank K V = Module.finrank K U + Module.finrank K W := by
  rw [LinearMap.exact_iff] at he
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [he, LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.finrank_range_of_inj hf] at hrn
  omega

theorem DFun.map_exact_middle {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k))
    (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hB : F.Obj B) (hf : IsHom A B f) (hp : IsHom B C p)
    (hi : Function.Injective f) (hs : Function.Surjective p) (he : Function.Exact f p) (i : ZMod n) :
    Function.Exact (F.map A B f i) (F.map B C p i) := by
  have hA : F.Obj A := F.obj_sub A B f hf hi hB
  have hC : F.Obj C := F.obj_quot B C p hp hs hB
  have hd := finrank_add_of_exact f p hi hs he
  simp only [Module.finrank_fin_fun] at hd
  have hpf : p ∘ₗ f = 0 := LinearMap.ext fun x => he.apply_apply_eq_zero x
  have h0hom : IsHom A C (0 : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) := fun g x => by simp
  have hcomp : F.map B C p i ∘ₗ F.map A B f i = 0 := by
    rw [← F.map_comp A B C f p hA hB hC hf hp i, hpf]
    refine LinearMap.ext fun x => ?_
    have h := F.map_smul A C 0 0 hA hC h0hom i x
    simpa using h
  refine exact_of_finrank_add (F.map A B f i) (F.map B C p i) (F.map_inj A B f hA hB hf hi i)
    (F.map_surj B C p hB hC hp hs i) hcomp ?_
  simp only [Vc, Module.finrank_fin_fun]
  exact hd

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddleStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_map_of_exact : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, Function.Exact (F.map A B f i) (F.map B C p i) := by
  first | exact @GlobalTheory.Models.DFun.map_exact_middle | exact GlobalTheory.Models.DFun.map_exact_middle | (intros; apply GlobalTheory.Models.DFun.map_exact_middle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanIsLinesOfGraded
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

namespace GlobalTheory.SenLines.SplitFil

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def lineMap {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) : (Fin r → F⟦X⟧) →ₗ[F] (ℤ → M) where
  toFun c := ∑ k, serLine (u k) (d k) (c k)
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.add_apply]
    split_ifs <;> simp [add_smul]
  map_smul' a c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.smul_apply]
    split_ifs <;> simp [mul_smul]

theorem smul_serMul (a : F) (f : F⟦X⟧) {y : ℤ → M} (hy : IsLaurent y) :
    a • serMul f y = serMul (a • f) y := by
  funext m
  simp only [Pi.smul_apply, serMul]
  rw [smul_finsum' a (serMul_finite f hy m)]
  refine finsum_congr fun j => ?_
  simp [mul_smul]

theorem mem_serSpan_iff {N : Type} (L : N → ℤ → M) (hL : ∀ x, IsLaurent (L x)) (y : ℤ → M) :
    y ∈ serSpan F (Set.range L) ↔
      ∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j)) := by
  constructor
  · intro hy
    obtain ⟨n, c, g, h⟩ := Submodule.mem_span_set'.mp hy
    have hg : ∀ i, ∃ (f : F⟦X⟧) (x : N), (g i : ℤ → M) = serMul f (L x) := fun i => by
      obtain ⟨f, w, ⟨x, rfl⟩, -, h⟩ := (g i).2
      exact ⟨f, x, h⟩
    choose f x hg using hg
    refine ⟨n, x, fun i => c i • f i, ?_⟩
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg, smul_serMul _ _ (hL _)]
    rfl
  · rintro ⟨s, x, f, rfl⟩
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.subset_span ⟨f j, L (x j), ⟨x j, rfl⟩, hL _, rfl⟩

theorem exists_coef {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (a : ℤ) (z : M)
    (hz : z ∈ Submodule.span F (d '' {k | a ≤ u k})) :
    ∃ c : Fin r → F, (∀ k, u k < a → c k = 0) ∧ z = ∑ k, c k • d k := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun k' hk' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hk (not_le.mpr hk')
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    exact ⟨c + c', fun k hk => by simp [hc k hk, hc' k hk],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul b x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨b • c, fun k hk => by simp [hc k hk], by simp [mul_smul, Finset.smul_sum]⟩

theorem gradedSer_eq_range {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M)
    (hA : ∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) :
    gradedSer A = LinearMap.range (lineMap (F := F) u d) := by
  apply le_antisymm
  · refine iSup_le fun a y hy => ?_
    obtain ⟨hy0, hy1⟩ := hy
    have hex : ∀ m : ℤ, ∃ c : Fin r → F, (∀ k, m + u k < 0 → c k = 0) ∧
        y m = ∑ k, c k • d k := fun m => by
      by_cases hm : m < -a
      · exact ⟨0, fun _ _ => rfl, by simp [hy0 m hm]⟩
      · obtain ⟨c, hc, h⟩ := exists_coef u d a (y m) (hA a ▸ hy1 m)
        exact ⟨c, fun k hk => hc k (by omega), h⟩
    choose c hc hyc using hex
    refine ⟨fun k => PowerSeries.mk fun j => c ((j : ℤ) - u k) k, ?_⟩
    funext m
    change (∑ k, serLine (u k) (d k) (PowerSeries.mk fun j => c ((j : ℤ) - u k) k)) m = y m
    rw [Finset.sum_apply, hyc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold serLine
    split_ifs with h
    · rw [coeff_mk, Int.toNat_of_nonneg h, add_sub_cancel_right]
    · rw [hc m k (not_le.mp h), zero_smul]
  · rintro _ ⟨c, rfl⟩
    change (∑ k, serLine (u k) (d k) (c k)) ∈ _
    refine Submodule.sum_mem _ fun k _ => ?_
    refine Submodule.mem_iSup_of_mem (u k) ⟨fun m hm => ?_, fun m => ?_⟩
    · unfold serLine
      rw [if_neg (by omega)]
    · unfold serLine
      split_ifs
      · rw [hA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, le_refl (u k), rfl⟩)
      · exact Submodule.zero_mem _

theorem spanIsLines_of_graded : ∀ {F M N : Type} [Field F] [AddCommGroup M] [Module F M] (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent (L x)) → (∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) → GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serSpan F (Set.range L) = GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.gradedSer A → GlobalTheory.SenLines.SpanIsLines L u d F := by
  intro F M N _ _ _ L r u d A hL hA h y
  rw [← mem_serSpan_iff L hL, h, gradedSer_eq_range u d A hA]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end GlobalTheory.SenLines.SplitFil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerOfLinApprox
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem ker_of_linApprox : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l))
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), IsSSRep r → LinApprox r C → ∀ s : Γ, (∀ ρ ∈ C, ρ s = 1) → r s = 1 := by
  intro l _ Γ _ a r C hss hC s hs
  have htr : ∀ g, trc r (s * g) = trc r g := by
    intro g
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨t, c, ht, hb⟩ := hC (ε / 2) (by positivity)
    have hsum : ∑ ρ ∈ t, c ρ * trc ρ (s * g) = ∑ ρ ∈ t, c ρ * trc ρ g := by
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      simp [trc, map_mul, hs ρ (ht hρ)]
    rw [dist_eq_norm]
    calc ‖trc r (s * g) - trc r g‖
        = ‖(trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)) - (trc r g - ∑ ρ ∈ t, c ρ * trc ρ g)‖ := by
          rw [hsum]; congr 1; ring
      _ ≤ ‖trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)‖ + ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hb _) (hb _)
      _ = ε := by ring
  set R : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) with hR
  have hM : R s - 1 ∈ Submodule.span (PadicAlgCl l) (Set.range R) := by
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) ?_
    have : R 1 = 1 := by simp [hR]
    rw [← this]; exact Submodule.subset_span ⟨1, rfl⟩
  have h0 := GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss (R s - 1) hM (fun g => by
    have := htr g
    simp only [trc, map_mul, Units.val_mul] at this
    rw [sub_mul, one_mul, Matrix.trace_sub]
    simpa [hR] using sub_eq_zero.2 this)
  ext i j
  have := congrFun (congrFun (sub_eq_zero.1 h0) i) j
  simpa [hR] using this

end GlobalTheory.Cong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmul
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

def unitBallSubring (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] : Subring E where
  carrier := {t | ‖t‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem norm_det_one_add_smul (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
    (x : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ‖(1 + ϖ • x).det‖ = 1 := by
  set O := unitBallSubring E
  let y : Matrix (Fin n) (Fin n) O := fun i j => ⟨x i j, hx i j⟩
  let w : O := ⟨ϖ, hϖ.le⟩
  have hmap : O.subtype.mapMatrix (1 + w • y) = 1 + ϖ • x := by
    rw [map_add (f := _), map_one]
    congr 1
  have hdet : (1 + ϖ • x).det = ((1 + w • y).det : E) := by
    rw [← hmap, ← RingHom.map_det]; rfl
  have hq : (Ideal.Quotient.mk (Ideal.span {w})) (1 + w • y).det = 1 := by
    rw [RingHom.map_det, map_add (f := _), map_one]
    have : (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (w • y) = 0 := by
      ext i j
      simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    rw [this, add_zero, Matrix.det_one]
  have hmem : (1 + w • y).det - 1 ∈ Ideal.span {w} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hq, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc' : ((1 + w • y).det : E) - 1 = (c : E) * ϖ := by
    have := congrArg Subtype.val hc
    simpa [w] using this.symm
  have hlt : ‖(1 + ϖ • x).det - 1‖ < 1 := by
    rw [hdet, hc', norm_mul]
    calc ‖(c : E)‖ * ‖ϖ‖ ≤ 1 * ‖ϖ‖ := mul_le_mul_of_nonneg_right c.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hϖ
  have key : (1 + ϖ • x).det = 1 + ((1 + ϖ • x).det - 1) := by ring
  rw [key, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne')]
  simp [hlt.le]

end GlobalTheory.UnitDiscAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmulStatement
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_norm_det_one_add_smul : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → (∀ i j, ‖x i j‖ ≤ 1) → ‖(1 + ϖ • x).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | exact GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | (intros; apply GlobalTheory.UnitDiscAlg.norm_det_one_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapAevalNab
noncomputable section
namespace GlobalTheory.Models.EPolyModel
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem map_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a) (g' : Vc k b →ₗ[k] Vc k b)
    (h : ∀ x, φ (g x) = g' (φ x)) (x : Vc k a) : φ (nab g x) = nab g' (φ x) := by
  rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, h]

theorem map_aeval_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (f : Polynomial k) (x : Vc k a) :
    φ (Polynomial.aeval (nab g) f x) = Polynomial.aeval (nab g') f (φ x) := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact φ.map_smul_of_tower c x
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval (nab g')), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, map_nab φ g g' h]

theorem comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ)
    (hN : EPoly g' N s) : EPoly g (N.comap (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, fun x hx => ?_⟩
  have h1 := hN (φ x) hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  change φ _ ∈ N
  rwa [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem map {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k a)) (s : ℤ)
    (hN : EPoly g N s) : EPoly g' (N.map (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hN x hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  refine ⟨_, h1, ?_⟩
  change φ _ = _ • nab g' (Polynomial.aeval (nab g') f (φ x))
  rw [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem model_ePoly : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T3 l →
    ∀ (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i, Dt.ty i = LType.Bd →
      EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h3 A N hN i hi
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have oB := M.base_obj B Nb hB
  have o1 := F.obj_sub A₁ B j hj hji oB
  have oA := F.obj_quot A₁ A p hp hps o1
  exact map _ _ _ (F.map_γ A₁ A p o1 oA hp i) _ _
    (comap _ _ _ (F.map_γ A₁ B j o1 oB hj i) _ _ (M.base_e h1 h3 B Nb hB i hi))

end GlobalTheory.Models.EPolyModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfSmulEqZero
noncomputable section

namespace GlobalTheory.AdmLoc

open Formalism.WeaklyAdmissibleFiltrations
open scoped Pointwise

section Sub

variable {O G : Type} [CommRing O] [Group G] {M : Type} [AddCommGroup M] [Module O M]

def IsStab (π : Representation O G M) (X : Submodule O M) : Prop := ∀ g, ∀ x ∈ X, π g x ∈ X

variable {π : Representation O G M}

theorem IsStab.smul {X : Submodule O M} (h : IsStab π X) (c : O) : IsStab π (c • X) := by
  intro g x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x c X).mp hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (h g y hy)

theorem IsStab.sup {X Y : Submodule O M} (h : IsStab π X) (h' : IsStab π Y) : IsStab π (X ⊔ Y) := by
  intro g x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (h g y hy) (h' g z hz)

def subquotRep {X Y : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) :
    Representation O G (↥Y ⧸ X.comap Y.subtype) :=
  (π.subrepresentation Y hY).quotient (X.comap Y.subtype) (fun g x hx => hX g x hx)

theorem subquot_sameSS_prod {X Y Z : Submodule O M} (hX : IsStab π X) (hY : IsStab π Y) (hZ : IsStab π Z)
    (hXY : X ≤ Y) (hYZ : Y ≤ Z) (h : IsFiniteLength O (↥Z ⧸ X.comap Z.subtype)) :
    SameSS (subquotRep hX hZ) ((subquotRep hX hY).prod (subquotRep hY hZ)) := by
  refine SameSS.of_exact
    (f := Submodule.mapQ _ _ (Submodule.inclusion hYZ) (fun _ hx => hx))
    (p := Submodule.mapQ _ _ LinearMap.id (fun _ hx => hXY hx)) ?_ ?_ ?_ ?_ ?_ h
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : Submodule.inclusion hYZ x ∈ X.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr h1
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    constructor
    · intro hx
      have h1 : x ∈ Y.comap Z.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
      exact ⟨Submodule.Quotient.mk ⟨x, h1⟩, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← hy]
      exact (Submodule.Quotient.mk_eq_zero (Y.comap Z.subtype) (x := Submodule.inclusion hYZ y)).mpr y.2

def smulEquiv {c : O} (hc : IsSMulRegular M c) (Y : Submodule O M) : ↥Y ≃ₗ[O] ↥(c • Y) :=
  Submodule.equivMapOfInjective (DistribSMul.toLinearMap O M c) hc Y

theorem subquot_sameSS_smul {c : O} (hc : IsSMulRegular M c) {X Y : Submodule O M} (hX : IsStab π X)
    (hY : IsStab π Y) (h : IsFiniteLength O (↥Y ⧸ X.comap Y.subtype)) :
    SameSS (subquotRep hX hY) (subquotRep (hX.smul c) (hY.smul c)) := by
  refine SameSS.of_equiv h (Submodule.Quotient.equiv _ _ (smulEquiv hc Y) ?_) ?_
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx
    · intro hz
      obtain ⟨y, rfl⟩ := (smulEquiv hc Y).surjective z
      obtain ⟨x, hx, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c X).mp hz
      have hxy' : x = (y : M) := hc hxy
      exact ⟨y, (hxy' ▸ hx : (y : M) ∈ X), rfl⟩
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact (map_smul (π g) c (x : M)).symm

theorem SameSS.prod_comm {A C : Type} [AddCommGroup A] [Module O A] [AddCommGroup C] [Module O C]
    (α : Representation O G A) (γ : Representation O G C) (hA : IsFiniteLength O A) (hC : IsFiniteLength O C) :
    SameSS (α.prod γ) (γ.prod α) :=
  ((SameSS.refl α hA).prod (SameSS.refl γ hC)).congr_right (LinearEquiv.prodComm O A C) (fun _ _ => rfl)

variable [IsDomain O] [IsDiscreteValuationRing O]

theorem finiteLength_of_smul_eq_zero {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] {c : O}
    (hc : c ≠ 0) (h : ∀ x : N, c • x = 0) : IsFiniteLength O N := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O N (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) N := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) N := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem finiteLength_subquot {c : O} (hc : c ≠ 0) {X Y : Submodule O M} (hY : Y.FG) (h : c • Y ≤ X) :
    IsFiniteLength O (↥Y ⧸ X.comap Y.subtype) := by
  haveI : Module.Finite O ↥Y := Module.Finite.iff_fg.mpr hY
  refine finiteLength_of_smul_eq_zero hc fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h (Submodule.smul_mem_pointwise_smul _ _ _ x.2)

theorem fg_smul {Y : Submodule O M} (hY : Y.FG) (c : O) : (c • Y).FG := hY.map _

theorem red_sameSS_step {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M} (hA : IsStab π A)
    (hB : IsStab π B) (fA : A.FG) (fB : B.FG) (h1 : c • A ≤ B) (h2 : B ≤ A) :
    SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have h3 : c • B ≤ c • A := Submodule.map_mono h2
  have e1 := subquot_sameSS_prod (hA.smul c) hB hA h1 h2 (finiteLength_subquot hc0 fA le_rfl)
  have e2 := subquot_sameSS_prod (hB.smul c) (hA.smul c) hB h3 h1 (finiteLength_subquot hc0 fB le_rfl)
  have l1 := finiteLength_subquot hc0 fB h3
  have l2 := finiteLength_subquot hc0 fA h1
  have e3 := subquot_sameSS_smul hc hB hA l2
  exact (e1.trans (SameSS.prod_comm _ _ l1 l2)).trans ((e3.prod (SameSS.refl _ l1)).trans e2.symm)

theorem red_sameSS_of_pow {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {B : Submodule O M} (hB : IsStab π B)
    (fB : B.FG) (n : ℕ) : ∀ {A : Submodule O M} (hA : IsStab π A), A.FG → c ^ n • A ≤ B → B ≤ A →
      SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  induction n with
  | zero =>
    intro A hA fA h1 h2
    rw [pow_zero, one_smul] at h1
    obtain rfl : A = B := le_antisymm h1 h2
    exact SameSS.refl _ (finiteLength_subquot hc0 fA le_rfl)
  | succ n ih =>
    intro A hA fA h1 h2
    have fA' : (B ⊔ c • A).FG := fB.sup (fg_smul fA c)
    refine (red_sameSS_step hc0 hc hA (hB.sup (hA.smul c)) fA fA' le_sup_right
      (sup_le h2 (Submodule.smul_le_self_of_tower c A))).trans (ih _ fA' ?_ le_sup_left)
    rw [Submodule.smul_sup', smul_smul, ← pow_succ]
    exact sup_le (Submodule.smul_le_self_of_tower _ B) h1

theorem red_sameSS_of_commensurable {c : O} (hc0 : c ≠ 0) (hc : IsSMulRegular M c) {A B : Submodule O M}
    (hA : IsStab π A) (hB : IsStab π B) (fA : A.FG) (fB : B.FG) {m n : ℕ} (h1 : c ^ m • A ≤ B)
    (h2 : c ^ n • B ≤ A) : SameSS (subquotRep (hA.smul c) hA) (subquotRep (hB.smul c) hB) := by
  have fS : (A ⊔ B).FG := fA.sup fB
  refine (red_sameSS_of_pow hc0 hc hA fA n (hA.sup hB) fS ?_ le_sup_left).symm.trans
    (red_sameSS_of_pow hc0 hc hB fB m (hA.sup hB) fS ?_ le_sup_right)
  · rw [Submodule.smul_sup']
    exact sup_le (Submodule.smul_le_self_of_tower _ A) h2
  · rw [Submodule.smul_sup']
    exact sup_le h1 (Submodule.smul_le_self_of_tower _ B)

end Sub

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]

def resScal (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V) : Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

variable {ρ : Representation LL G V}

theorem isStab_lattice (L : Lattice (O := O) ρ) : IsStab (resScal O ρ) L.T := L.stable

variable [IsDomain O] [IsDiscreteValuationRing O]

theorem modRep_sameSS_subquot (L : Lattice (O := O) ρ) {c : O} (hc : c ≠ 0) :
    SameSS (subquotRep ((isStab_lattice L).smul c) (isStab_lattice L)) (modRep (latRep L) c) := by
  refine SameSS.of_equiv (finiteLength_subquot hc L.fg le_rfl) (Submodule.quotEquivOfEq _ _ ?_) ?_
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c L.T).mp hx
      exact (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mpr ⟨⟨y, hy⟩, trivial, Subtype.ext hxy⟩
    · intro hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c ⊤).mp hx
      exact Submodule.smul_mem_pointwise_smul _ _ _ y.2
  · intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

variable [IsFractionRing O LL]

theorem exists_pow_smul_mem (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) (v : V) :
    ∃ n : ℕ, lam ^ n • v ∈ L.T := by
  have hv : v ∈ Submodule.span LL (L.T : Set V) := by rw [L.span]; trivial
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) v hv
  rw [Submodule.span_eq] at hs
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero s.2) hlam
  refine ⟨n, ?_⟩
  have h := L.T.smul_mem ((u⁻¹ : Oˣ) : O) hs
  rwa [Submonoid.smul_def, smul_smul, hu, Units.inv_mul_cancel_left] at h

theorem exists_pow_smul_le (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam) {A : Submodule O V}
    (hA : A.FG) : ∃ n : ℕ, lam ^ n • A ≤ L.T := by
  induction A, hA using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := exists_pow_smul_mem L hlam x
    refine ⟨n, ?_⟩
    rw [Submodule.smul_span, Set.smul_set_singleton, Submodule.span_singleton_le_iff_mem]
    exact hn
  | sup A B _ _ hA hB =>
    obtain ⟨m, hm⟩ := hA
    obtain ⟨n, hn⟩ := hB
    refine ⟨m + n, ?_⟩
    rw [Submodule.smul_sup']
    refine sup_le ?_ ?_
    · rw [pow_add, mul_comm, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hm
    · rw [pow_add, ← smul_smul]
      exact (Submodule.smul_le_self_of_tower _ _).trans hn

theorem lattice_reduction_sameSS {lam : O} (hlam : Irreducible lam) (L L' : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) lam) (modRep (latRep L') lam) := by
  have h0 : lam ≠ 0 := hlam.ne_zero
  have hreg : IsSMulRegular V lam := by
    intro x y hxy
    have h1 : algebraMap O LL lam ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).mpr h0
    have h2 : algebraMap O LL lam • x = algebraMap O LL lam • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V h1 h2
  obtain ⟨m, hm⟩ := exists_pow_smul_le L' hlam L.fg
  obtain ⟨n, hn⟩ := exists_pow_smul_le L hlam L'.fg
  exact ((modRep_sameSS_subquot L h0).symm.trans
    (red_sameSS_of_commensurable h0 hreg (isStab_lattice L) (isStab_lattice L') L.fg L'.fg hm hn)).trans
    (modRep_sameSS_subquot L' h0)

end Lat

end GlobalTheory.AdmLoc
end
end
