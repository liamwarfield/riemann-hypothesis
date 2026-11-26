module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigIdxFiniteTypesCOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexExtension
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.RamRational

section General

variable {K V W M N ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ}

theorem exists_complex_extension [Fintype ι] (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)
    (hli : LinearIndependent ℂ (fun i => e (b i))) (g : V →ₛₗ[σ] N) :
    ∃ G : M →ₗ[ℂ] N, ∀ x, G (e x) = g x := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℂ (fun i => g (b i))) ∘ₗ hli.repr)
  have hb : ∀ i, G (e (b i)) = g (b i) := by
    intro i
    have hm : e (b i) ∈ Submodule.span ℂ (Set.range (fun i => e (b i))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 := LinearMap.congr_fun hG ⟨e (b i), hm⟩
    have h2 : hli.repr ⟨e (b i), hm⟩ = Finsupp.single i 1 := hli.repr_eq_single i _ rfl
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, h2,
      Finsupp.linearCombination_single, one_smul] at h1
    exact h1
  refine ⟨G, fun x => ?_⟩
  rw [← b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, hb, RingHom.id_apply]

theorem mem_span_of_kernel [Fintype ι] {J : Type} [Fintype J] (e : V →ₛₗ[σ] M)
    (b : Module.Basis ι K V) (hli : LinearIndependent ℂ (fun i => e (b i)))
    (F : J → M →ₗ[ℂ] M) (hF : ∀ j x, ∃ y, e y = F j (e x)) (m : M)
    (hm : m ∈ Submodule.span ℂ (Set.range (fun i => e (b i)))) (h0 : ∀ j, F j m = 0) :
    m ∈ Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0}) := by
  classical
  have hinj := inj_of_li σ e b hli
  let f : J → V →ₗ[K] V := fun j => descend e e hinj (F j) (hF j)
  have hf : ∀ j x, e (f j x) = F j (e x) := fun j x => descend_spec e e hinj (F j) (hF j) x
  let g : V →ₗ[K] (J → V) := LinearMap.pi f
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨h, hh⟩ := LinearMap.exists_extend s
  have hg : ∀ x, g (h (g x)) = g x := by
    intro x
    have h1 : h (g x) = s (g.rangeRestrict x) := LinearMap.congr_fun hh (g.rangeRestrict x)
    have h2 := LinearMap.congr_fun hs (g.rangeRestrict x)
    rw [h1]
    exact congrArg Subtype.val h2
  choose H hH using fun j : J =>
    exists_complex_extension e b hli (e.comp (h ∘ₗ LinearMap.single K (fun _ : J => V) j))
  let P : M →ₗ[ℂ] M := LinearMap.id - ∑ j, H j ∘ₗ F j
  have hP : ∀ x, P (e x) = e (x - h (g x)) := by
    intro x
    have h1 : g x = ∑ j, Pi.single j (f j x) := (Finset.univ_sum_single (g x)).symm
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, map_sub, map_sum, ← hf, hH, LinearMap.coe_single]
  have hPm : P m = m := by
    simp [P, LinearMap.sum_apply, h0]
  rw [← hPm]
  have hle : Submodule.span ℂ (Set.range (fun i => e (b i))) ≤
      (Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0})).comap P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨b i - h (g (b i)), fun j => ?_, (hP _).symm⟩
    have h1 : g (b i - h (g (b i))) = 0 := by rw [map_sub, hg, sub_self]
    have h2 : f j (b i - h (g (b i))) = 0 := congrFun h1 j
    rw [← hf, h2, map_zero]
  exact hle hm

theorem preserves_of_span (e : V →ₛₗ[σ] M) (S : Set V) (hS : Submodule.span K S = ⊤)
    (F : M →ₗ[ℂ] M) (hF : ∀ x ∈ S, ∃ y, e y = F (e x)) (x : V) : ∃ y, e y = F (e x) := by
  have hx : x ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hF x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by simp [LinearMap.map_smulₛₗ, ha]⟩

end General

theorem span_ramSub {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL]
    {embLL : LL →+* ℂ} {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
    {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) :
    Submodule.span ℂ (M.emb 0 '' (M.ramSub : Set (M.lat 0).V)) = A.Mram := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro m hm
    have hsp : Submodule.span ℂ (Set.range (fun a => M.emb 0 ((M.lat 0).b a))) = A.Mu0 :=
      (M.emb_basis 0).2.trans M.Fi_zero
    have hrho : ∀ v a x, ∃ y, M.emb 0 y = A.rhoT v a (M.emb 0 x) := fun v a =>
      preserves_of_span (M.emb 0) _ (M.lat_good 0).2.2 (A.rhoT v a) (fun x hx => by
        obtain ⟨y, -, hy⟩ := M.rhoT_lat v a x hx
        exact ⟨y, hy⟩)
    have hNm : ∀ v x, ∃ y, M.emb 0 y = A.Nm v (M.emb 0 x) := by
      intro v x
      choose y hy using fun a => hrho v a x
      exact ⟨∑ a, y a, by simp only [map_sum, hy, ColumnsAtT.Nm, LinearMap.sum_apply]⟩
    have hall : ∀ x, M.emb 0 x ∈ A.Mu0 := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsp, ← (M.lat 0).b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := mem_span_of_kernel (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 A.Nm hNm m
      (hsp ▸ hm.1) (fun v => (Submodule.mem_iInf _).1 hm.2 v)
    refine Submodule.span_mono (Set.image_mono ?_) h
    intro x hx
    exact ⟨hall x, (Submodule.mem_iInf _).2 hx⟩

theorem span_ramSub_cols : ∀ (B : Base) (C : Cols B) (u : B.Word),
    Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) =
      (C.mem u).A.Mram :=
  fun _ C u => span_ramSub (C.fm u)

end GlobalTheory.RamRational
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedFrames
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem

theorem cnorm_mulVec_eq_of_gram {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (M : Matrix ι μ ℂ) (N : Matrix κ μ ℂ) (h : Mᴴ * M = Nᴴ * N) (u : μ → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M.mulVec u) = Formalism.HermitianLatticesTheory.cnorm (N.mulVec u) := by
  have key : ∀ {ι : Type} [Fintype ι] (M : Matrix ι μ ℂ),
      ((∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ (Mᴴ * M).mulVec u := by
    intro ι _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  have h2 : (∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) = ∑ i, ‖N.mulVec u i‖ ^ 2 := by
    have := key M
    rw [h, ← key N] at this
    exact_mod_cast this
  unfold Formalism.HermitianLatticesTheory.cnorm
  rw [h2]

theorem exists_restricted_frames : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (U : Submodule K A.V) (L : Submodule (𝓞 K) U), (∀ v, IsUnit (A.X v).det) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K U) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      (∀ v, IsUnit (X v).det) ∧
        ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v x = Formalism.HermitianLatticesTheory.normAt A.b A.X v (x : A.V) := by
  intro K _ _ _ A U _ hX
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  let n := Module.finrank K U
  let b : Module.Basis (Fin n) K U := Module.finBasis K U
  let E : Matrix A.ι (Fin n) K := LinearMap.toMatrix b A.b U.subtype
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  have hLE : LinearMap.toMatrix A.b b g * E = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  let M : InfinitePlace K → Matrix A.ι (Fin n) ℂ := fun v => (A.X v)⁻¹ * E.map v.embedding
  have hM : ∀ v, Function.Injective (M v).mulVec := by
    intro v x y hxy
    have h1 : ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v) * M v = 1 := by
      simp only [M]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.X v), Matrix.mul_nonsing_inv _ (hX v),
        Matrix.one_mul, ← Matrix.map_mul, hLE, Formalism.L2.DIV.map_one']
    have := congrArg ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hP : ∀ v, ((M v)ᴴ * M v).PosDef := fun v => Matrix.PosDef.conjTranspose_mul_self _ (hM v)
  refine ⟨n, b, fun v => Formalism.L2.DIV.frameOf ((M v)ᴴ * M v),
    fun v => (Formalism.L2.DIV.frameOfSpec n _ (hP v)).1, fun v x => ?_⟩
  have h2 := (Formalism.L2.DIV.frameOfSpec n _ (hP v)).2
  have h3 : Formalism.HermitianLatticesTheory.vecAt A.b v (x : A.V) = (E.map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    have h4 := LinearMap.toMatrix_mulVec_repr b A.b U.subtype x
    funext i
    have h5 := congrFun h4 i
    simp only [Submodule.subtype_apply] at h5
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← h5]
    simp [Matrix.mulVec, dotProduct, E, Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  rw [h3, Matrix.mulVec_mulVec]
  exact cnorm_mulVec_eq_of_gram _ _ h2 _

end GlobalTheory.Mem

end
end

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem linearIndependent_semilinear_of_basis {K : Type} [Field K] (e : K →+* ℂ) {V : Type} [AddCommGroup V]
    [Module K V] {W : Type} [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) {ι κ : Type}
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun i => j (b i))) (v : κ → V)
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => j (v i)) := by
  classical
  set S : Submodule ℂ W := Submodule.span ℂ (Set.range fun i => j (b i)) with hS
  have hmem : ∀ x, j x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact S.add_mem hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
  let j' : V →ₛₗ[e] S := j.codRestrict S hmem
  have h1 : LinearIndependent ℂ (fun i => j' (b i)) :=
    LinearIndependent.of_comp S.subtype hb
  have h2 : Submodule.span ℂ (Set.range fun i => j' (b i)) = ⊤ := by
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  let b' := Module.Basis.extend (hv.linearIndepOn_id)
  have h3 := (GlobalTheory.semilinear_basis_image_indep_of_basis K e V S j' ι _ b b' ⟨h1, h2⟩).1
  have h4 := h3.map' S.subtype S.ker_subtype
  let f : κ → (hv.linearIndepOn_id).extend (Set.subset_univ _) := fun i =>
    ⟨v i, (hv.linearIndepOn_id).subset_extend _ ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hv.injective (congrArg Subtype.val h)
  have h5 := h4.comp f hf
  have h6 : (fun i => j (v i)) = (⇑S.subtype ∘ fun i => j' (b' i)) ∘ f := by
    funext i
    simp [b', f, j', Module.Basis.extend_apply_self]
  rw [h6]
  exact h5

def coordForm {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) : (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

theorem coordForm_basisFun {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) (i : Fin n) : coordForm e c (Pi.basisFun K (Fin n) i) = c i := by
  classical
  show ∑ k, e (Pi.basisFun K (Fin n) i k) • c k = c i
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

def ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) :
    (C.fm u).ramSub →ₛₗ[B.embLL] W.Mu u where
  toFun x := (W.eMu u).symm ⟨(C.fm u).emb 0 x, x.2⟩
  map_add' x y := by
    rw [← map_add (f := _)]; congr 1; ext1; simp
  map_smul' a x := by
    rw [← map_smul]; congr 1; ext1; simp [map_smulₛₗ]

theorem eMu_ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) (x : (C.fm u).ramSub) :
    ((W.eMu u (ramForm W u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) =
      (C.fm u).emb 0 x := by
  show ((W.eMu u ((W.eMu u).symm _) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = _
  rw [LinearEquiv.apply_symm_apply]

theorem ramForm_basis {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) {κ : Type}
    (b : Module.Basis κ B.LL (C.fm u).ramSub) :
    LinearIndependent ℂ (fun i => ramForm W u (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) = ⊤ := by
  let g : W.Mu u →ₗ[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) :=
    (C.mem u).A.Mram.subtype ∘ₗ (W.eMu u).toLinearMap
  have hg : ∀ x, g (ramForm W u x) = (C.fm u).emb 0 x := eMu_ramForm W u
  have hginj : Function.Injective g := (C.mem u).A.Mram.injective_subtype.comp (W.eMu u).injective
  constructor
  · apply LinearIndependent.of_comp g
    have := linearIndependent_semilinear_of_basis B.embLL ((C.fm u).emb 0) ((C.fm u).lat 0).b
      ((C.fm u).emb_basis 0).1 (fun i => ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V))
      (b.linearIndependent.map' (C.fm u).ramSub.subtype (Submodule.ker_subtype _))
    have h6 : (⇑g ∘ fun i => ramForm W u (b i)) =
        fun i => (C.fm u).emb 0 ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V) := funext fun i => hg _
    rw [h6]
    exact this
  · set S := Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) with hS
    have hmem : ∀ x, ramForm W u x ∈ S := by
      intro x
      have hx : x ∈ Submodule.span B.LL (Set.range b) := by rw [b.span_eq]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact S.add_mem hy hz
      | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
    rw [eq_top_iff]
    intro φ _
    have h1 : g φ ∈ (C.mem u).A.Mram := (W.eMu u φ).2
    rw [← GlobalTheory.RamRational.span_ramSub_cols B C u] at h1
    have h2 : Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) ≤ S.map g := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hmem ⟨x, hx⟩, hg _⟩
    obtain ⟨ψ, hψ, hψ'⟩ := h2 h1
    rwa [← hginj hψ']

theorem exists_divStage (B : Base) (C : Cols B) (W : RowsRest B C) (n : ℕ) (c : Module.Basis (Fin n) ℂ W.EE)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (hXo : ∀ v, IsUnit (Xo v).det)
    (Lr : Submodule (𝓞 B.LL) (Fin n → B.LL)) (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V)
    (Bk : ∀ u, ((C.fm u).lat 0).V →ₗ[B.LL] Module.Dual B.LL (Fin n → B.LL)) (h : B.Word → ℝ) (etaF : ℝ) :
    ∃ (V : DivStage B C W) (e : V.div.RR.V ≃ₗ[B.LL] (Fin n → B.LL)),
      (∀ x, V.jEE x = ∑ i, B.embLL (e x i) • c i) ∧ (∀ x, x ∈ V.div.RR.L ↔ e x ∈ Lr) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x, Formalism.HermitianLatticesTheory.normAt V.div.RR.b V.div.RR.X v x =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v (e x)) ∧
      (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧
      (∀ u φ x, V.div.Bk u φ x = Bk u (V.nuIn u φ) (e x)) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧
      V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax := by
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL W.EE n c Lr
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else Xo v
  let RR : HLat B.LL :=
    { V := Fin n → B.LL, ι := Fin n, b := Pi.basisFun B.LL (Fin n), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let D : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := fun u => (Bk u) ∘ₗ (C.fm u).ramSub.subtype, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := W.Dall, delP := W.delp,
      delP_le_one := W.delp_le_one }
  let V : DivStage B C W :=
    { div := D
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := coordForm B.embLL c
      jEE_basis := by
        have : (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) = c :=
          funext (coordForm_basisFun B.embLL c)
        show LinearIndependent ℂ (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) ∧
          Submodule.span ℂ (Set.range (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i))) = ⊤
        rw [this]
        exact ⟨c.linearIndependent, c.span_eq⟩
      jN := ramForm W
      jN_basis := fun u => ramForm_basis W u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => eMu_ramForm W u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, LinearEquiv.refl _ _, fun x => rfl, fun x => Iff.rfl, fun v hv x => ?_, fun u x => Iff.rfl,
    fun u φ x => rfl, rfl, rfl, rfl⟩
  show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X v x = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v x
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]

end GlobalTheory.Mem

end
