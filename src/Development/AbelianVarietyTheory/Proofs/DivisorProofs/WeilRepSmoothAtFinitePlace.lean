module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedForms
open Topology Filter

namespace GlobalTheory

theorem span_finiteDimensional_of_bounded_forms {V : Type} [AddCommGroup V] [Module ℂ V]
    (s : Set V) (hs : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) :
    FiniteDimensional ℂ (Submodule.span ℂ s) := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent ℂ s
  have ht : t.Finite := by
    by_contra hinf
    have hinf' : t.Infinite := hinf
    let e : ℕ ↪ t := hinf'.natEmbedding
    have hli' : LinearIndepOn ℂ id t := hli
    let b := Module.Basis.extend hli'
    let v : (hli'.extend (Set.subset_univ t)) → ℂ := fun i =>
      if h : ∃ k : ℕ, ((e k : t) : V) = (i : V) then (h.choose : ℂ) else 0
    obtain ⟨C, hC⟩ := hs (b.constr ℂ v)
    have key : ∀ k : ℕ, b.constr ℂ v ((e k : t) : V) = (k : ℂ) := by
      intro k
      have hmem : ((e k : t) : V) ∈ hli'.extend (Set.subset_univ t) :=
        hli'.subset_extend _ (e k).2
      have hb : b ⟨_, hmem⟩ = ((e k : t) : V) := by simp [b, Module.Basis.coe_extend]
      rw [← hb, Module.Basis.constr_basis]
      have h : ∃ j : ℕ, ((e j : t) : V) = ((⟨_, hmem⟩ : hli'.extend (Set.subset_univ t)) : V) :=
        ⟨k, rfl⟩
      simp only [v, dif_pos h]
      have hj : h.choose = k := e.injective (Subtype.ext h.choose_spec)
      rw [hj]
    obtain ⟨k, hk⟩ := exists_nat_gt C
    have hle := hC _ (hts (e k).2)
    rw [key, Complex.norm_natCast] at hle
    linarith
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ t) := FiniteDimensional.span_of_finite ℂ ht
  rw [hspan] at hfd
  exact hfd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFiniteDimensionalOfBoundedFormsStatement
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s) := by
  first | exact @GlobalTheory.span_finiteDimensional_of_bounded_forms | exact GlobalTheory.span_finiteDimensional_of_bounded_forms | (intros; apply GlobalTheory.span_finiteDimensional_of_bounded_forms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsFixOfContinuousCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsFixOfContinuousCoefficients
open Topology Filter

namespace GlobalTheory.SmoothFix

theorem eq_one_of_pow_norm_sub_one_le_half {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_nhds_fix : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  intro hfd G _ _ H V _ _ S hmul h1 hcont hsmall v
  obtain ⟨K₀, hK₀H, hK₀c, ⟨O₀, hO₀o, hO₀1, hO₀K⟩, -⟩ := hsmall Set.univ univ_mem
  let s : Set V := (fun k => S k v) '' (K₀ : Set G)
  have hb : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C := by
    intro l
    obtain ⟨C, hC⟩ := hK₀c.exists_bound_of_continuousOn ((hcont l v).mono hK₀H)
    exact ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hC k hk⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ s) := hfd s hb
  set W := Submodule.span ℂ s with hW
  have hinv : ∀ k ∈ K₀, ∀ w ∈ W, S k w ∈ W := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      show S k (S k' v) ∈ W
      rw [← Module.End.mul_apply, ← hmul k (hK₀H hk) k' (hK₀H hk')]
      exact Submodule.subset_span ⟨k * k', K₀.mul_mem hk hk', rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  let R : K₀ → Module.End ℂ W := fun k => (S k).restrict (hinv k.1 k.2)
  have hRv : ∀ (k : K₀) (w : W), (R k w : V) = S k w := fun _ _ => rfl
  have hRpow : ∀ (k : K₀) (m : ℕ), R (k ^ m) = R k ^ m := by
    intro k m
    induction m with
    | zero =>
      ext w
      simp [hRv, h1]
    | succ m ih =>
      ext w
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih, hRv, hRv, hRv]
      have hm : ((k ^ m : K₀) : G) ∈ H := hK₀H (k ^ m).2
      simp only [Subgroup.coe_mul]
      rw [hmul _ hm _ (hK₀H k.2), Module.End.mul_apply]
  let b := Module.finBasis ℂ W
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  let M : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ := fun x i j => c i (S x (b j))
  have hMR : ∀ k : K₀, LinearMap.toMatrixAlgEquiv b (R k) = M k := by
    intro k
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have := LinearMap.congr_fun (hc i) (R k (b j))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    rw [← this, hRv]
  have hR1 : R 1 = 1 := by
    ext w
    simp [hRv, h1]
  have hM1 : M 1 = 1 := by
    have := hMR 1
    rw [hR1, map_one] at this
    simpa using this.symm
  have hM : ContinuousOn M (H : Set G) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont (c i) (b j)
  have hN : ContinuousWithinAt (fun x => ‖M x - 1‖) (H : Set G) 1 :=
    ((hM 1 H.one_mem).sub continuousWithinAt_const).norm
  have hev : {x | ‖M x - 1‖ < 1 / 2} ∈ 𝓝[(H : Set G)] 1 :=
    hN (Iio_mem_nhds (by show ‖M 1 - 1‖ < 1 / 2; rw [hM1, sub_self, norm_zero]; norm_num))
  obtain ⟨u, hu, h1u, hsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨K, hKH, -, ⟨O, hOo, hO1, hOK⟩, hKU⟩ :=
    hsmall (u ∩ O₀) (Filter.inter_mem (hu.mem_nhds h1u) (hO₀o.mem_nhds hO₀1))
  have hvW : v ∈ W := Submodule.subset_span ⟨1, K₀.one_mem, by simp [h1]⟩
  refine ⟨O, hOo.mem_nhds hO1, fun x hxO hxH => ?_⟩
  have hxK : x ∈ K := hOK x hxO hxH
  have hxK₀ : x ∈ K₀ := hO₀K x (hKU hxK).2 (hKH hxK)
  let kk : K₀ := ⟨x, hxK₀⟩
  have hpow : ∀ m : ℕ, ‖(LinearMap.toMatrixAlgEquiv b (R kk)) ^ m - 1‖ ≤ 1 / 2 := by
    intro m
    rw [← map_pow, ← hRpow, hMR]
    have hm : x ^ m ∈ K := K.pow_mem hxK m
    have := hsub ⟨(hKU hm).1, hKH hm⟩
    exact le_of_lt (by simpa using this)
  have hone := eq_one_of_pow_norm_sub_one_le_half hpow
  rw [← map_one (LinearMap.toMatrixAlgEquiv b)] at hone
  have hRk := (LinearMap.toMatrixAlgEquiv b).injective hone
  have := congrArg Subtype.val (LinearMap.congr_fun hRk ⟨v, hvW⟩)
  simpa [hRv] using this

end GlobalTheory.SmoothFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsFixOfContinuousCoefficientsStatement
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  first | exact @GlobalTheory.SmoothFix.exists_nhds_fix | exact GlobalTheory.SmoothFix.exists_nhds_fix | (intros; apply GlobalTheory.SmoothFix.exists_nhds_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSmoothAtFinitePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) :
    (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  show u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
  simp

theorem mul_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g h : UA σ X.J} (hg : g ∈ UAt σ X ev) (hh : h ∈ UAt σ X ev) : g * h ∈ UAt σ X ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    show mat g * mat h - 1 = _
    noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem inv_mem_uAt {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R)
    {g : UA σ X.J} (hg : g ∈ UAt σ X ev) : g⁻¹ ∈ UAt σ X ev := by
  intro u hu
  have h1 : mat g⁻¹ * mat g = 1 := by
    show ((g⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1
    rw [inv_mul_cancel]; rfl
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def locGrp {σ : E →ₐ[F] E} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    Subgroup (UA σ X.J × UA σ W.J) where
  carrier := {x | x.1 ∈ UAt σ X (evFin F v) ∧ x.2 ∈ UAt σ W (evFin F v)}
  one_mem' := ⟨one_mem_uAt X _, one_mem_uAt W _⟩
  mul_mem' ha hb := ⟨mul_mem_uAt X _ ha.1 hb.1, mul_mem_uAt W _ ha.2 hb.2⟩
  inv_mem' ha := ⟨inv_mem_uAt X _ ha.1, inv_mem_uAt W _ ha.2⟩

def tensL {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (R : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ R
  map_add' φ ψ := funext fun x => by simp [tens, add_mul]
  map_smul' c φ := funext fun x => by simp [tens, mul_assoc]

def locOp {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (R : (κ → AF F) → ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Module.End ℂ ((κ → Fv F v) → ℂ) :=
  (R 0)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun (t : κ → Fv F v) i => GlobalTheory.LatVac.liftV v (t i)) ∘ₗ T ∘ₗ tensL v R)

theorem tens_liftV {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {R : (κ → AF F) → ℂ} (φ : (κ → Fv F v) → ℂ)
    (hR : Rest (evFin F v) φ R) (t : κ → Fv F v) :
    tens (evFin F v) φ R (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ t * R 0 := by
  have h1 := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i)) fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (t i) u hu
  rw [zero_add] at h1
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, h1]

theorem locOp_eq {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0) {φ φ₁ : (κ → Fv F v) → ℂ}
    (hR : Rest (evFin F v) φ R) (hR₁ : Rest (evFin F v) φ₁ R) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    (h : Acts (evFin F v) T φ φ₁) : locOp v R T φ = φ₁ := by
  funext t
  have := h R hR
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply]
  change (R 0)⁻¹ • T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)) = φ₁ t
  rw [this, tens_liftV v φ₁ hR₁ t, smul_eq_mul]
  field_simp

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_fst (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) : (GlobalTheory.LatVac.liftV v a).1 = 0 := rfl


open scoped Classical in
theorem continuous_locOp {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil B.ψ χX χW om) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (R : (Fin n × Fin d → AF F) → ℂ) (φ : (Fin n × Fin d → Fv F v) → ℂ)
    (hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d))
    (lam : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ) :
    Continuous fun x : UA σ X.J × UA σ W.J => lam (locOp v R (om x) φ) := by
  let L : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun (t : Fin n × Fin d → Fv F v) i => GlobalTheory.LatVac.liftV v (t i))
  have hl : lam ∘ₗ L ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨lam (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : L (GlobalTheory.WeilM.pureA F f g) = f 0 • (fun t => g (fun i => (GlobalTheory.LatVac.liftV v (t i)).2)) := by
      funext t
      simp only [L, LinearMap.funLeft_apply, GlobalTheory.WeilM.pureA, liftV_fst, map_zero, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [LinearMap.comp_apply, e, map_smul, smul_eq_mul, _root_.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hc := hW.2.2 (lam ∘ₗ L) hl _ hΦ
  have h2 : Continuous fun x : UA σ X.J × UA σ W.J => (R 0)⁻¹ * (lam ∘ₗ L) (om x (tens (evFin F v) φ R)) :=
    continuous_const.mul hc
  refine h2.congr fun x => ?_
  simp only [locOp, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_eq_mul]
  rfl

end GlobalTheory.SmoothAtPlace

namespace GlobalTheory.SmoothAtPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem weil_smooth_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    (∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁) →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      ∀ x ∈ U, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) → x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v hActs φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  let H := locGrp (σ := σ) X W v
  let V := GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)
  have key : ∀ x ∈ H, ∀ ψ ∈ V, locOp v R (om x) ψ ∈ V ∧ Acts (evFin F v) (om x) ψ (locOp v R (om x) ψ) := by
    intro x hx ψ hψ
    obtain ⟨ψ₁, hψ₁, hA⟩ := hActs x hx.1 hx.2 ψ hψ
    rw [locOp_eq v hR0 (hR ψ hψ) (hR ψ₁ hψ₁) hA]
    exact ⟨hψ₁, hA⟩
  classical
  let S : UA σ X.J × UA σ W.J → Module.End ℂ V := fun x =>
    if hx : x ∈ H then (locOp v R (om x)).restrict (fun ψ hψ => (key x hx ψ hψ).1) else LinearMap.id
  have hS : ∀ x (hx : x ∈ H) (ψ : V), ((S x ψ : V) : (Fin n × Fin d → Fv F v) → ℂ) = locOp v R (om x) ψ := by
    intro x hx ψ
    simp only [S, dif_pos hx]
    rfl
  have hmul : ∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y := by
    intro x hx y hy
    ext ψ : 1
    apply Subtype.ext
    rw [hS _ (H.mul_mem hx hy), Module.End.mul_apply, hS _ hx, hS _ hy]
    have h1 := key y hy ψ ψ.2
    have h2 := key x hx _ h1.1
    refine locOp_eq v hR0 (hR ψ ψ.2) (hR _ h2.1) fun r hr => ?_
    have hr' : Rest (evFin F v) (locOp v R (om y) ψ) r := ⟨hr.1, by
      rw [← h1.2 r hr]
      exact (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil).pres y _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1.2 r hr, h2.2 r hr']
  have hone : S 1 = 1 := by
    ext ψ : 1
    apply Subtype.ext
    rw [hS 1 H.one_mem]
    exact locOp_eq v hR0 (hR ψ ψ.2) (hR ψ ψ.2) fun r _ => by rw [map_one]; rfl
  have hcont : ∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set (UA σ X.J × UA σ W.J)) := by
    intro l w
    obtain ⟨lam, hlam⟩ := LinearMap.exists_extend l
    refine (continuous_locOp hP.weil v R w.1 (hR w.1 w.2).2 lam).continuousOn.congr fun x hx => ?_
    have : S x w = ⟨locOp v R (om x) w, (key x hx w w.2).1⟩ := Subtype.ext (hS x hx w)
    rw [this, ← hlam]
    rfl
  have hbasis : ∀ U ∈ 𝓝 (1 : UA σ X.J × UA σ W.J), ∃ K : Subgroup (UA σ X.J × UA σ W.J), K ≤ H ∧
      IsCompact (K : Set (UA σ X.J × UA σ W.J)) ∧
      (∃ O : Set (UA σ X.J × UA σ W.J), IsOpen O ∧ (1 : UA σ X.J × UA σ W.J) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧
      (K : Set (UA σ X.J × UA σ W.J)) ⊆ U := by
    intro U hU
    rw [show (1 : UA σ X.J × UA σ W.J) = (1, 1) from rfl, nhds_prod_eq] at hU
    obtain ⟨U1, hU1, U2, hU2, hsub⟩ := Filter.mem_prod_iff.1 hU
    obtain ⟨K1, hK1H, hK1c, ⟨O1, hO1, h1O1, hO1K⟩, hK1U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ X v U1 hU1
    obtain ⟨K2, hK2H, hK2c, ⟨O2, hO2, h1O2, hO2K⟩, hK2U⟩ := GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace hσ W v U2 hU2
    refine ⟨K1.prod K2, fun x hx => ⟨hK1H _ hx.1, hK2H _ hx.2⟩, ?_,
      ⟨O1 ×ˢ O2, hO1.prod hO2, ⟨h1O1, h1O2⟩, fun x hx hxH => ⟨hO1K _ hx.1 hxH.1, hO2K _ hx.2 hxH.2⟩⟩,
      fun x hx => hsub ⟨hK1U hx.1, hK2U hx.2⟩⟩
    rw [Subgroup.coe_prod]
    exact hK1c.prod hK2c
  obtain ⟨U, hU, hfix⟩ := GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients GlobalTheory.T.finiteDimensional_span_of_forall_linear_bounded H S hmul hone hcont hbasis ⟨φ, hφ⟩
  refine ⟨U, hU, fun x hxU hx1 hx2 => ?_⟩
  have hx : x ∈ H := ⟨hx1, hx2⟩
  have e := congrArg Subtype.val (hfix x hxU hx)
  rw [hS x hx] at e
  have := (key x hx φ hφ).2
  rwa [e] at this

end GlobalTheory.SmoothAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSmoothAtFinitePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_smooth_at_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    (∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁) →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      ∀ x ∈ U, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) → x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ := by
  first | exact @GlobalTheory.SmoothAtPlace.weil_smooth_at | exact GlobalTheory.SmoothAtPlace.weil_smooth_at | (intros; apply GlobalTheory.SmoothAtPlace.weil_smooth_at <;> assumption)
end
