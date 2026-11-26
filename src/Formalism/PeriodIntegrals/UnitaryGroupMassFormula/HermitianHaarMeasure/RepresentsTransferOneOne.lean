module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepOnOfEq
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.SmoothLevZero
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepOnAlgebraMap
open MeasureTheory

noncomputable section

namespace PI.QnHermHaar.Gen

variable {α β : Type*} [MeasurableSpace α]

def pr (μ : Measure α) (ι : α → β) (f h : β → ℂ) : ℂ := ∫ x, f (ι x) * star (h (ι x)) ∂μ

def IntOn (μ : Measure α) (ι : α → β) (𝓕 : Submodule ℂ (β → ℂ)) : Prop :=
  ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, Integrable (fun x => f (ι x) * star (h (ι x))) μ

variable {μ : Measure α} {ι : α → β} {𝓕 : Submodule ℂ (β → ℂ)}

theorem pr_conj (f h : β → ℂ) : pr μ ι h f = star (pr μ ι f h) := by
  simp only [pr]
  rw [show star (∫ x, f (ι x) * star (h (ι x)) ∂μ) = (starRingEnd ℂ) (∫ x, f (ι x) * star (h (ι x)) ∂μ) from rfl,
    ← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

theorem pr_smul_left (c : ℂ) (f h : β → ℂ) : pr μ ι (c • f) h = c * pr μ ι f h := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem pr_add_left (hI : IntOn μ ι 𝓕) {f f' h : β → ℂ} (hf : f ∈ 𝓕) (hf' : f' ∈ 𝓕) (hh : h ∈ 𝓕) :
    pr μ ι (f + f') h = pr μ ι f h + pr μ ι f' h := by
  simp only [pr, Pi.add_apply, add_mul]
  exact integral_add (hI f hf h hh) (hI f' hf' h hh)

theorem pr_sub_left (hI : IntOn μ ι 𝓕) {f f' h : β → ℂ} (hf : f ∈ 𝓕) (hf' : f' ∈ 𝓕) (hh : h ∈ 𝓕) :
    pr μ ι (f - f') h = pr μ ι f h - pr μ ι f' h := by
  simp only [pr, Pi.sub_apply, sub_mul]
  exact integral_sub (hI f hf h hh) (hI f' hf' h hh)

def N (hI : IntOn μ ι 𝓕) : Submodule ℂ 𝓕 where
  carrier := {f | ∀ h ∈ 𝓕, pr μ ι f.1 h = 0}
  zero_mem' := by
    intro h _
    simp [pr]
  add_mem' := by
    intro a b ha hb h hh
    simp only [Submodule.coe_add]
    rw [pr_add_left hI a.2 b.2 hh, ha h hh, hb h hh, add_zero]
  smul_mem' := by
    intro c a ha h hh
    simp only [Submodule.coe_smul]
    rw [pr_smul_left, ha h hh, mul_zero]

abbrev X (hI : IntOn μ ι 𝓕) := 𝓕 ⧸ N hI

variable (hI : IntOn μ ι 𝓕)

def rep (x : X hI) : 𝓕 := (Submodule.Quotient.mk_surjective (N hI) x).choose

theorem mk_rep (x : X hI) : Submodule.Quotient.mk (rep hI x) = x := (Submodule.Quotient.mk_surjective (N hI) x).choose_spec

private theorem pr_left_eq_of_sub_mem_N {f f' : 𝓕} (hf : f - f' ∈ N hI) (h : β → ℂ) (hh : h ∈ 𝓕) :
    pr μ ι f.1 h = pr μ ι f'.1 h := by
  have hf' : ∀ k ∈ 𝓕, pr μ ι (f - f').1 k = 0 := hf
  have := hf' h hh
  rw [Submodule.coe_sub, pr_sub_left hI f.2 f'.2 hh] at this
  exact sub_eq_zero.mp this

theorem pr_eq_of_sub {f f' h h' : 𝓕} (hf : f - f' ∈ N hI) (hh : h - h' ∈ N hI) :
    pr μ ι f.1 h.1 = pr μ ι f'.1 h'.1 := by
  rw [pr_left_eq_of_sub_mem_N hI hf h.1 h.2, pr_conj (μ := μ) (ι := ι) h.1 f'.1,
    pr_conj (μ := μ) (ι := ι) h'.1 f'.1, pr_left_eq_of_sub_mem_N hI hh f'.1 f'.2]

def ip (x y : X hI) : ℂ := pr μ ι (rep hI x).1 (rep hI y).1

theorem ip_mk (f h : 𝓕) : ip hI (Submodule.Quotient.mk f) (Submodule.Quotient.mk h) = pr μ ι f.1 h.1 := by
  unfold ip
  apply pr_eq_of_sub hI
  · exact (Submodule.Quotient.eq _).mp (mk_rep hI _)
  · exact (Submodule.Quotient.eq _).mp (mk_rep hI _)

theorem ip_conj (x y : X hI) : ip hI y x = star (ip hI x y) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [ip_mk, ip_mk, pr_conj]

theorem ip_add_left (x x' y : X hI) : ip hI (x + x') y = ip hI x y + ip hI x' y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨f', rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x'
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [← Submodule.Quotient.mk_add, ip_mk, ip_mk, ip_mk, Submodule.coe_add,
    pr_add_left hI f.2 f'.2 h.2]

theorem ip_smul_left (c : ℂ) (x y : X hI) : ip hI (c • x) y = c * ip hI x y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [← Submodule.Quotient.mk_smul, ip_mk, ip_mk, Submodule.coe_smul, pr_smul_left]

theorem ip_add_right (x y y' : X hI) : ip hI x (y + y') = ip hI x y + ip hI x y' := by
  rw [ip_conj hI (y + y') x, ip_add_left, star_add, ← ip_conj hI y x,
    ← ip_conj hI y' x]

theorem ip_smul_right (c : ℂ) (x y : X hI) : ip hI x (c • y) = star c * ip hI x y := by
  rw [ip_conj hI (c • y) x, ip_smul_left, star_mul', ← ip_conj hI y x]

theorem ip_sub_left (x x' y : X hI) : ip hI (x - x') y = ip hI x y - ip hI x' y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨f', rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x'
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [← Submodule.Quotient.mk_sub, ip_mk, ip_mk, ip_mk, Submodule.coe_sub,
    pr_sub_left hI f.2 f'.2 h.2]

theorem ip_sub_right (x y y' : X hI) : ip hI x (y - y') = ip hI x y - ip hI x y' := by
  rw [ip_conj hI (y - y') x, ip_sub_left, star_sub, ← ip_conj hI y x,
    ← ip_conj hI y' x]

theorem eq_zero_of_ip (x : X hI) (hx : ∀ y, ip hI x y = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  rw [Submodule.Quotient.mk_eq_zero]
  show ∀ h ∈ 𝓕, pr μ ι f.1 h = 0
  intro h hh
  have := hx (Submodule.Quotient.mk ⟨h, hh⟩)
  rwa [ip_mk] at this

theorem eq_of_ip_right {S T : Module.End ℂ (X hI)} (h : ∀ x y, ip hI x (S y) = ip hI x (T y)) : S = T := by
  refine LinearMap.ext fun y => ?_
  rw [← sub_eq_zero]
  apply eq_zero_of_ip hI
  intro x
  rw [ip_conj hI x, ip_sub_right, h x y, sub_self, star_zero]

def Adj : Subalgebra ℂ (Module.End ℂ (X hI)) where
  carrier := {T | ∃ T' : Module.End ℂ (X hI), ∀ x y, ip hI (T x) y = ip hI x (T' y)}
  mul_mem' := by
    rintro S T ⟨S', hS⟩ ⟨T', hT⟩
    refine ⟨T' * S', fun x y => ?_⟩
    simp only [mul_apply_eq_comp]
    rw [hS, hT]
  add_mem' := by
    rintro S T ⟨S', hS⟩ ⟨T', hT⟩
    refine ⟨S' + T', fun x y => ?_⟩
    simp only [LinearMap.add_apply]
    rw [ip_add_left, ip_add_right, hS, hT]
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap ℂ (Module.End ℂ (X hI)) (star c), fun x y => ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [ip_smul_left, ip_smul_right, star_star]

abbrev A := ↥(Adj hI)

def adjOf (T : A hI) : Module.End ℂ (X hI) := T.2.choose

theorem adjOf_spec (T : A hI) (x y : X hI) : ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x (adjOf hI T y) := T.2.choose_spec x y

theorem adjOf_mem (T : A hI) : adjOf hI T ∈ Adj hI := by
  show ∃ T' : Module.End ℂ (X hI), ∀ x y, ip hI (adjOf hI T x) y = ip hI x (T' y)
  refine ⟨(T : Module.End ℂ (X hI)), fun x y => ?_⟩
  rw [ip_conj hI y (adjOf hI T x), ← adjOf_spec, ← ip_conj hI ((T : Module.End ℂ (X hI)) y) x]

theorem adjOf_unique (T : A hI) (S : Module.End ℂ (X hI))
    (h : ∀ x y, ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x (S y)) : adjOf hI T = S := by
  apply eq_of_ip_right hI
  intro x y
  rw [← adjOf_spec, h]

instance instStar : Star (A hI) := ⟨fun T => ⟨adjOf hI T, adjOf_mem hI T⟩⟩

theorem star_coe (T : A hI) : ((star T : A hI) : Module.End ℂ (X hI)) = adjOf hI T := rfl

theorem star_spec (T : A hI) (x y : X hI) :
    ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x (((star T : A hI) : Module.End ℂ (X hI)) y) := adjOf_spec hI T x y

theorem star_eq_of (T S : A hI)
    (h : ∀ x y, ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x ((S : Module.End ℂ (X hI)) y)) : star T = S := by
  apply Subtype.ext
  rw [star_coe]
  exact adjOf_unique hI T _ h

instance instStarRing : StarRing (A hI) where
  star_involutive T := by
    apply star_eq_of
    intro x y
    rw [ip_conj hI y, ← star_spec, ← ip_conj]
  star_mul S T := by
    apply star_eq_of
    intro x y
    show ip hI ((S : Module.End ℂ (X hI)) ((T : Module.End ℂ (X hI)) x)) y =
      ip hI x (((star T : A hI) : Module.End ℂ (X hI)) (((star S : A hI) : Module.End ℂ (X hI)) y))
    rw [star_spec, star_spec]
  star_add S T := by
    apply star_eq_of
    intro x y
    show ip hI ((S : Module.End ℂ (X hI)) x + (T : Module.End ℂ (X hI)) x) y =
      ip hI x (((star S : A hI) : Module.End ℂ (X hI)) y + ((star T : A hI) : Module.End ℂ (X hI)) y)
    rw [ip_add_left, ip_add_right, star_spec, star_spec]

instance instStarModule : StarModule ℂ (A hI) where
  star_smul c T := by
    apply star_eq_of
    intro x y
    show ip hI (c • (T : Module.End ℂ (X hI)) x) y = ip hI x (star c • ((star T : A hI) : Module.End ℂ (X hI)) y)
    rw [ip_smul_left, ip_smul_right, star_star, star_spec]


open scoped Classical in
def mk' (f : β → ℂ) : X hI := by
  classical
  exact if hf : f ∈ 𝓕 then Submodule.Quotient.mk ⟨f, hf⟩ else 0

theorem mk'_of {f : β → ℂ} (hf : f ∈ 𝓕) : mk' hI f = Submodule.Quotient.mk ⟨f, hf⟩ := by
  rw [mk', dite_eq_left hf]

theorem mk'_surj (x : X hI) : ∃ f ∈ 𝓕, mk' hI f = x := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  exact ⟨f.1, f.2, mk'_of hI f.2⟩

theorem ip_mk' {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : ip hI (mk' hI f) (mk' hI h) = pr μ ι f h := by
  rw [mk'_of hI hf, mk'_of hI hh, ip_mk]

theorem mk'_add {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : mk' hI (f + h) = mk' hI f + mk' hI h := by
  rw [mk'_of hI (𝓕.add_mem hf hh), mk'_of hI hf, mk'_of hI hh, ← Submodule.Quotient.mk_add]
  rfl

theorem mk'_smul (c : ℂ) {f : β → ℂ} (hf : f ∈ 𝓕) : mk' hI (c • f) = c • mk' hI f := by
  rw [mk'_of hI (𝓕.smul_mem c hf), mk'_of hI hf, ← Submodule.Quotient.mk_smul]
  rfl

theorem mk'_neg {f : β → ℂ} (hf : f ∈ 𝓕) : mk' hI (-f) = -mk' hI f := by
  rw [mk'_of hI (𝓕.neg_mem hf), mk'_of hI hf, ← Submodule.Quotient.mk_neg]
  rfl

theorem mk'_sub {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : mk' hI (f - h) = mk' hI f - mk' hI h := by
  rw [mk'_of hI (𝓕.sub_mem hf hh), mk'_of hI hf, mk'_of hI hh, ← Submodule.Quotient.mk_sub]
  rfl

theorem mk'_zero : mk' hI (0 : β → ℂ) = 0 := by
  rw [mk'_of hI 𝓕.zero_mem]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (N hI).zero_mem

theorem A_ext {S T : A hI}
    (h : ∀ f ∈ 𝓕, (S : Module.End ℂ (X hI)) (mk' hI f) = (T : Module.End ℂ (X hI)) (mk' hI f)) : S = T := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨f, hf, rfl⟩ := mk'_surj hI x
  exact h f hf

section onG

variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)

include hG in
theorem pr_vanish {F : β → ℂ} (hF : ∀ g ∈ G, F g = 0) (h : β → ℂ) : pr μ ι F h = 0 := by
  unfold pr
  apply integral_eq_zero_of_ae
  filter_upwards [hG] with x hx
  simp [hF _ hx]

include hG in
theorem mk'_eq_of_eqOn {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) (he : ∀ g ∈ G, f g = h g) :
    mk' hI f = mk' hI h := by
  rw [← sub_eq_zero, ← mk'_sub hI hf hh, mk'_of hI (𝓕.sub_mem hf hh), Submodule.Quotient.mk_eq_zero]
  show ∀ k ∈ 𝓕, pr μ ι (f - h) k = 0
  intro k _
  exact pr_vanish G hG (fun g hg => by simp [he g hg]) k

structure AdjOp (Φ Φ' : (β → ℂ) → (β → ℂ)) : Prop where
  mem : ∀ f ∈ 𝓕, Φ f ∈ 𝓕
  mem' : ∀ f ∈ 𝓕, Φ' f ∈ 𝓕
  lin : ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, ∀ c : ℂ, ∀ g ∈ G, Φ (fun x => f x + c * h x) g = Φ f g + c * Φ h g
  lin' : ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, ∀ c : ℂ, ∀ g ∈ G, Φ' (fun x => f x + c * h x) g = Φ' f g + c * Φ' h g
  adj : ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, pr μ ι (Φ f) h = pr μ ι f (Φ' h)

variable {G}

theorem AdjOp.symm {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') :
    AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ' Φ := by
  refine ⟨hΦ.mem', hΦ.mem, hΦ.lin', hΦ.lin, ?_⟩
  intro f hf h hh
  rw [pr_conj, ← hΦ.adj h hh f hf, ← pr_conj]

private theorem adjOp_map_add_smul {Φ Φ' : (β → ℂ) → (β → ℂ)}
    (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) (c : ℂ) :
    ∀ g ∈ G, Φ (f + c • h) g = Φ f g + c * Φ h g :=
  fun g hg => hΦ.lin f hf h hh c g hg

theorem AdjOp.zero {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') :
    ∀ g ∈ G, Φ 0 g = 0 := by
  intro g hg
  have := (_root_.PI.QnHermHaar.Gen.adjOp_map_add_smul hΦ) (𝓕.zero_mem) (𝓕.zero_mem) 1 g hg
  rw [smul_zero, add_zero] at this
  linear_combination -this

theorem AdjOp.add {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : ∀ g ∈ G, Φ (f + h) g = Φ f g + Φ h g := by
  intro g hg
  have := (_root_.PI.QnHermHaar.Gen.adjOp_map_add_smul hΦ) hf hh 1 g hg
  rwa [one_smul, one_mul] at this

theorem AdjOp.smul {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    (c : ℂ) {h : β → ℂ} (hh : h ∈ 𝓕) : ∀ g ∈ G, Φ (c • h) g = c * Φ h g := by
  intro g hg
  have := (_root_.PI.QnHermHaar.Gen.adjOp_map_add_smul hΦ) (𝓕.zero_mem) hh c g hg
  rwa [zero_add, hΦ.zero g hg, zero_add] at this

variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)

def opF {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') : 𝓕 →ₗ[ℂ] X hI where
  toFun f := mk' hI (Φ f.1)
  map_add' f h := by
    show mk' hI (Φ (f.1 + h.1)) = mk' hI (Φ f.1) + mk' hI (Φ h.1)
    rw [mk'_eq_of_eqOn hI G hG (hΦ.mem _ (𝓕.add_mem f.2 h.2)) (𝓕.add_mem (hΦ.mem _ f.2) (hΦ.mem _ h.2))
      (fun g hg => by rw [hΦ.add f.2 h.2 g hg]; rfl)]
    exact mk'_add hI (hΦ.mem _ f.2) (hΦ.mem _ h.2)
  map_smul' c f := by
    show mk' hI (Φ (c • f.1)) = c • mk' hI (Φ f.1)
    rw [mk'_eq_of_eqOn hI G hG (hΦ.mem _ (𝓕.smul_mem c f.2)) (𝓕.smul_mem c (hΦ.mem _ f.2))
      (fun g hg => by rw [hΦ.smul c f.2 g hg]; rfl)]
    exact mk'_smul hI c (hΦ.mem _ f.2)

def opX {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') : Module.End ℂ (X hI) :=
  (N hI).liftQ (opF hI hG hΦ) (by
    intro f hf
    rw [LinearMap.mem_ker]
    show mk' hI (Φ f.1) = 0
    rw [mk'_of hI (hΦ.mem _ f.2), Submodule.Quotient.mk_eq_zero]
    intro h hh
    rw [hΦ.adj f.1 f.2 h hh]
    exact hf _ (hΦ.mem' h hh))

theorem opX_mk' {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    {f : β → ℂ} (hf : f ∈ 𝓕) : opX hI hG hΦ (mk' hI f) = mk' hI (Φ f) := by
  rw [mk'_of hI hf]
  rfl

def toA {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') : A hI :=
  ⟨opX hI hG hΦ, opX hI hG hΦ.symm, fun x y => by
    obtain ⟨f, hf, rfl⟩ := mk'_surj hI x
    obtain ⟨h, hh, rfl⟩ := mk'_surj hI y
    rw [opX_mk' hI hG hΦ hf, opX_mk' hI hG hΦ.symm hh, ip_mk' hI (hΦ.mem _ hf) hh,
      ip_mk' hI hf (hΦ.mem' _ hh)]
    exact hΦ.adj f hf h hh⟩

theorem toA_mk' {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    {f : β → ℂ} (hf : f ∈ 𝓕) : ((toA hI hG hΦ : A hI) : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f) := opX_mk' hI hG hΦ hf

theorem star_toA {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') :
    star (toA hI hG hΦ) = toA hI hG hΦ.symm := by
  apply star_eq_of
  intro x y
  obtain ⟨f, hf, rfl⟩ := mk'_surj hI x
  obtain ⟨h, hh, rfl⟩ := mk'_surj hI y
  rw [toA_mk' hI hG hΦ hf, toA_mk' hI hG hΦ.symm hh,
    ip_mk' hI (hΦ.mem _ hf) hh, ip_mk' hI hf (hΦ.mem' _ hh)]
  exact hΦ.adj f hf h hh

def RepOn (T : A hI) (Φ : (β → ℂ) → β → ℂ) : Prop :=
  ∀ f ∈ 𝓕, Φ f ∈ 𝓕 ∧ (T : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f)

theorem repOn_toA {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') :
    RepOn hI (toA hI hG hΦ) Φ := fun f hf => ⟨hΦ.mem f hf, toA_mk' hI hG hΦ hf⟩

theorem repOn_mul {S T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) (hT : RepOn hI T Ψ) :
    RepOn hI (S * T) (fun f => Φ (Ψ f)) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hT f hf
  obtain ⟨h3, h4⟩ := hS _ h1
  refine ⟨h3, ?_⟩
  show (S : Module.End ℂ (X hI)) ((T : Module.End ℂ (X hI)) (mk' hI f)) = mk' hI (Φ (Ψ f))
  rw [h2, h4]

theorem repOn_add {S T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) (hT : RepOn hI T Ψ) :
    RepOn hI (S + T) (fun f => Φ f + Ψ f) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hS f hf
  obtain ⟨h3, h4⟩ := hT f hf
  refine ⟨𝓕.add_mem h1 h3, ?_⟩
  show (S : Module.End ℂ (X hI)) (mk' hI f) + (T : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f + Ψ f)
  rw [h2, h4, mk'_add hI h1 h3]

theorem repOn_sub {S T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) (hT : RepOn hI T Ψ) :
    RepOn hI (S - T) (fun f => Φ f - Ψ f) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hS f hf
  obtain ⟨h3, h4⟩ := hT f hf
  refine ⟨𝓕.sub_mem h1 h3, ?_⟩
  show (S : Module.End ℂ (X hI)) (mk' hI f) - (T : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f - Ψ f)
  rw [h2, h4, mk'_sub hI h1 h3]

theorem repOn_neg {S : A hI} {Φ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) :
    RepOn hI (-S) (fun f => -Φ f) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hS f hf
  refine ⟨𝓕.neg_mem h1, ?_⟩
  show -(S : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (-Φ f)
  rw [h2, mk'_neg hI h1]

theorem repOn_smul (c : ℂ) {S : A hI} {Φ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) :
    RepOn hI (c • S) (fun f => c • Φ f) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hS f hf
  refine ⟨𝓕.smul_mem c h1, ?_⟩
  show c • (S : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (c • Φ f)
  rw [h2, mk'_smul hI c h1]

theorem repOn_one : RepOn hI (1 : A hI) (fun f => f) := fun _ hf => ⟨hf, rfl⟩

theorem repOn_zero : RepOn hI (0 : A hI) (fun _ => 0) := by
  intro _ _
  refine ⟨𝓕.zero_mem, ?_⟩
  show (0 : X hI) = mk' hI 0
  rw [mk'_zero]

theorem repOn_algebraMap (c : ℂ) : RepOn hI (algebraMap ℂ (A hI) c) (fun f => c • f) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact repOn_smul hI c (repOn_one hI)

theorem repOn_intCast (n : ℤ) : RepOn hI ((n : A hI)) (fun f => (n : ℂ) • f) := by
  simpa only [map_intCast] using repOn_algebraMap hI (n : ℂ)

theorem repOn_sum {γ : Type*} (s : Finset γ) {T : γ → A hI} {Φ : γ → (β → ℂ) → β → ℂ}
    (h : ∀ c ∈ s, RepOn hI (T c) (Φ c)) : RepOn hI (∑ c ∈ s, T c) (fun f => ∑ c ∈ s, Φ c f) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact repOn_zero hI
  · intro a s ha ih h
    simp only [Finset.sum_insert ha]
    exact repOn_add hI (h a (Finset.mem_insert_self a s))
      (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

theorem repOn_ite (p : Prop) [Decidable p] {S T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ)
    (hT : RepOn hI T Ψ) : RepOn hI (if p then S else T) (if p then Φ else Ψ) := by
  split_ifs
  · exact hS
  · exact hT

theorem repOn_list (t : ℕ) (F : Fin t → A hI) (Φ : Fin t → (β → ℂ) → β → ℂ)
    (h : ∀ k, RepOn hI (F k) (Φ k)) :
    RepOn hI (List.ofFn F).prod (fun f => (List.ofFn Φ).foldr (fun T h => T h) f) := by
  induction t with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, List.foldr_nil]
    exact repOn_one hI
  | succ t ih =>
    simp only [List.ofFn_succ, List.prod_cons, List.foldr_cons]
    exact repOn_mul hI (h 0) (ih (fun i => F i.succ) (fun i => Φ i.succ) (fun i => h i.succ))

theorem pr_of_repOn {T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hT : RepOn hI T Φ) (hS : RepOn hI (star T) Ψ)
    {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : pr μ ι (Φ f) h = pr μ ι f (Ψ h) := by
  rw [← ip_mk' hI (hT f hf).1 hh, ← (hT f hf).2, star_spec, (hS h hh).2,
    ip_mk' hI hf (hS h hh).1]

end onG

end PI.QnHermHaar.Gen
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section test

variable {k r : ℕ} {i : Fin (r + 1)}

theorem smoothLev_zero : SmoothLev k r i Set.univ (0 : Mx k r → ℂ) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => (0 : ℂ), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothLev_add {f h : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) (hh : SmoothLev k r i Set.univ h) :
    SmoothLev k r i Set.univ (f + h) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hhG⟩ := hh g₀ hg₀
  refine ⟨U ∩ V, fun x => F x + G x, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
  show f g + h g = F g + G g
  rw [hfF g hg.1 hgl, hhG g hg.2 hgl]

theorem smoothLev_smul (c : ℂ) {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) :
    SmoothLev k r i Set.univ (c • f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => c * F x, hU, hgU, contDiffOn_const.mul hF, fun g hg hgl => ?_⟩
  show c • f g = c * F g
  rw [hfF g hg hgl, smul_eq_mul]

theorem cptOn_zero : CptOn k r i (0 : Mx k r → ℂ) :=
  ⟨∅, isCompact_empty, fun _ _ _ => rfl⟩

theorem cptOn_add {f h : Mx k r → ℂ} (hf : CptOn k r i f) (hh : CptOn k r i h) : CptOn k r i (f + h) := by
  obtain ⟨K, hK, hfK⟩ := hf
  obtain ⟨L, hL, hhL⟩ := hh
  refine ⟨K ∪ L, hK.union hL, fun g hg hn => ?_⟩
  have h1 : g ∉ K := fun hk => hn (Or.inl hk)
  have h2 : g ∉ L := fun hl => hn (Or.inr hl)
  show f g + h g = 0
  rw [hfK g hg h1, hhL g hg h2, add_zero]

theorem cptOn_smul (c : ℂ) {f : Mx k r → ℂ} (hf : CptOn k r i f) : CptOn k r i (c • f) := by
  obtain ⟨K, hK, hfK⟩ := hf
  refine ⟨K, hK, fun g hg hn => ?_⟩
  show c • f g = 0
  rw [hfK g hg hn, smul_zero]

def testSub (k r : ℕ) (i : Fin (r + 1)) : Submodule ℂ (Mx k r → ℂ) where
  carrier := {f | TestF k r i f}
  zero_mem' := ⟨smoothLev_zero, cptOn_zero⟩
  add_mem' hf hh := ⟨smoothLev_add hf.1 hh.1, cptOn_add hf.2 hh.2⟩
  smul_mem' c _ hf := ⟨smoothLev_smul c hf.1, cptOn_smul c hf.2⟩

theorem mem_testSub {f : Mx k r → ℂ} : f ∈ testSub k r i ↔ TestF k r i f :=
  Iff.rfl

theorem posL_inj {a b : Fin (mdim k r i)} (h : posL k r i a = posL k r i b) : a = b := by
  have h' : a.val + i.val = b.val + i.val := congrArg Fin.val h
  exact Fin.ext (by omega)

end test

structure Hyp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (μ : Measure (Mt k r)) : Prop where
  hμ : Formalism.FourierDecayAlt.B.IsHaarOn (Glev k r i) μ
  hz : inWb k r z
  hz' : inWb k r z'
  ET : EabTest
  EA : EabAdj
  MT : MulTest
  TI : TestInt
  Yb : YbRel
  Xb : XbRel
  HF : HmFacts
  EP : EabPres
  Gl : EabGlLev
  YL : YLeibniz

section main

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

abbrev ιo (k r : ℕ) : Mt k r → Mx k r := fun x => Matrix.of x

theorem hI (H : Hyp k r z z' i μ) : IntOn μ (ιo k r) (testSub k r i) :=
  fun f hf h hh => H.TI k r i μ H.hμ f h hf hh

theorem hG (H : Hyp k r z z' i μ) : ∀ᵐ x ∂μ, ιo k r x ∈ Glev k r i := by
  first
    | exact ae_iff.mpr H.hμ.conc
    | (rw [ae_iff]; exact H.hμ.conc)

def EOp (k r : ℕ) (i : Fin (r + 1)) (a b : Fin (mdim k r i)) : (Mx k r → ℂ) → Mx k r → ℂ :=
  EH k r (posL k r i a) (posL k r i b)

def EOp' (k r : ℕ) (i : Fin (r + 1)) (a b : Fin (mdim k r i)) : (Mx k r → ℂ) → Mx k r → ℂ :=
  fun f g => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g

def MOp {k r : ℕ} (φ : Mx k r → ℂ) : (Mx k r → ℂ) → Mx k r → ℂ := fun f g => φ g * f g

def MOp' {k r : ℕ} (φ : Mx k r → ℂ) : (Mx k r → ℂ) → Mx k r → ℂ := fun f g => star (φ g) * f g

theorem EOp'_eq (a b : Fin (mdim k r i)) (f : Mx k r → ℂ) :
    EOp' k r i a b f = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EOp k r i c d f := by
  funext g
  simp only [EOp', EOp, Finset.sum_apply, Pi.smul_apply]

theorem adjOp_E (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    AdjOp (μ := μ) (ι := ιo k r) (𝓕 := testSub k r i) (Glev k r i) (EOp k r i a b) (EOp' k r i a b) := by
  refine ⟨fun f hf => H.ET k r i a b f hf, ?_, ?_, ?_, fun f hf h hh => H.EA k r i μ H.hμ a b f h hf hh⟩
  · intro f hf
    rw [EOp'_eq]
    exact Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ =>
      Submodule.smul_mem _ _ (H.ET k r i c d f hf)
  · intro f hf h hh c g hg
    have := (H.EP ℂ k r z i Set.univ a b f h c isOpen_univ hf.1 hh.1).2.2 g ⟨hg, trivial⟩
    simpa only [EOp, smul_eq_mul] using this
  · intro f hf h hh c g hg
    simp only [EOp']
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c' _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    have := (H.EP ℂ k r z i Set.univ c' d f h c isOpen_univ hf.1 hh.1).2.2 g ⟨hg, trivial⟩
    simp only [smul_eq_mul] at this ⊢
    rw [this]
    ring

theorem adjOp_M (φ : Mx k r → ℂ)
    (hφ : ∀ f, TestF k r i f → TestF k r i (fun g => φ g * f g) ∧ TestF k r i (fun g => star (φ g) * f g)) :
    AdjOp (μ := μ) (ι := ιo k r) (𝓕 := testSub k r i) (Glev k r i) (MOp φ) (MOp' φ) := by
  refine ⟨fun f hf => (hφ f hf).1, fun f hf => (hφ f hf).2, ?_, ?_, ?_⟩
  · intro f _ h _ c g _
    simp only [MOp]
    ring
  · intro f _ h _ c g _
    simp only [MOp']
    ring
  · intro f _ h _
    unfold pr MOp MOp'
    congr 1
    funext x
    rw [star_star_mul]
    ring

theorem yTest (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => yv k r z i g c * f g) ∧ TestF k r i (fun g => star (yv k r z i g c) * f g) :=
  ⟨(H.MT k r z i c f hf).1, (H.MT k r z i c f hf).2.1⟩

theorem ybTest (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => ybv k r z i g c * f g) ∧ TestF k r i (fun g => star (ybv k r z i g c) * f g) :=
  ⟨(H.MT k r z i c f hf).2.2.1, (H.MT k r z i c f hf).2.2.2⟩

def EA (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : A (hI H) := toA (hI H) (hG H) (adjOp_E H a b)

def YA (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) : A (hI H) :=
  toA (hI H) (hG H) (adjOp_M (fun g => yv k r z i g c) (yTest H c))

def YbA (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) : A (hI H) :=
  toA (hI H) (hG H) (adjOp_M (fun g => ybv k r z i g c) (ybTest H c))

theorem repE (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : RepOn (hI H) (EA H a b) (EOp k r i a b) :=
  repOn_toA (hI H) (hG H) (adjOp_E H a b)

theorem repY (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) :
    RepOn (hI H) (YA H c) (MOp (fun g => yv k r z i g c)) :=
  repOn_toA (hI H) (hG H) (adjOp_M _ (yTest H c))

theorem repYb (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) :
    RepOn (hI H) (YbA H c) (MOp (fun g => ybv k r z i g c)) :=
  repOn_toA (hI H) (hG H) (adjOp_M _ (ybTest H c))

end main

end PI.QnHermHaar
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem repOn_of_eq {hI' : IntOn μ (ιo k r) (testSub k r i)} {T : A hI'} {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ}
    (h : RepOn hI' T Φ) (e : ∀ f, Φ f = Ψ f) : RepOn hI' T Ψ := by
  have hΦΨ : Φ = Ψ := funext e
  subst hΦΨ
  exact h

private theorem eq_of_repOn_of_agree_on_test (H : Hyp k r z z' i μ) {S T : A (hI H)}
    {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ} (hS : RepOn (hI H) S Φ) (hT : RepOn (hI H) T Ψ)
    (e : ∀ f, TestF k r i f → ∀ g ∈ Glev k r i, Φ f g = Ψ f g) : S = T :=
  A_ext (hI H) fun f hf => by
    rw [(hS f hf).2, (hT f hf).2]
    exact mk'_eq_of_eqOn (hI H) (Glev k r i) (hG H) (hS f hf).1 (hT f hf).1 (e f hf)

private theorem repOn_ite' (H : Hyp k r z z' i μ) (p : Prop) [Decidable p] {T : A (hI H)}
    {Φ : (Mx k r → ℂ) → Mx k r → ℂ} (hT : RepOn (hI H) T Φ) :
    RepOn (hI H) (if p then T else 0) (fun f g => if p then Φ f g else 0) := by
  by_cases hp : p
  · simp only [if_pos hp]
    exact hT
  · simp only [if_neg hp]
    have h0 := repOn_sub _ hT hT
    rw [sub_self] at h0
    exact repOn_of_eq h0 fun f => funext fun g => by simp

theorem glRel_A (H : Hyp k r z z' i μ) : GlRel (EA H) := by
  intro a b c d
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repE H c d)) (repOn_mul _ (repE H c d) (repE H a b)))
    (repOn_sub _ (repOn_ite' H (b = c) (repE H a d)) (repOn_ite' H (d = a) (repE H c b))) fun f hf g hg => ?_
  exact H.Gl ℂ k r i Set.univ a b c d f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩

theorem starE_A (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    star (EA H a b) = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d := by
  have hL : RepOn (hI H) (star (EA H a b)) (EOp' k r i a b) := by
    show RepOn (hI H) (star (toA (hI H) (hG H) (adjOp_E H a b))) _
    rw [star_toA]
    exact repOn_toA _ _ _
  have hR : RepOn (hI H) (∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d)
      (fun f => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EOp k r i c d f) :=
    repOn_sum _ _ fun c _ => repOn_sum _ _ fun d _ => repOn_smul _ _ (repE H c d)
  refine eq_of_repOn_of_agree_on_test H hL hR fun f _ g _ => ?_
  simp only [EOp'_eq]

theorem yComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YA H a * YA H b = YA H b * YA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repY H a) (repY H b)) (repOn_mul _ (repY H b) (repY H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem ybComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YbA H a * YbA H b = YbA H b * YbA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repYb H a) (repYb H b)) (repOn_mul _ (repYb H b) (repYb H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem yybComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YA H a * YbA H b = YbA H b * YA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repY H a) (repYb H b)) (repOn_mul _ (repYb H b) (repY H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem eyComm (H : Hyp k r z z' i μ) (a b c : Fin (mdim k r i)) :
    EA H a b * YA H c - YA H c * EA H a b = if a = c then -YA H b else 0 := by
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repY H c)) (repOn_mul _ (repY H c) (repE H a b)))
    (repOn_ite' H (a = c) (repOn_neg _ (repY H b))) fun f hf g hg => ?_
  have hy := (H.YL ℂ k r z i Set.univ a b c f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩).1
  show EH k r (posL k r i a) (posL k r i b) (fun x => yv k r z i x c • f x) g -
      yv k r z i g c * EH k r (posL k r i a) (posL k r i b) f g =
      if a = c then -(yv k r z i g b * f g) else 0
  rw [hy]
  split_ifs <;> simp only [smul_eq_mul] <;> ring

theorem eybComm (H : Hyp k r z z' i μ) (a b c : Fin (mdim k r i)) :
    EA H a b * YbA H c - YbA H c * EA H a b = if b = c then YbA H a else 0 := by
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repYb H c)) (repOn_mul _ (repYb H c) (repE H a b)))
    (repOn_ite' H (b = c) (repYb H a)) fun f hf g hg => ?_
  have hy := (H.YL ℂ k r z i Set.univ a b c f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩).2
  show EH k r (posL k r i a) (posL k r i b) (fun x => ybv k r z i x c • f x) g -
      ybv k r z i g c * EH k r (posL k r i a) (posL k r i b) f g =
      if b = c then ybv k r z i g a * f g else 0
  rw [hy]
  split_ifs <;> simp only [smul_eq_mul] <;> ring

theorem ybStar (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) :
    YbA H c = ∑ l, Hm k r i l c • star (YA H l) := by
  have hs : ∀ l, RepOn (hI H) (star (YA H l)) (MOp' (fun g => yv k r z i g l)) := fun l => by
    show RepOn (hI H) (star (toA (hI H) (hG H) (adjOp_M _ (yTest H l)))) _
    rw [star_toA]
    exact repOn_toA _ _ _
  refine eq_of_repOn_of_agree_on_test H (repYb H c) (repOn_sum _ _ fun l _ => repOn_smul _ _ (hs l)) fun f _ g hg => ?_
  simp only [MOp, MOp', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [H.Yb k r z i H.hz g hg c, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

end PI.QnHermHaar
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem repTm (H : Hyp k r z z' i μ) (w : ℂ) (a b : Fin (mdim k r i)) :
    RepOn (hI H) (Tm (EA H) w a b) (Top (EH k r) w (posL k r i a) (posL k r i b)) := by
  have h := repOn_add (hI H) (repOn_ite (hI H) (a = b) (repOn_algebraMap (hI H) w) (repOn_zero (hI H)))
    (repE H a b)
  unfold Tm
  refine repOn_of_eq h fun f => ?_
  funext g
  by_cases hab : a = b
  · subst hab; simp [Formalism.QuantumDeterminants.Top, EOp]
  · have : posL k r i a ≠ posL k r i b := fun h => hab (posL_inj h)
    simp [Formalism.QuantumDeterminants.Top, EOp, hab, this]

theorem repQminor (H : Hyp k r z z' i μ) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) :
    RepOn (hI H) (qminor (EA H) a b w) (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w) := by
  unfold qminor
  exact repOn_sum (hI H) Finset.univ fun σ _ => repOn_mul (hI H) (repOn_intCast (hI H) _)
    (repOn_list (hI H) t _ _ fun k' => repTm H _ _ _)

theorem represents_transfer_zero_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 0)
      (tL k r z z' i Y 0 0) :=
  repQminor H id id _

theorem represents_transfer_zero_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 1)
      (tL k r z z' i Y 0 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xv k r z' i b)
      (repOn_mul (hI H) (repYb H a) (repQminor H (skip1 a) (skip1 b) (uC k r i Y - 1))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem represents_transfer_one_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 0)
      (tL k r z z' i Y 1 0) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xbv k r z' i a)
      (repOn_mul (hI H) (repY H b) (repQminor H (skip1 a) (skip1 b) (uC k r i Y))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem tA_11 {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) : tA E Y Yb x xb u 1 1 = -∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0 := rfl

theorem represents_transfer_one_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 1)
      (tL k r z z' i Y 1 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a' _ =>
    repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b' _ =>
    repOn_ite (hI H) (a < a' ∧ b < b')
      (repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (a' : ℕ) + (b : ℕ) + (b' : ℕ)))
        (repOn_mul (hI H)
          (repOn_mul (hI H)
            (repOn_sub (hI H) (repOn_mul (hI H) (repYb H a) (repOn_algebraMap (hI H) (xbv k r z' i a')))
              (repOn_mul (hI H) (repYb H a') (repOn_algebraMap (hI H) (xbv k r z' i a))))
            (repOn_sub (hI H) (repOn_mul (hI H) (repY H b) (repOn_algebraMap (hI H) (xv k r z' i b')))
              (repOn_mul (hI H) (repY H b') (repOn_algebraMap (hI H) (xv k r z' i b)))))
          (repQminor H (skip2 a a') (skip2 b b') (uC k r i Y - 1))))
      (repOn_zero (hI H)))
  rw [tA_11]
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chat2L, Pi.neg_apply, Finset.sum_apply]
  rw [neg_inj]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro a' _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro b' _
  split_ifs
  · simp only [MOp, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · rfl

theorem rep_tL (H : Hyp k r z z' i μ) (Y : ℂ) (p q : Fin 2) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) p q)
      (tL k r z z' i Y p q) := by
  fin_cases p <;> fin_cases q
  · exact represents_transfer_zero_zero H Y
  · exact represents_transfer_zero_one H Y
  · exact represents_transfer_one_zero H Y
  · exact represents_transfer_one_one H Y

theorem uC_star (Y : ℂ) : star (uC k r i Y) = uC k r i (star Y) := by
  simp [uC]

theorem glue_holds_var : Glue := by
  intro hAlg hET hEA hMT hTI hYb hXb hHm hEP hGl hYL k r z z' i μ hμ hz hz' f₁ f₂ hs₁ hs₂ hc₁ hc₂ Y a b
  have H : Hyp k r z z' i μ := ⟨hμ, hz, hz', hET, hEA, hMT, hTI, hYb, hXb, hHm, hEP, hGl, hYL⟩
  have hstar := hAlg (A (hI H)) (mdim k r i) (EA H) (YA H) (YbA H) (Hm k r i) (xv k r z' i) (xbv k r z' i)
    (glRel_A H) (hHm k r i).1 (hHm k r i).2 (starE_A H) (yComm H) (ybComm H) (yybComm H) (eyComm H) (eybComm H)
    (ybStar H) (hXb k r z' i hz') (uC k r i Y) a b
  have hT := rep_tL H Y a b
  have hS : RepOn (hI H) (star (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) a b))
      (tL k r z z' i (star Y) b a) := by
    rw [hstar, uC_star]
    exact rep_tL H (star Y) b a
  exact pr_of_repOn (hI H) hT hS (mem_testSub.2 ⟨hs₁, hc₁⟩) (mem_testSub.2 ⟨hs₂, hc₂⟩)

end PI.QnHermHaar
