module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormRootSubOneLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRangeMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWach
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiGamPowNeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResEqOneIff
noncomputable section

namespace GlobalTheory.HWL.EtMod

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

section Abstract

variable {O E R : Type} [CommRing O] [CommRing E] [CommRing R] [Algebra O E] [Algebra O R]
  {M M' : Type} [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M]
  [AddCommGroup M'] [Module R M'] [Module O M'] [IsScalarTower O R M']

def jB (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) : (Fin r → E) →ₗ[O] M where
  toFun x := ∑ i, ι (x i) • e i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_assoc]

theorem jB_apply (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (x : Fin r → E) :
    jB ι e x = ∑ i, ι (x i) • e i := rfl

theorem repr_jB (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (x : Fin r → E) (i) :
    e.repr (jB ι e x) i = ι (x i) := by
  rw [jB_apply, e.repr_sum_self]

theorem jB_smul (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (a : E) (x : Fin r → E) :
    jB ι e (a • x) = ι a • jB ι e x := by
  simp [jB_apply, Finset.smul_sum, mul_smul]

theorem jB_inj (ι : E →ₐ[O] R) (hι : Function.Injective ι) {r : ℕ} (e : Module.Basis (Fin r) R M) :
    Function.Injective (jB ι e) := fun x y h => funext fun i => hι (by
  rw [← repr_jB ι e, h, repr_jB])

theorem jB_single (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (i) :
    jB ι e (Pi.single i 1) = e i := by
  apply e.repr.injective
  ext k
  rw [repr_jB, e.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : k = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem jB_span (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) :
    Submodule.span R (Set.range (jB ι e)) = ⊤ := by
  rw [eq_top_iff, ← e.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨_, jB_single ι e i⟩

theorem mem_range_jB (ι : E →ₐ[O] R) {r : ℕ} (e : Module.Basis (Fin r) R M) (y : M)
    (h : ∀ i, e.repr y i ∈ Set.range ι) : ∃ x, jB ι e x = y := by
  choose x hx using h
  exact ⟨x, by simp [jB_apply, hx]⟩

theorem exists_lift (ι : E →ₐ[O] R) (hι : Function.Injective ι) {r r' : ℕ}
    (e : Module.Basis (Fin r) R M) (e' : Module.Basis (Fin r') R M') (F : M →ₗ[O] M')
    (σ : E → E) (hF : ∀ a y, F (ι a • y) = ι (σ a) • F y)
    (h : ∀ j i, e'.repr (F (e j)) i ∈ Set.range ι) :
    ∃ f : (Fin r → E) →ₗ[O] (Fin r' → E), ∀ x, jB ι e' (f x) = F (jB ι e x) := by
  choose y hy using fun j => mem_range_jB ι e' _ (h j)
  have h1 : ∀ x, ∃ z, jB ι e' z = F (jB ι e x) := fun x =>
    ⟨∑ j, σ (x j) • y j, by simp [map_sum, jB_smul, hy, jB_apply ι e, hF]⟩
  choose f hf using h1
  exact ⟨⟨⟨f, fun a b => jB_inj ι hι e' (by simp [hf])⟩,
    fun c a => jB_inj ι hι e' (by simp [hf])⟩, hf⟩

theorem repr_semi {r : ℕ} (e : Module.Basis (Fin r) R M) (F : M →ₗ[O] M) (σ : R → R)
    (hF : ∀ a y, F (a • y) = σ a • F y) (y : M) (i) :
    e.repr (F y) i = ∑ k, e.repr (F (e k)) i * σ (e.repr y k) := by
  have : F y = ∑ k, σ (e.repr y k) • F (e k) := by
    conv_lhs => rw [← e.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hF]
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, mul_comm]

theorem isUnit_of_span {r : ℕ} (e : Module.Basis (Fin r) R M) (x : Fin r → M)
    (h : ∀ y, y ∈ Submodule.span R (Set.range x)) :
    IsUnit (Matrix.of fun i j => e.repr (x j) i).det := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun R).1 (h (e k))
  apply Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun j k => c k j)
  ext i k
  have := congrArg (fun y => e.repr y i) (hc k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
    smul_eq_mul, e.repr_self, Finsupp.single_apply] at this
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_comm (e.repr _ _), this, eq_comm]

end Abstract

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {RW : Type} [CommRing RW] [Algebra O RW]

theorem act_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (g : G) (r : RW) (y : TW RW T) :
    TWact f T g (r • y) = f r • TWact f T g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]

theorem phi_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (r : RW) (y : TW RW T) :
    TWmap f T (r • y) = f r • TWmap f T y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, TensorProduct.smul_tmul']
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]

theorem act_mul (f f' f'' : RW →ₐ[O] RW) (hf : ∀ x, f x = f' (f'' x)) (T : LocLat G Qp LL O) (g h : G)
    (y : TW RW T) : TWact f T (g * h) y = TWact f' T g (TWact f'' T h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : T.actT (g * h) t = T.actT g (T.actT h t) := Subtype.ext (by
      change T.ρ (g * h) t = T.ρ g (T.ρ h t)
      rw [map_mul]; rfl)
    simp [TWact, this, hf]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem phi_act (φ f : RW →ₐ[O] RW) (hf : ∀ x, φ (f x) = f (φ x)) (T : LocLat G Qp LL O) (g : G)
    (y : TW RW T) : TWmap φ T (TWact f T g y) = TWact f T g (TWmap φ T y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TWmap, hf]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

abbrev oneT (RW : Type) [CommRing RW] [Algebra O RW] {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) :
    TW RW T →ₗ[O] TW RW T' :=
  TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) ((f.f.restrictScalars O).restrict f.T_le)

theorem oneT_smul {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (r : RW) (y : TW RW T) :
    oneT RW f (r • y) = r • oneT RW f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]

theorem oneT_phi {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (φ : RW →ₐ[O] RW) (y : TW RW T) :
    oneT RW f (TWmap φ T y) = TWmap φ T' (oneT RW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem oneT_act {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (φ : RW →ₐ[O] RW) (g : G)
    (y : TW RW T) : oneT RW f (TWact φ T g y) = TWact φ T' g (oneT RW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : (f.f.restrictScalars O).restrict f.T_le (T.actT g t) =
        T'.actT g ((f.f.restrictScalars O).restrict f.T_le t) := Subtype.ext (f.equiv g t)
    simp [TWact, this]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem oneT_id (T : LocLat G Qp LL O) (y : TW RW T) : oneT RW (latId T) y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem oneT_comp {T T' T'' : LocLat G Qp LL O} (g : LatHom T'.L T''.L) (f : LatHom T.L T'.L)
    (y : TW RW T) : oneT RW (latComp g f) y = oneT RW g (oneT RW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem oneT_add {T T' : LocLat G Qp LL O} (f g : LatHom T.L T'.L)
    (y : TW RW T) : oneT RW (latAdd f g) y = oneT RW f y + oneT RW g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_add]
    rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; abel

theorem oneT_latSmul (T : LocLat G Qp LL O) (c : O)
    (y : TW RW T) : oneT RW (latSmul T c) y = c • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul]
    congr 1
    apply Subtype.ext
    change algebraMap O LL c • (t : T.V) = c • (t : T.V)
    rw [algebraMap_smul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, smul_add]

theorem span_phi (φ : RW →ₐ[O] RW) (T : LocLat G Qp LL O) {r : ℕ}
    (e : Module.Basis (Fin r) RW (TW RW T)) (y : TW RW T) :
    y ∈ Submodule.span RW (Set.range fun j => TWmap φ T (e j)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : a ⊗ₜ[O] t = a • TWmap φ T ((1 : RW) ⊗ₜ[O] t) := by
      simp [TWmap, TensorProduct.smul_tmul']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, ← e.sum_repr ((1 : RW) ⊗ₜ[O] t), map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [phi_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

variable {Γ : WGam PD LL O v n s} {R : WSer Γ} {RA : Type} [CommRing RA] [Algebra O RA]
  {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem exists_et (I : WIo R RA RW inclR φR gR πA)
    (hmul : ∀ g h x, gR (g * h) x = gR g (gR h x)) (hφ : ∀ g x, φR (gR g x) = gR g (φR x))
    (hinj : Function.Injective I.ioE) (hunit : ∀ x, IsUnit (I.ioE x) → IsUnit x)
    (hrat : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) R.EE) (A' : Matrix (Fin q) (Fin q) R.EE)
      (U : Matrix (Fin p) (Fin q) RW), IsUnit A → IsUnit A' →
      (∀ i j g, Γ.resΓ g = 1 → gR g (U i j) = U i j) →
      A.map I.ioE * U.map φR = U * A'.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE)
    (e : ∀ T : LocLat G Qp LL O, Module.Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T))
    (hfix : ∀ T g, Γ.resΓ g = 1 → ∀ i, TWact (gR g) T g (e T i) = e T i)
    (het : ∀ T i j, (e T).repr (TWmap φR T (e T j)) i ∈ Set.range I.ioE) : Nonempty (WEt I) := by
  classical
  choose A hA using het
  have hAu : ∀ T, IsUnit (Matrix.of (A T)) := fun T => by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply hunit
    have h := isUnit_of_span (e T) _ (span_phi φR T (e T))
    rw [AlgHom.map_det]
    convert h using 2
    ext i j
    exact hA T i j
  have key : ∀ (T : LocLat G Qp LL O) (q : ℕ) (x : Fin q → TW RW T) (Bm : Matrix (Fin q) (Fin q) R.EE),
      IsUnit Bm → (∀ g, Γ.resΓ g = 1 → ∀ j, TWact (gR g) T g (x j) = x j) →
      (∀ j, TWmap φR T (x j) = ∑ k, I.ioE (Bm k j) • x k) →
      ∀ j i, (e T).repr (x j) i ∈ Set.range I.ioE := by
    intro T q x Bm hB hx hφx j i
    refine hrat _ q (Matrix.of (A T)) Bm (Matrix.of fun i j => (e T).repr (x j) i) (hAu T) hB ?_ ?_ i j
    · intro i j g hg
      have h := repr_semi (e T) (TWact (gR g) T g) (gR g) (act_smul _ T g) (x j) i
      simp only [hx g hg, hfix T g hg, Module.Basis.repr_self, Finsupp.single_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      exact h.symm
    · ext i j
      have h := repr_semi (e T) (TWmap φR T) φR (phi_smul _ T) (x j) i
      rw [hφx] at h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
        smul_eq_mul] at h
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hA]
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hφe : ∀ T j, TWmap φR T (e T j) = ∑ k, I.ioE (A T k j) • e T k := fun T j => by
    simp only [hA, Module.Basis.sum_repr]
  have h1 := fun T => exists_lift I.ioE hinj (e T) (e T) (TWmap φR T) R.φE
    (fun a y => by rw [phi_smul, I.ioE_φ]) (fun j i => ⟨_, hA T i j⟩)
  choose φD hφD using h1
  have h2 := fun T g => exists_lift I.ioE hinj (e T) (e T) (TWact (gR g) T g) (R.γE (Γ.resΓ g))
    (fun a y => by rw [act_smul, I.ioE_γ])
    (key T _ _ ((R.γE (Γ.resΓ g)).mapMatrix (Matrix.of (A T))) ((hAu T).map _)
      (fun h hh j => by
        rw [← act_mul _ _ _ (hmul h g), show h * g = g * (g⁻¹ * h * g) by group,
          act_mul _ _ _ (hmul g _), hfix T _ (by simp [hh])])
      (fun j => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [phi_act _ _ (hφ g), hφe, map_sum]
        simp only [act_smul, ← I.ioE_γ]
        rfl))
  choose γG hγG using h2
  have h3 := fun (T T' : LocLat G Qp LL O) (f : LatHom T.L T'.L) =>
    exists_lift I.ioE hinj (e T) (e T') (oneT RW f) id
    (fun a y => oneT_smul f _ y)
    (key T' _ _ (Matrix.of (A T)) (hAu T)
      (fun h hh j => by rw [← oneT_act, hfix T h hh])
      (fun j => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← oneT_phi, hφe, map_sum]
        simp only [oneT_smul]
        rfl))
  choose mp hmp using h3
  have hker : ∀ T h, Γ.resΓ h = 1 → ∀ x, TWact (gR h) T h (jB I.ioE (e T) x) = jB I.ioE (e T) x := by
    intro T h hh x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [jB_apply, map_sum, act_smul, ← I.ioE_γ, hh, hfix T h hh, map_one, AlgHom.one_apply]
  choose sec hsec using Γ.resΓ_onto
  have hact : ∀ T g x, jB I.ioE (e T) (γG T (sec (Γ.resΓ g)) x) =
      TWact (gR g) T g (jB I.ioE (e T) x) := by
    intro T g x
    rw [hγG, show sec (Γ.resΓ g) = g * (g⁻¹ * sec (Γ.resΓ g)) by group, act_mul _ _ _ (hmul g _),
      hker T _ (by simp [hsec])]
  have hj := fun T => jB_inj I.ioE hinj (e T)
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI : Nontrivial R.EE := R.EE_inj.nontrivial
  exact ⟨{
    DD := fun T => Fin (Module.finrank O ↥T.L.T) → R.EE
    φD := φD
    φD_smul := fun T a x => hj T (by rw [hφD, jB_smul, jB_smul, phi_smul, hφD, I.ioE_φ])
    γD := fun T g => γG T (sec g)
    γD_smul := fun T g a x => hj T (by
      rw [hγG, jB_smul, jB_smul, act_smul, hγG, ← I.ioE_γ, hsec])
    γD_one := fun T x => hj T (by rw [hγG, hker T _ (hsec 1)])
    γD_mul := fun T g h x => hj T (by
      rw [hγG T (sec g), hγG T (sec h), ← act_mul _ _ _ (hmul _ _), ← hact, map_mul, hsec, hsec])
    φγ_comm := fun T g x => hj T (by rw [hφD, hγG, hγG, hφD, phi_act _ _ (hφ _)])
    DD_free := fun T => ⟨inferInstance, Module.finrank_fin_fun _⟩
    map := fun {T T'} f =>
      { toFun := mp T T' f
        map_add' := map_add _
        map_smul' := fun a x => hj T' (by
          rw [hmp, jB_smul, RingHom.id_apply, jB_smul, oneT_smul, hmp]) }
    map_φ := fun {T T'} f x => hj T' (by
      change jB _ _ (mp T T' f _) = jB _ _ (φD T' (mp T T' f x))
      rw [hmp, hφD, hφD, hmp, oneT_phi])
    map_γ := fun {T T'} f g x => hj T' (by
      change jB _ _ (mp T T' f _) = jB _ _ (γG T' _ (mp T T' f x))
      rw [hmp, hγG, hγG, hmp, oneT_act])
    map_id := fun T x => hj T ((hmp _ _ _ x).trans (oneT_id T _))
    map_comp := fun {T T' T''} g f x => hj T'' (by
      change jB _ _ (mp T T'' _ x) = jB _ _ (mp T' T'' g (mp T T' f x))
      rw [hmp, hmp, hmp, oneT_comp])
    map_latAdd := fun {T T'} f g x => hj T' (by
      change jB _ _ (mp T T' _ x) = jB _ _ (mp T T' f x + mp T T' g x)
      rw [map_add (f := _), hmp, hmp, hmp, oneT_add])
    map_latSmul := fun T c x => hj T (by
      change jB _ _ (mp T T _ x) = _
      rw [hmp, oneT_latSmul, map_smul])
    jD := fun T => jB I.ioE (e T)
    jD_smul := fun T => jB_smul _ _
    jD_φ := hφD
    jD_act := hact
    jD_inj := hj
    jD_span := fun T => jB_span _ _
    jD_map := fun {T T'} f x => hmp T T' f x }⟩

end Generic

section Concrete

theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g f' g' : W →ₐ[Z] W) (h : ∀ w, f (g w) = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w => simp [h]

theorem map_id_comp {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f f' g' : W →ₐ[Z] W) (h : ∀ w, f w = f' (g' w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f x =
    Algebra.TensorProduct.map (AlgHom.id O O) f' (Algebra.TensorProduct.map (AlgHom.id O O) g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w => simp [h]

variable {l : ℕ} [Fact l.Prime]

theorem gRW_mul {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g h : GQ l) (x : RW LL) :
    AI.gRW LL (g * h) x = AI.gRW LL g (AI.gRW LL h x) :=
  map_id_comp _ _ _ (fun w => by simp) x

theorem phi_gRW {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (x : RW LL) :
    φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ _ _ (fun w => ?_) x
  ext n
  change (WittVector.map (frobenius (Cb l) l)
      (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n =
    (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n
  simp [WittVector.map_coeff, frobenius_def]

theorem res_eq_one_iff {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} (Γ : GamS P K s LL)
    (g : ↥(GK K)) : Γ.resΓ g = 1 ↔ P.χQ (g : GQ l) = 1 := by
  have h : algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ (Γ.resΓ g) : ↥(OL LL)) =
      algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    rw [Γ.χΓ_res g, P.PD_χ]
  constructor
  · intro hg
    rw [hg, map_one, Units.val_one, map_one] at h
    apply Units.ext
    apply (algebraMap ℚ_[l] ↥LL.1).injective
    rw [← h, Units.val_one, map_one]
  · intro hg
    rw [hg, Units.val_one, map_one] at h
    apply Γ.χΓ_inj
    rw [map_one]
    apply Units.ext
    exact Subtype.ext h


set_option maxHeartbeats 1000000 in
theorem nonempty_wEt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → (∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), EtBasis I T e) → Nonempty (WEt I) := by
  intro l _ P AI K s LL hg Γ R I hI h
  choose e he using h
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hg Γ R I hI
  refine exists_et I (fun g h x => gRW_mul AI LL _ _ x) (fun g x => phi_gRW AI LL _ x) h1 h2
    (fun p q A A' U hA hA' hU hφ => GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach l P AI K s LL hg Γ R I hI p q A A' 0 U hA hA'
      (fun i j g hgK hχ => hU i j ⟨g, hgK⟩ ((res_eq_one_iff Γ _).2 hχ)) ?_) e
    (fun T g hg => (he T).1 g ((res_eq_one_iff Γ g).1 hg)) (fun T => (he T).2)
  rw [hφ, Matrix.map_zero _ (map_zero _), add_zero]

end Concrete

end GlobalTheory.HWL.EtMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctor
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
namespace GlobalTheory.HWL.Assembly

theorem exists_wach (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (hF : FaithH AI) (hW : WachEx AI) :
    ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  obtain ⟨ht, hπ, -⟩ := GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI hT
  refine exists_of_layers P AI (fun K s LL g => ?_) ht hπ
  obtain ⟨Γ⟩ := GlobalTheory.HWL.GroupLayer.nonempty_gamS l P K s LL g
  obtain ⟨R⟩ := GlobalTheory.HWL.Ser.nonempty_wSer l P K s LL g Γ
  obtain ⟨I, hI⟩ := GlobalTheory.HWL.IoLayer.main l P AI K s LL g Γ R
  obtain ⟨E⟩ := GlobalTheory.HWL.EtMod.nonempty_wEt l P AI K s LL g Γ R I hI (GlobalTheory.EtaleBasis.exists_etBasis l P AI hF K s LL g Γ R I hI)
  obtain ⟨Mo⟩ := hW K s LL g Γ R I hI E
  obtain ⟨Cl⟩ := GlobalTheory.HerrClassMaps.exists_classMaps l P AI K s LL g Γ R I hI E
  obtain ⟨Cm⟩ := GlobalTheory.HWL.Cmp.nonempty_cmpS l P AI hT K s LL g Γ R I hI E Mo
  exact ⟨⟨Γ, R, I, hI, E, Mo, Cl, Cm⟩⟩

end GlobalTheory.HWL.Assembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctorStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_wach_functor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → FaithH AI → WachEx AI → ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  first | exact @GlobalTheory.HWL.Assembly.exists_wach | exact GlobalTheory.HWL.Assembly.exists_wach | (intros; apply GlobalTheory.HWL.Assembly.exists_wach <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithful
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithful
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Cyc GlobalTheory.Cyc.TraceTilt

namespace GlobalTheory.TiltFaithful

def Reps {G : Type*} [Group G] (H U : Subgroup G) (S : Finset G) : Prop :=
  (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ U

theorem exists_reps' {G : Type*} [Group G] (H U W : Subgroup G) [W.FiniteIndex] (hW : H ⊓ W ≤ U) :
    ∃ S : Finset G, Reps H U S := by
  classical
  haveI : (U.subgroupOf H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := W.subgroupOf H) fun x hx => hW ⟨x.2, hx⟩
  letI : Fintype (H ⧸ U.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ U.subgroupOf H => (q.out : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    have key : ∀ q : H ⧸ U.subgroupOf H,
        (q.out : G)⁻¹ * h ∈ U ↔ q = ((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H) := by
      intro q
      conv_rhs => rw [← q.out_eq']
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
    refine ⟨(((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H).out : G),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro s ⟨hs, hs'⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    rw [(key q).1 hs']

theorem reps_mul {G : Type*} [Group G] {H V U : Subgroup G} (hVH : V ≤ H) (hUV : U ≤ V)
    {S T : Finset G} (hS : Reps H V S) (hT : Reps V U T) :
    ∃ R : Finset G, Reps H U R ∧ ∀ {M : Type} [AddCommMonoid M] (f : G → M),
      ∑ r ∈ R, f r = ∑ s ∈ S, ∑ t ∈ T, f (s * t) := by
  classical
  have huniq : ∀ h ∈ H, ∃! p : G × G, p ∈ S ×ˢ T ∧ (p.1 * p.2)⁻¹ * h ∈ U := by
    intro h hh
    obtain ⟨s, ⟨hs, hsh⟩, hsu⟩ := hS.2 h hh
    obtain ⟨t, ⟨ht, hth⟩, htu⟩ := hT.2 _ hsh
    refine ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, ?_⟩, ?_⟩
    · rw [mul_inv_rev, mul_assoc]
      exact hth
    · rintro ⟨s', t'⟩ ⟨hm, hp⟩
      obtain ⟨hs', ht'⟩ := Finset.mem_product.1 hm
      rw [mul_inv_rev, mul_assoc] at hp
      have h1 : s' = s := hsu s' ⟨hs', by
        have := V.mul_mem (hT.1 t' ht') (hUV hp)
        rwa [mul_inv_cancel_left] at this⟩
      subst h1
      rw [htu t' ⟨ht', hp⟩]
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2) ↑(S ×ˢ T) := by
    intro p hp q hq he
    have hp' := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    refine (huniq (p.1 * p.2) (H.mul_mem (hS.1 _ hp'.1) (hVH (hT.1 _ hp'.2)))).unique
      ⟨hp, by simp⟩ ⟨hq, ?_⟩
    have he' : p.1 * p.2 = q.1 * q.2 := he
    rw [he']; simp
  refine ⟨(S ×ˢ T).image fun p => p.1 * p.2, ⟨?_, ?_⟩, fun f => ?_⟩
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    have hp' := Finset.mem_product.1 hp
    exact H.mul_mem (hS.1 _ hp'.1) (hVH (hT.1 _ hp'.2))
  · intro h hh
    obtain ⟨p, ⟨hp, hph⟩, hpu⟩ := huniq h hh
    refine ⟨p.1 * p.2, ⟨Finset.mem_image_of_mem _ hp, hph⟩, ?_⟩
    rintro s ⟨hs, hsh⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    rw [hpu q ⟨hq, hsh⟩]
  · rw [Finset.sum_image hinj, Finset.sum_product]

variable {l : ℕ} [Fact l.Prime]

theorem exists_tilt_near {P : LocPrime l} (AI : LocAinf l P) (N : Subgroup (GQ l))
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) (B : ℕ → OC l)
    (hB : ∀ j, ∀ n ∈ N, AI.actC n (B j) = B j)
    (hs : ∀ j, ‖(B (j + 1) : PadicComplex l) ^ l - B j‖ ≤ r) :
    ∃ (x : OCb l) (y : OC l), (∀ n ∈ N, AI.actT n x = x) ∧
      PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y ∧
      ‖(B 0 : PadicComplex l) - y‖ ≤ r := by
  have hp : l.Prime := Fact.out
  have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := (l : ℝ)⁻¹) (by positivity) hr
  have hk' : r ^ l ^ k ≤ (l : ℝ)⁻¹ :=
    (pow_le_pow_of_le_one hr0 hr.le (Nat.lt_pow_self hp.one_lt).le).trans hk.le
  have hB1 : ∀ j, ‖(B j : PadicComplex l)‖ ≤ 1 := fun j => (mem_OC _).1 (B j).2
  have hcomp : ∀ n, (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + 1 + k) ^ l ^ k) :
      ModP (OC l) l) ^ l = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + k) ^ l ^ k) := by
    intro n
    have h0 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})
        ((B (n + k + 1) ^ l - B (n + k)) ^ l ^ k) = 0 := by
      rw [mk_eq_zero_iff]
      push_cast
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hs _) _).trans hk'
    have h2 := sub_pow_char_pow (R := ModP (OC l) l) (p := l) (n := k)
      (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + k + 1) ^ l))
      (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + k)))
    rw [map_pow, map_sub] at h0
    have h3 := sub_eq_zero.mp (h2.symm.trans h0)
    rw [show n + 1 + k = n + k + 1 by omega, ← map_pow, ← pow_mul, mul_comm, pow_mul, map_pow,
      map_pow _ (B (n + k))]
    exact h3
  let x : OCb l := ⟨fun n => Ideal.Quotient.mk _ (B (n + k) ^ l ^ k), hcomp⟩
  have hx : ∀ n, PreTilt.coeff n x = Ideal.Quotient.mk _ (B (n + k) ^ l ^ k) := fun n => rfl
  have h4 : ∀ j, ‖(B 0 : PadicComplex l) - (B j : PadicComplex l) ^ l ^ j‖ ≤ r := by
    intro j
    induction j with
    | zero => simpa using hr0
    | succ j ih =>
      rw [← sub_add_sub_cancel _ ((B j : PadicComplex l) ^ l ^ j)]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
      rw [pow_succ', pow_mul, norm_sub_rev]
      refine (norm_pow_sub_pow_le ?_ (hB1 j) _).trans (hs j)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hB1 _)
  refine ⟨x, _, fun g hg => Perfection.ext fun n => ?_, hx 0, ?_⟩
  · change PreTilt.coeff n (AI.actT g x) = PreTilt.coeff n x
    obtain ⟨y', hy', hy⟩ := AI.actT_coeff g x n _ (hx n)
    rw [hy, hx]
    congr 1
    apply Subtype.ext
    rw [hy']
    push_cast
    rw [map_pow, hB _ g hg]
  · rw [zero_add]
    exact h4 k

theorem near_of_tilt {P : LocPrime l} (AI : LocAinf l P) (T : Finset (GQ l)) (d : GQ l) (x : OCb l)
    (y : OC l) (hy : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y)
    (b : Om l) (r : ℝ) (hr : (l : ℝ)⁻¹ ≤ r) (hb : ‖(b : PadicComplex l) - y‖ ≤ r)
    (hd : AI.actT d (∑ t ∈ T, AI.actT t x) = ∑ t ∈ T, AI.actT t x) :
    ‖d (∑ t ∈ T, t b) - ∑ t ∈ T, t b‖ ≤ r := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hb
  choose z hz hz' using fun s => AI.actT_coeff s x 0 y hy
  have hd' : ∑ t ∈ T, AI.actT (d * t) x = ∑ t ∈ T, AI.actT t x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hd, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul AI.actT, RingAut.mul_apply]
  have h1 := congrArg (PreTilt.coeff 0) hd'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_congr rfl fun s _ => hz' (d * s),
    Finset.sum_congr rfl fun s _ => hz' s] at h1
  have h2 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})
      (∑ s ∈ T, (z (d * s) - z s)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_sub_distrib, map_sub, map_sum, map_sum]
    exact sub_eq_zero.2 h1
  rw [mk_eq_zero_iff] at h2
  have h3 : ((∑ s ∈ T, (z (d * s) - z s) : OC l) : PadicComplex l) =
      ∑ s ∈ T, (AI.actC (d * s) y - AI.actC s y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ s ∈ T, (z (d * s) - z s) : OC l) : PadicComplex l) =
      ∑ s ∈ T, ((z (d * s) - z s : OC l) : PadicComplex l) from
      map_sum (PadicComplexInt l).subtype _ _]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← hz, ← hz]
    rfl
  have h5 : ((d (∑ t ∈ T, t b) - ∑ t ∈ T, t b : Om l) : PadicComplex l) =
      ∑ s ∈ T, (AI.actC (d * s) ((b : PadicComplex l) - y) - AI.actC s ((b : PadicComplex l) - y)) +
        ∑ s ∈ T, (AI.actC (d * s) y - AI.actC s y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_add_distrib, map_sum, ← Finset.sum_sub_distrib, PadicComplex.coe_eq, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sub, map_sub, map_sub, AI.actC_ext, AI.actC_ext, PadicComplex.coe_eq,
      PadicComplex.coe_eq, AlgEquiv.mul_apply]
    ring
  rw [← PadicComplex.norm_extends l, h5]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ((h3 ▸ h2).trans hr))
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr0 fun s _ => ?_
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [AI.actC_norm]; exact hb
  · rw [norm_neg, AI.actC_norm]; exact hb

theorem fixed_of_near (hn : ∀ (g : GQ l) (x : Om l), ‖g x‖ = ‖x‖) (D A : Subgroup (GQ l))
    (hAD : A ≤ D) (S : Finset (GQ l)) (hS : Reps D A S) (a u : Om l) (ha0 : a ≠ 0) (ha1 : ‖a‖ < 1)
    (haD : ∀ d ∈ D, d a = a) (hu1 : ‖u‖ ≤ 1) (hu : ‖a‖ ≤ ‖∑ s ∈ S, s u‖)
    (hnear : ∀ y : Om l, ‖y‖ ≤ 1 → (∀ n ∈ A, n y = y) → ∀ d ∈ D,
      ‖d (u * y) - u * y‖ ≤ ‖a‖ ^ 3)
    (y : Om l) (hy : ∀ n ∈ A, n y = y) (g : GQ l) (hg : g ∈ D) : g y = y := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hdu : ∀ d ∈ D, ‖d u - u‖ ≤ ‖a‖ ^ 3 := fun d hd => by
    simpa using hnear 1 (by simp) (by simp) d hd
  set m : Om l := (S.card : Om l) with hm
  have hsplit : ∀ w : Om l, ∑ s ∈ S, s w = m * w + ∑ s ∈ S, (s w - w) := fun w => by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have h3 : ‖a‖ ^ 3 < ‖a‖ := pow_lt_self_of_lt_one₀ hapos ha1 (by norm_num)
  have hmu : ‖a‖ ≤ ‖m‖ * ‖u‖ := by
    rw [hsplit] at hu
    have h1 := hu.trans (IsUltrametricDist.norm_add_le_max _ _)
    have h2 : ‖∑ s ∈ S, (s u - u)‖ ≤ ‖a‖ ^ 3 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        fun s hs => hdu s (hS.1 s hs)
    rcases le_max_iff.1 h1 with h | h
    · rwa [norm_mul] at h
    · linarith
  have hm1 : ‖m‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  have ham : ‖a‖ ≤ ‖m‖ := hmu.trans (mul_le_of_le_one_right (norm_nonneg _) hu1)
  have hau : ‖a‖ ≤ ‖u‖ := hmu.trans (mul_le_of_le_one_left (norm_nonneg _) hm1)
  have hmove : ∀ w : Om l, ‖w‖ ≤ 1 → (∀ n ∈ A, n w = w) → ∀ d ∈ D, ‖d w - w‖ ≤ ‖a‖ ^ 2 := by
    intro w hw1 hw d hd
    have e : u * (d w - w) = (d (u * w) - u * w) + -((d u - u) * d w) := by
      rw [map_mul]; ring
    have h1 : ‖u * (d w - w)‖ ≤ ‖a‖ ^ 3 := by
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hnear w hw1 hw d hd) ?_)
      rw [norm_neg, norm_mul, hn]
      exact (mul_le_of_le_one_right (norm_nonneg _) hw1).trans (hdu d hd)
    rw [norm_mul] at h1
    have h2 := (mul_le_mul_of_nonneg_right hau (norm_nonneg (d w - w))).trans h1
    rw [pow_succ'] at h2
    exact le_of_mul_le_mul_left h2 hapos
  have hsmall : ∀ w : Om l, ‖w‖ ≤ 1 → (∀ n ∈ A, n w = w) → ∑ s ∈ S, s w = 0 → ‖w‖ ≤ ‖a‖ := by
    intro w hw1 hw h0
    rw [hsplit, add_eq_zero_iff_eq_neg] at h0
    have h1 : ‖m * w‖ ≤ ‖a‖ ^ 2 := by
      rw [h0, norm_neg]
      exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        fun s hs => hmove w hw1 hw s (hS.1 s hs)
    rw [norm_mul] at h1
    have h2 := (mul_le_mul_of_nonneg_right ham (norm_nonneg w)).trans h1
    rw [pow_two] at h2
    exact le_of_mul_le_mul_left h2 hapos
  have hzero : ∀ w : Om l, (∀ n ∈ A, n w = w) → ∑ s ∈ S, s w = 0 → w = 0 := by
    intro w hw h0
    by_contra hw0
    obtain ⟨k, hk1, hk2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.2 hw0) ((one_lt_inv₀ hapos).2 ha1)
    have hpos : 0 < ‖a‖ ^ (k + 1) := zpow_pos hapos _
    have h1 := hsmall (a ^ (k + 1) * w) (by
      rw [norm_mul, norm_zpow]
      refine (mul_le_mul_of_nonneg_left hk2 hpos.le).trans ?_
      rw [inv_zpow, mul_inv_cancel₀ hpos.ne'])
      (fun n hnA => by rw [map_mul, map_zpow₀, haD n (hAD hnA), hw n hnA]) (by
        rw [← mul_zero (a ^ (k + 1)), ← h0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [map_mul, map_zpow₀, haD s (hS.1 s hs)])
    rw [norm_mul, norm_zpow] at h1
    have h2 := mul_lt_mul_of_pos_left hk1 hpos
    rw [inv_zpow, zpow_add_one₀ hapos.ne', mul_comm _ ‖a‖, mul_assoc,
      mul_inv_cancel₀ (zpow_pos hapos k).ne', mul_one, mul_comm ‖a‖, ← zpow_add_one₀ hapos.ne'] at h2
    linarith
  have htr : ∀ d ∈ D, d (∑ s ∈ S, s y) = ∑ s ∈ S, s y := fun d hd => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_shift D A S hS.1 hS.2 (fun g => g y) ?_ d hd
    intro g v _ hv
    change g (v y) = g y
    rw [hy v hv]
  have h0 := hzero (m * y - ∑ s ∈ S, s y)
    (fun n hnA => by rw [map_sub, map_mul, hm, map_natCast, hy n hnA, htr n (hAD hnA)]) (by
      rw [Finset.sum_congr rfl fun s hs => show s (m * y - ∑ s ∈ S, s y) =
        m * s y - ∑ s ∈ S, s y by rw [map_sub, map_mul, hm, map_natCast, htr s (hS.1 s hs)],
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, sub_self])
  have h1 := htr g hg
  rw [← sub_eq_zero.1 h0, map_mul, hm, map_natCast] at h1
  exact mul_left_cancel₀ (norm_pos_iff.1 (hapos.trans_le ham)) h1

theorem faithH : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI := by
  intro l _ P AI L g hg hfix
  have hp : l.Prime := Fact.out
  have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hn : ∀ (g : GQ l) (x : Om l), ‖g x‖ = ‖x‖ := fun g x => by
    rw [← PadicComplex.norm_extends l, ← AI.actC_ext, AI.actC_norm, PadicComplex.norm_extends]
  let K : FinExt l := ⟨⊥, inferInstance⟩
  have hH : ∀ h : GQ l, h ∈ Hinf K ↔ P.χQ h = 1 := fun h =>
    ((cyc_basic l P.χQ P.χQ_cyc).2.2 K h (by
      have : K0 K = ⊥ := bot_inf_eq _
      rw [this, IntermediateField.fixingSubgroup_bot]; trivial)).2
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let E : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] L.1 (Om l)
  have hLE : L.1 ≤ E := IntermediateField.le_normalClosure _
  haveI : FiniteDimensional ℚ_[l] E := inferInstance
  haveI : Normal ℚ_[l] E := inferInstance
  haveI : E.fixingSubgroup.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen E.fixingSubgroup E.fixingSubgroup_isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  have hsup : (Kinf K ⊔ E).fixingSubgroup = Hinf K ⊓ E.fixingSubgroup :=
    IntermediateField.fixingSubgroup_sup
  have hst : ∀ h ∈ Hinf K, ∀ x ∈ Kinf K ⊔ E, h x ∈ Kinf K ⊔ E := by
    intro h hh
    have : Kinf K ⊔ E ≤ (Kinf K ⊔ E).comap (h : Om l →ₐ[ℚ_[l]] Om l) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · change h x ∈ Kinf K ⊔ E
        rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx]
        exact (le_sup_left : Kinf K ≤ Kinf K ⊔ E) hx
      · change h x ∈ Kinf K ⊔ E
        have h1 := AlgEquiv.restrictNormal_commutes h E ⟨x, hx⟩
        have h2 : h x ∈ E := by
          have : h x = (h.restrictNormal E ⟨x, hx⟩ : E) := h1.symm
          rw [this]; exact Subtype.property _
        exact (le_sup_right : E ≤ Kinf K ⊔ E) h2
    exact fun x hx => this hx
  set N := (Kinf K ⊔ E).fixingSubgroup with hN
  let A : Subgroup (GQ l) := Hinf K ⊓ GK L
  let D : Subgroup (GQ l) :=
    { carrier := {d | d ∈ Hinf K ∧ ∀ x : OCb l, (∀ h ∈ A, AI.actT h x = x) → AI.actT d x = x}
      one_mem' := ⟨one_mem _, fun x _ => by rw [map_one]; rfl⟩
      mul_mem' := fun {c d} hc hd => ⟨mul_mem hc.1 hd.1, fun x hx => by
        rw [map_mul AI.actT, RingAut.mul_apply, hd.2 x hx, hc.2 x hx]⟩
      inv_mem' := fun {c} hc => ⟨inv_mem hc.1, fun x hx => by
        conv_lhs => rw [← hc.2 x hx]
        rw [← RingAut.mul_apply, ← map_mul AI.actT, inv_mul_cancel, map_one]; rfl⟩ }
  have hDH : D ≤ Hinf K := fun d hd => hd.1
  have hAD : A ≤ D := fun d hd => ⟨hd.1, fun x hx => hx d hd⟩
  have hNA : N ≤ A := by
    rw [hsup]
    exact inf_le_inf_left _ (IntermediateField.fixingSubgroup_le hLE)
  have hgD : g ∈ D := ⟨(hH g).2 hg, fun x hx => hfix x fun h h1 h2 => hx h ⟨(hH h).2 h2, h1⟩⟩
  obtain ⟨S₁, hS₁⟩ := exists_reps' (Hinf K) D E.fixingSubgroup (hsup ▸ hNA.trans hAD)
  obtain ⟨S₂, hS₂⟩ := exists_reps' D A E.fixingSubgroup
    ((inf_le_inf_right _ hDH).trans (hsup ▸ hNA))
  obtain ⟨T, hT⟩ := exists_reps' A N E.fixingSubgroup
    ((inf_le_inf_right _ (hAD.trans hDH)).trans hsup.ge)
  obtain ⟨R₂, hR₂, hs₂⟩ := reps_mul hAD hNA hS₂ hT
  obtain ⟨R, hR, hs⟩ := reps_mul hDH (hNA.trans hAD) hS₁ hR₂
  obtain ⟨r, hr0, hr1, hroot⟩ := approx_root hn K (Kinf K ⊔ E) R le_sup_left hst hR.1 hR.2
  have hr' : max r (l : ℝ)⁻¹ < 1 := max_lt hr1 (inv_lt_one_of_one_lt₀ hl)
  have hr'0 : 0 ≤ max r (l : ℝ)⁻¹ := le_max_of_le_left hr0
  obtain ⟨a, ha, hra, ha1⟩ := exists_near_one K ((max r (l : ℝ)⁻¹) ^ ((3 : ℕ)⁻¹ : ℝ))
    (Real.rpow_nonneg hr'0 _) (Real.rpow_lt_one hr'0 hr' (by norm_num))
  have hra3 : max r (l : ℝ)⁻¹ ≤ ‖a‖ ^ 3 := by
    rw [← Real.rpow_inv_natCast_pow hr'0 (n := 3) (by norm_num)]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hr'0 _) hra.le 3
  have ha0 : a ≠ 0 := norm_pos_iff.1 ((Real.rpow_nonneg hr'0 _).trans_lt hra)
  obtain ⟨e, heM, he1, he⟩ :=
    trace_almost_onto l K (Kinf K ⊔ E) R le_sup_left hst hR.1 hR.2 a ha ha1
  have heN : ∀ n ∈ N, n e = e := fun n hnN =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hnN e heM
  have key : ∀ b : Om l, ‖b‖ ≤ 1 → (∀ n ∈ N, n b = b) → ∀ d ∈ D,
      ‖d (∑ t ∈ T, t b) - ∑ t ∈ T, t b‖ ≤ ‖a‖ ^ 3 := by
    intro b0 hb01 hb0 d hd
    let X := {c : Om l // ‖c‖ ≤ 1 ∧ ∀ n ∈ N, n c = c}
    have hstep : ∀ b : X, ∃ c : X, ‖c.1 ^ l - b.1‖ ≤ r := fun b => by
      obtain ⟨c, hc, hc'⟩ := hroot b.1 b.2.1 b.2.2
      exact ⟨⟨c, hc⟩, hc'⟩
    choose f hf using hstep
    let b : ℕ → X := fun j => f^[j] ⟨b0, hb01, hb0⟩
    obtain ⟨x, y, hxN, hxy, hy⟩ := exists_tilt_near AI N r hr0 hr1
      (fun j => ⟨((b j).1 : PadicComplex l), (mem_OC _).2 (by
        rw [PadicComplex.norm_extends]; exact (b j).2.1)⟩)
      (fun j n hnL => by
        change AI.actC n ((b j).1 : PadicComplex l) = ((b j).1 : PadicComplex l)
        rw [AI.actC_ext, (b j).2.2 n hnL])
      (fun j => by
        change ‖((b (j + 1)).1 : PadicComplex l) ^ l - ((b j).1 : PadicComplex l)‖ ≤ r
        have h1 := hf (b j)
        rw [← PadicComplex.norm_extends l, PadicComplex.coe_eq, map_sub, map_pow] at h1
        have h2 : b (j + 1) = f (b j) := Function.iterate_succ_apply' f j _
        rw [h2]
        exact h1)
    refine near_of_tilt AI T d x y hxy b0 _ ((le_max_right _ _).trans hra3)
      (le_trans hy ((le_max_left _ _).trans hra3)) (hd.2 _ fun h hh => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have := sum_shift A N T hT.1 hT.2 (fun g => AI.actT g x)
      (fun g v _ hv => by rw [map_mul AI.actT, RingAut.mul_apply, hxN v hv]) h hh
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul AI.actT, RingAut.mul_apply]
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_
  refine fixed_of_near hn D A hAD S₂ hS₂ a (∑ t ∈ T, t e) ha0 ha1
    (fun d hd => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hDH hd) a ha) ?_ ?_ ?_ y
    (fun n hnA => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hnA.2 y hy) g hgD
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => by
      rw [hn]; exact he1
  · rw [← he, hs (fun r => r e)]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun s _ => ?_
    rw [← hn s (∑ s ∈ S₂, s (∑ t ∈ T, t e))]
    apply le_of_eq
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs₂ (fun r => (s * r) e), map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    rfl
  · intro w hw1 hw d hd
    have h1 := key (e * w) (by
      rw [norm_mul]; exact mul_le_one₀ he1 (norm_nonneg _) hw1)
      (fun n hnN => by rw [map_mul, heN n hnN, hw n (hNA hnN)]) d hd
    have h2 : ∑ t ∈ T, t (e * w) = (∑ t ∈ T, t e) * w := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun t ht => by rw [map_mul, hw t (hT.1 t ht)]
    rwa [h2] at h1

end GlobalTheory.TiltFaithful
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithfulStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI := by
  first | exact @GlobalTheory.TiltFaithful.faithH | exact GlobalTheory.TiltFaithful.faithH | (intros; apply GlobalTheory.TiltFaithful.faithH <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_hwOf_fonOf_cmpOf : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  intro L A hT hW
  have key : ∀ (l : ℕ) [Fact l.Prime], ∃ H : LocHW l (L l), ∃ F : LocFon l (L l) (A l) H,
      Nonempty (LocCmpT l (L l) (A l) H F) := fun l _ =>
    GlobalTheory.T.exists_local_wach_functor l (L l) (A l) (hT l) (GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful l (L l) (A l)) (hW l)
  choose H F hC using key
  exact ⟨fun l _ => H l, fun l _ => F l, ⟨fun l _ => (hC l).some⟩⟩

end GlobalTheory.HWL
