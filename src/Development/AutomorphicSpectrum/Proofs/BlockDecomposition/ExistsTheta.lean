module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleSubfaceZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeFormsMapMemSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquiv
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem dZ_addEquiv_apply {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    e _ (dZ M r m c i) = dZ N r' m (fun i => e _ (c i)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dZ, map_sum, map_zsmul, hn]

theorem dZ_eq_zero_of_addEquiv {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, N (ent i)) (hc : dZ N r' m c = 0) :
    dZ M r m (fun i => (e _).symm (c i)) = 0 := by
  funext i
  apply (e _).injective
  rw [dZ_addEquiv_apply M N r r' e hn m, Pi.zero_apply, map_zero]
  simp only [AddEquiv.apply_symm_apply]
  exact congrFun hc i

theorem exP_of_addEquiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  intro ι _ M N _ _ r r' e hn hM
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : (e ∅).symm x = 0 := by
      apply h0
      intro i
      have h7 := hn (Finset.empty_subset (ent i)) ((e ∅).symm x)
      rw [AddEquiv.apply_symm_apply] at h7
      have h8 : r' (Finset.empty_subset (ent i)) x = 0 := hx i
      rw [h8] at h7
      exact (e _).injective (h7.trans (map_zero _).symm)
    simpa using congrArg (e ∅) hx'
  · intro c hc
    obtain ⟨x, hx⟩ := h1 (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn 0 c hc)
    refine ⟨e ∅ x, fun i => ?_⟩
    have h5 : r (Finset.empty_subset (ent i)) x = (e _).symm (c i) := hx i
    have h6 := hn (Finset.empty_subset (ent i)) x
    rw [h5, AddEquiv.apply_symm_apply] at h6
    exact h6.symm
  · intro m c hc
    obtain ⟨b, hb⟩ := h2 m (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn (m + 1) c hc)
    refine ⟨fun i => e _ (b i), ?_⟩
    funext i
    have h3 := dZ_addEquiv_apply M N r r' e hn m b i
    have h4 : dZ M r m b i = (e _).symm (c i) := congrFun hb i
    rw [h4, AddEquiv.apply_symm_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquivStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exP_of_compatible_equiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PmExactnessOfExP
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PmExactnessOfExP
set_option autoImplicit false

noncomputable section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

theorem cech_d_eq_dZ (P : PM.{0} R ι) (n : ℕ) (c : P.cech.X n) :
    P.cech.d n c = dZ P.M (fun h x => P.res h x) n c := by
  funext i
  simp only [CrystallineSemistableComparison.Cos.d, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, dZ]
  rfl

theorem cech_d_aug (P : PM.{0} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  rw [cech_d_eq_dZ]
  funext i
  have key : ∀ (k : Fin 2), P.res (ent_comp i k.succAbove) (P.aug x (i ∘ k.succAbove)) =
      P.res (Finset.empty_subset (ent i)) x := fun k => P.res_comp _ _ x
  simp only [dZ, Fin.sum_univ_two, key]
  simp
  rfl

theorem ex_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι),
    ExP P.M (fun h x => P.res h x) → P.Ex := by
  intro R _ ι _ P h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨cech_d_aug P, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [one_smul]
    exact h0 x fun i => congrFun hx i
  · obtain ⟨x, hx⟩ := h1 y ((cech_d_eq_dZ P 0 y).symm.trans hy)
    exact ⟨x, (funext hx).trans (one_smul _ _).symm⟩
  · obtain ⟨b, hb⟩ := h2 n y ((cech_d_eq_dZ P (n + 1) y).symm.trans hy)
    exact ⟨b, ((cech_d_eq_dZ P n b).trans hb).trans (one_smul _ _).symm⟩

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PmExactnessOfExPStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pm_exactness_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι), ExP P.M (fun h x => P.res h x) → P.Ex := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemScalarTowerExt
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemScalarTowerExt
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4 TensorProduct

section Core
variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A]
variable {P Q R P' Q' R' : Type} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
  [Module B P] [Module B Q] [Module B R]
  [AddCommGroup P'] [AddCommGroup Q'] [AddCommGroup R']
  [Module A P'] [Module A Q'] [Module A R'] [Module B P'] [Module B Q'] [Module B R']
  [IsScalarTower B A P'] [IsScalarTower B A Q'] [IsScalarTower B A R']

theorem equiv_lTensor {p : P →ₗ[B] P'} {q : Q →ₗ[B] Q'} (hp : IsBaseChange A p) (hq : IsBaseChange A q)
    (f : P →ₗ[B] Q) (f' : P' →ₗ[A] Q') (h : ∀ x, f' (p x) = q (f x)) (z : A ⊗[B] P) :
    f' (hp.equiv z) = hq.equiv (LinearMap.lTensor A f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [IsBaseChange.equiv_tmul, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exact_core [Module.Flat B A] {p : P →ₗ[B] P'} {q : Q →ₗ[B] Q'} {s : R →ₗ[B] R'}
    (hp : IsBaseChange A p) (hq : IsBaseChange A q) (hs : IsBaseChange A s)
    (f : P →ₗ[B] Q) (g : Q →ₗ[B] R) (f' : P' →ₗ[A] Q') (g' : Q' →ₗ[A] R')
    (hf : ∀ x, f' (p x) = q (f x)) (hg : ∀ x, g' (q x) = s (g x))
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) : ∀ y, g' y = 0 → ∃ x, f' x = y := by
  intro y hy
  let P0 : Submodule B P := (LinearMap.ker g).comap f
  let f0 : P0 →ₗ[B] Q := f ∘ₗ P0.subtype
  have h0 : Function.Exact f0 g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hex y hy
      exact ⟨⟨x, hy⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.2
  have h1 := Module.Flat.lTensor_exact A h0
  have h2 : LinearMap.lTensor A g (hq.equiv.symm y) = 0 := by
    apply hs.equiv.injective
    rw [← equiv_lTensor hq hs g g' hg, LinearEquiv.apply_symm_apply, hy, map_zero]
  obtain ⟨z, hz⟩ := (h1 _).1 h2
  refine ⟨hp.equiv (LinearMap.lTensor A P0.subtype z), ?_⟩
  have h3 : LinearMap.lTensor A f (LinearMap.lTensor A P0.subtype z) = LinearMap.lTensor A f0 z := by
    simp only [f0, LinearMap.lTensor_comp, LinearMap.comp_apply]
  rw [equiv_lTensor hp hq f f' hf, h3, hz, LinearEquiv.apply_symm_apply]

theorem inj_core [Module.Flat B A] {q : Q →ₗ[B] Q'} {s : R →ₗ[B] R'}
    (hq : IsBaseChange A q) (hs : IsBaseChange A s)
    (g : Q →ₗ[B] R) (g' : Q' →ₗ[A] R') (hg : ∀ x, g' (q x) = s (g x))
    (hinj : ∀ y, g y = 0 → y = 0) : ∀ y, g' y = 0 → y = 0 := by
  intro y hy
  have hi : Function.Injective g := (injective_iff_map_eq_zero g).2 hinj
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := A) g hi
  have h2 : LinearMap.lTensor A g (hq.equiv.symm y) = 0 := by
    apply hs.equiv.injective
    rw [← equiv_lTensor hq hs g g' hg, LinearEquiv.apply_symm_apply, hy, map_zero]
  have h3 : hq.equiv.symm y = 0 := h1 (h2.trans (map_zero _).symm)
  simpa using h3
end Core

section Cech
variable {ι : Type} [DecidableEq ι]

def dZL (K : Type) [CommRing K] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module K (M S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (hr : ∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap K (r h)) (m : ℕ) :
    (∀ i : Fin (m + 1) → ι, M (ent i)) →ₗ[K] ∀ i : Fin (m + 2) → ι, M (ent i) where
  toFun := dZ M r m
  map_add' c c' := by
    funext i
    simp only [Pi.add_apply, dZ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_add]
    exact congrArg _ ((hr (ent_comp i k.succAbove)).map_add _ _)
  map_smul' a c := by
    funext i
    rw [RingHom.id_apply, Pi.smul_apply]
    change ∑ k : Fin (m + 2), _ = a • ∑ k : Fin (m + 2), _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm a]
    exact congrArg _ ((hr (ent_comp i k.succAbove)).map_smul a _)

def augL (K : Type) [CommRing K] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module K (M S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (hr : ∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap K (r h)) :
    M ∅ →ₗ[K] ∀ i : Fin (0 + 1) → ι, M (ent i) where
  toFun x i := r (Finset.empty_subset (ent i)) x
  map_add' x y := by
    funext i
    exact (hr _).map_add x y
  map_smul' a x := by
    funext i
    exact (hr _).map_smul a x

theorem exP_flat : ∀ {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Flat B A] {ι : Type}
    [DecidableEq ι] [Fintype ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module B (M S)]
    [∀ S, AddCommGroup (N S)] [∀ S, Module A (N S)] [∀ S, Module B (N S)] [∀ S, IsScalarTower B A (N S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap B (r h)) →
    ∀ (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap A (r' h)) →
    ∀ (ψ : ∀ S, M S →ₗ[B] N S), (∀ S, IsBaseChange A (ψ S)) →
    (∀ {S T : Finset ι} (h : S ⊆ T) x, r' h (ψ S x) = ψ T (r h x)) → ExP M r → ExP N r' := by
  intro B A _ _ _ _ ι _ _ M N _ _ _ _ _ _ r hr r' hr' ψ hψ hn hM
  let Ψ : ∀ m : ℕ, (∀ i : Fin (m + 1) → ι, M (ent i)) →ₗ[B] ∀ i : Fin (m + 1) → ι, N (ent i) :=
    fun m => .pi fun i => ψ (ent i) ∘ₗ .proj i
  have hΨ : ∀ m, IsBaseChange A (Ψ m) := fun m => IsBaseChange.pi _ fun i => hψ _
  have hd : ∀ m c, dZL A N r' hr' m (Ψ m c) = Ψ (m + 1) (dZL B M r hr m c) := by
    intro m c
    funext i
    change ∑ k : Fin (m + 2), _ = ψ _ (∑ k : Fin (m + 2), _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    exact hn _ _
  have ha : ∀ x, augL A N r' hr' (ψ ∅ x) = Ψ 0 (augL B M r hr x) := by
    intro x
    funext i
    exact hn _ _
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact inj_core (hψ ∅) (hΨ 0) (augL B M r hr) (augL A N r' hr') ha
      (fun y hy => h1 y fun i => congrFun hy i) x (funext hx)
  · intro c hc
    obtain ⟨x, hx⟩ := exact_core (hψ ∅) (hΨ 0) (hΨ 1) (augL B M r hr) (dZL B M r hr 0)
      (augL A N r' hr') (dZL A N r' hr' 0) ha (hd 0)
      (fun y hy => by
        obtain ⟨x, hx⟩ := h2 y hy
        exact ⟨x, funext hx⟩) c hc
    exact ⟨x, fun i => congrFun hx i⟩
  · intro m c hc
    exact exact_core (hΨ m) (hΨ (m + 1)) (hΨ (m + 2)) (dZL B M r hr m) (dZL B M r hr (m + 1))
      (dZL A N r' hr' m) (dZL A N r' hr' (m + 1)) (hd m) (hd (m + 1)) (h3 m) c hc

end Cech
end GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemScalarTowerExtStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finset_system_scalar_tower_ext : ∀ {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Flat B A] {ι : Type} [DecidableEq ι] [Fintype ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module B (M S)] [∀ S, AddCommGroup (N S)] [∀ S, Module A (N S)] [∀ S, Module B (N S)] [∀ S, IsScalarTower B A (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap B (r h)) → ∀ (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap A (r' h)) → ∀ (ψ : ∀ S, M S →ₗ[B] N S), (∀ S, IsBaseChange A (ψ S)) → (∀ {S T : Finset ι} (h : S ⊆ T) x, r' h (ψ S x) = ψ T (r h x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat.exP_flat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUnique
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}


variable (K n d) in
def tau : Bp K n d := ∏ e, MvPolynomial.X e

theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (h : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst h; rfl

theorem mon_zero (M : AddSubmonoid (Gam n d)) : mon K (0 : Gam n d) M.zero_mem = 1 := rfl

theorem mon_pow {M : AddSubmonoid (Gam n d)} (g : Gam n d) (hg : g ∈ M) (k : ℕ) :
    mon K g hg ^ k = mon K (k • g) (M.nsmul_mem hg k) := by
  induction k with
  | zero => rw [pow_zero]; exact ((mon_congr (zero_nsmul g) _ M.zero_mem).trans (mon_zero M)).symm
  | succ k ih => rw [pow_succ, ih, mon_mul]; exact mon_congr (succ_nsmul g k).symm _ _

theorem mon_prod {M : AddSubmonoid (Gam n d)} (s : Finset (E n d)) (f : E n d → Gam n d) (hf : ∀ e, f e ∈ M) :
    ∏ e ∈ s, mon K (f e) (hf e) = mon K (∑ e ∈ s, f e) (M.sum_mem fun e _ => hf e) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact (mon_zero M).symm
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha).symm _ _

theorem poly_monomial (S : Finset (Fin d)) (k : E n d → ℕ) :
    poly n K S (∏ e, MvPolynomial.X e ^ k e) =
      mon K (∑ e, k e • oneE e) ((cone S).sum_mem fun e _ => (cone S).nsmul_mem (oneE_mem S e) (k e)) := by
  rw [map_prod]
  simp only [map_pow, poly_X, mon_pow]
  exact mon_prod _ _ _

theorem poly_tau_pow (S : Finset (Fin d)) (N : ℕ) :
    ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), (∀ e, g e = N) ∧
      poly n K S (tau K n d ^ N) = mon K g hg := by
  refine ⟨N • ∑ e, oneE e, (cone S).nsmul_mem ((cone S).sum_mem fun e _ => oneE_mem S e) N, fun e => ?_, ?_⟩
  · simp only [Pi.smul_apply, Finset.sum_apply, oneE, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul, mul_one]
  · rw [map_pow, tau, map_prod]
    simp only [poly_X]
    rw [mon_prod, mon_pow]

theorem exists_poly (S : Finset (Fin d)) (y : R0 K n d S) :
    ∃ (N : ℕ) (b : Bp K n d), poly n K S (tau K n d ^ N) * y = poly n K S b := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨N₁, b₁, h₁⟩ := hf
    obtain ⟨N₂, b₂, h₂⟩ := hg
    refine ⟨N₁ + N₂, tau K n d ^ N₂ * b₁ + tau K n d ^ N₁ * b₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m c =>
    obtain ⟨g, hg⟩ := m
    let N : ℕ := ∑ e, (g e).natAbs
    have hN : ∀ e, 0 ≤ (N : ℤ) + g e := fun e => by
      have h1 : (g e).natAbs ≤ N := Finset.single_le_sum (f := fun e => (g e).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      omega
    obtain ⟨g', hg', hc, hp⟩ := poly_tau_pow (K := K) (n := n) S N
    refine ⟨N, c • ∏ e, MvPolynomial.X e ^ ((N : ℤ) + g e).toNat, ?_⟩
    have h1 : (AddMonoidAlgebra.single ⟨g, hg⟩ c : R0 K n d S) = c • mon K g hg := by
      simp [mon]
    rw [map_smul, poly_monomial, h1, hp, mul_smul_comm, mon_mul]
    congr 1
    refine mon_congr ?_ _ _
    funext e
    have h2 : (∑ e', ((N : ℤ) + g e').toNat • (oneE e' : Gam n d)) e = ((N : ℤ) + g e).toNat := by
      simp [oneE, Finset.sum_apply, Pi.single_apply]
    rw [h2, Pi.add_apply, hc, Int.toNat_of_nonneg (hN e)]

theorem mul_injective (T : Finset (Fin d)) (N : ℕ) :
    Function.Injective fun x : R0 K n d T => poly n K T (tau K n d ^ N) * x := by
  intro x y hxy
  have hi : Function.Injective (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) :=
    AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective _)
  apply hi
  obtain ⟨g, hg, -, hp⟩ := poly_tau_pow (K := K) (n := n) T N
  have h := congrArg (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) hxy
  simp only [map_mul, hp, incl_mon] at h
  have hu : IsUnit (mon K g (AddSubmonoid.mem_top g) : Lr K n d) := by
    refine isUnit_iff_exists_inv.2 ⟨mon K (-g) (AddSubmonoid.mem_top _), ?_⟩
    rw [mon_mul]
    exact (mon_congr (add_neg_cancel g) _ _).trans (mon_zero _)
  exact hu.mul_left_cancel h

variable {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d)

theorem eq_zero_of_mul {T : Finset (Fin d)} (θ' : R0 K n d T →ₐ[K] C.R T)
    (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)) (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ'))
    (N : ℕ) (z : C.R T) (hz : toR C T (phi C (tau K n d ^ N)) * z = 0) : z = 0 := by
  haveI := etale_Aa C
  haveI : Module.Flat (Bp K n d) (Aa C) := Algebra.Smooth.flat _ _
  let f : R0 K n d T →ₗ[Bp K n d] R0 K n d T := LinearMap.mulLeft (Bp K n d) (poly n K T (tau K n d ^ N))
  have hf : Function.Injective f := mul_injective T N
  have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := Aa C) f hf
  let v : Rb C T := toR C T (phi C (tau K n d ^ N))
  have key : ∀ w : TensorProduct (Bp K n d) (Aa C) (R0 K n d T),
      hb.equiv (f.lTensor (Aa C) w) = v * hb.equiv w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [map_add (f := _), hu, hu', mul_add]
    | tmul a x =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      change toR C T a * θ' (poly n K T (tau K n d ^ N) * x) = toR C T (phi C (tau K n d ^ N)) * (toR C T a * θ' x)
      rw [map_mul, hθ']
      ring
  have main : ∀ z' : Rb C T, v * z' = 0 → z' = 0 := by
    intro z' hz'
    have hw : f.lTensor (Aa C) (hb.equiv.symm z') = 0 := by
      apply hb.equiv.injective
      rw [map_zero, key, LinearEquiv.apply_symm_apply]
      exact hz'
    have h3 := hl (hw.trans (map_zero _).symm)
    exact hb.equiv.symm.map_eq_zero_iff.1 h3
  exact main z hz

theorem theta_unique {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T)
    (h₁ : ∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) (h₂ : ∀ b, θ₂ (poly n K S b) = toR C T (phi C b))
    (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b))
    (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ')) : θ₁ = θ₂ := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨N, b, h⟩ := exists_poly S y
  have e₁ := congrArg θ₁ h
  have e₂ := congrArg θ₂ h
  rw [map_mul, h₁, h₁] at e₁
  rw [map_mul, h₂, h₂] at e₂
  refine sub_eq_zero.1 (eq_zero_of_mul C θ' hθ' hb N _ ?_)
  rw [mul_sub, e₁, e₂, sub_self]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUniqueStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_base_change_map_unique : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T), (∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) → (∀ b, θ₂ (poly n K S b) = toR C T (phi C b)) → ∀ (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)), IsBaseChange (Aa C) (thetaLin C θ' hθ') → θ₁ = θ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChange
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto
namespace RelBC
open TensorProduct

theorem multilinear_mem_of_span {R ι M N : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : (ι → M) →ₘₗ[R] N) (X : ι → Set M) (T : Submodule R N)
    (h : ∀ w : ι → M, (∀ i, w i ∈ X i) → f w ∈ T) (v : ι → M)
    (hv : ∀ i, v i ∈ Submodule.span R (X i)) : f v ∈ T := by
  have key : ∀ (s : Finset ι) (w : ι → M), (∀ i ∈ s, w i ∈ Submodule.span R (X i)) → (∀ i, i ∉ s → w i ∈ X i) →
      f w ∈ T := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro w _ hw; exact h w fun i => hw i (by simp)
    | insert i s hi ih =>
      intro w h1 h2
      have hup : ∀ x ∈ Submodule.span R (X i), f (Function.update w i x) ∈ T := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          refine ih _ (fun j hj => ?_) (fun j hj => ?_)
          · have hji : j ≠ i := fun e => hi (e ▸ hj)
            rw [Function.update_of_ne hji]
            exact h1 j (Finset.mem_insert_of_mem hj)
          · by_cases hji : j = i
            · subst hji
              rw [Function.update_self]
              exact hx
            · rw [Function.update_of_ne hji]
              exact h2 j (by simp [hji, hj])
        | zero =>
          rw [f.map_coord_zero i (Function.update_self i 0 w)]
          exact T.zero_mem
        | add x y _ _ hx hy =>
          rw [f.map_update_add]
          exact T.add_mem hx hy
        | smul c x _ hx =>
          rw [f.map_update_smul]
          exact T.smul_mem c hx
      have := hup _ (h1 i (Finset.mem_insert_self _ _))
      rwa [Function.update_eq_self] at this
  exact key Finset.univ v (fun i _ => hv i) (fun i hi => absurd (Finset.mem_univ i) hi)

theorem isBaseChange_of_pushout {P Q R₀ R M N : Type*} [CommRing P] [CommRing Q] [CommRing R₀] [CommRing R]
    [Algebra P Q] [Algebra P R₀] [Algebra P R] [Algebra Q R] [Algebra R₀ R] [IsScalarTower P Q R] [IsScalarTower P R₀ R]
    [Algebra.IsPushout P Q R₀ R] [AddCommGroup M] [Module P M] [Module R₀ M] [IsScalarTower P R₀ M]
    [AddCommGroup N] [Module P N] [Module Q N] [Module R N] [Module R₀ N] [IsScalarTower P Q N] [IsScalarTower Q R N]
    [IsScalarTower R₀ R N] (φ : M →ₗ[R₀] N) (f : M →ₗ[P] N) (e : ∀ x, f x = φ x) (hφ : IsBaseChange R φ) :
    IsBaseChange Q f := by
  have hc : (f.liftBaseChange Q : Q ⊗[P] M → N) =
      φ.liftBaseChange R ∘ (Algebra.IsPushout.cancelBaseChange P Q R₀ R M).symm := by
    funext z
    induction z with
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul s m => simp [e]
  have hb : Function.Bijective (φ.liftBaseChange R) := by
    have : (φ.liftBaseChange R : R ⊗[R₀] M → N) = hφ.equiv := by
      funext z
      induction z with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s m => simp
    rw [this]
    exact hφ.equiv.bijective
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange Q) ?_) fun x => ?_
  swap
  · change (f.liftBaseChange Q) (1 ⊗ₜ x) = f x
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  rw [hc]
  exact hb.comp (LinearEquiv.bijective _)

theorem isBaseChange_restrict {P Q U M V N : Type*} [CommRing P] [CommRing Q] [Algebra P Q] [Module.Flat P Q]
    [AddCommGroup U] [Module P U] [AddCommGroup M] [Module P M] [AddCommGroup V] [Module P V] [Module Q V]
    [IsScalarTower P Q V] [AddCommGroup N] [Module P N] [Module Q N] [IsScalarTower P Q N]
    (f : M →ₗ[P] N) (hf : IsBaseChange Q f) (u : U →ₗ[P] M) (hu : Function.Injective u) (g : U →ₗ[P] V)
    (j : V →ₗ[Q] N) (hj : Function.Injective j) (hg : ∀ x, j (g x) = f (u x))
    (hs : ∀ v, j v ∈ Submodule.span Q (Set.range fun x => f (u x))) : IsBaseChange Q g := by
  have hc : ∀ z : Q ⊗[P] U, j (g.liftBaseChange Q z) = hf.equiv (u.lTensor Q z) := by
    intro z
    induction z with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul s m => simp [hg]
  have hinj : Function.Injective (g.liftBaseChange Q) := fun x y h => by
    have h2 := congrArg j h
    rw [hc, hc] at h2
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := Q) u hu (hf.equiv.injective h2)
  have hsurj : Function.Surjective (g.liftBaseChange Q) := by
    intro v
    have h3 : j v ∈ LinearMap.range (j ∘ₗ g.liftBaseChange Q) := by
      refine (Submodule.span_le.2 ?_) (hs v)
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, by simp [hg]⟩
    obtain ⟨z, hz⟩ := h3
    exact ⟨z, hj hz⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange Q) ⟨hinj, hsurj⟩) fun x => ?_
  change (g.liftBaseChange Q) (1 ⊗ₜ x) = g x
  rw [LinearMap.liftBaseChange_tmul, one_smul]

theorem mem_span_of_mem_span {Q R N : Type*} [CommRing Q] [CommRing R] [Algebra Q R] [AddCommGroup N] [Module R N]
    [Module Q N] [IsScalarTower Q R N] (G : Set R) (hG : ∀ r : R, r ∈ Submodule.span Q G) (X : Set N)
    (hX : ∀ c ∈ G, ∀ x ∈ X, c • x ∈ X) {y : N} (hy : y ∈ Submodule.span R X) : y ∈ Submodule.span Q X := by
  have h1 : ∀ (r : R), ∀ x ∈ X, r • x ∈ Submodule.span Q X := by
    intro r x hx
    have hr := hG r
    induction hr using Submodule.span_induction with
    | mem c hc => exact Submodule.subset_span (hX c hc x hx)
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul q a _ ha => rw [smul_assoc]; exact Submodule.smul_mem _ q ha
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul r x _ hx =>
    have h2 : ∀ z ∈ Submodule.span Q X, r • z ∈ Submodule.span Q X := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx => exact h1 r x hx
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | smul q a _ ha => rw [smul_comm r q a]; exact Submodule.smul_mem _ q ha
    exact h2 x hx

theorem isBaseChange_core {P Q R₀ R M N U V : Type*} [CommRing P] [CommRing Q] [CommRing R₀] [CommRing R]
    [Algebra P Q] [Algebra P R₀] [Algebra P R] [Algebra Q R] [Algebra R₀ R] [IsScalarTower P Q R] [IsScalarTower P R₀ R]
    [Algebra.IsPushout P Q R₀ R] [Module.Flat P Q] [AddCommGroup M] [Module P M] [Module R₀ M] [IsScalarTower P R₀ M]
    [AddCommGroup N] [Module R N] [Module R₀ N] [IsScalarTower R₀ R N] [AddCommGroup U] [Module P U]
    [AddCommGroup V] [Module P V] [Module Q V] [IsScalarTower P Q V]
    (φ : M →ₗ[R₀] N) (hφ : IsBaseChange R φ) (u : U →ₗ[P] M) (hu : Function.Injective u)
    (hU : ∀ (c : R₀) x, ∃ x', u x' = c • u x) (g : U →ₗ[P] V) (j : V →+ N) (hj : Function.Injective j)
    (hq : ∀ (q : Q) v, j (q • v) = algebraMap Q R q • j v) (hg : ∀ x, j (g x) = φ (u x))
    (hs : ∀ v, j v ∈ Submodule.span R (Set.range fun x => φ (u x))) : IsBaseChange Q g := by
  letI : Module Q N := Module.compHom N (algebraMap Q R)
  letI : Module P N := Module.compHom N (algebraMap P R)
  haveI : IsScalarTower Q R N := ⟨fun q r n => by
    change (q • r) • n = algebraMap Q R q • (r • n)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower P Q N := ⟨fun p q n => by
    change algebraMap Q R (p • q) • n = algebraMap P R p • algebraMap Q R q • n
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]⟩
  let f : M →ₗ[P] N :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun p x => by
        change φ (p • x) = algebraMap P R p • φ x
        rw [← algebraMap_smul R₀ p x, map_smul, ← algebraMap_smul R (algebraMap P R₀ p),
          ← IsScalarTower.algebraMap_apply] }
  have hf : IsBaseChange Q f := isBaseChange_of_pushout φ f (fun _ => rfl) hφ
  let jq : V →ₗ[Q] N := { toFun := j, map_add' := map_add j, map_smul' := hq }
  refine isBaseChange_restrict f hf u hu g jq hj hg fun v => ?_
  refine mem_span_of_mem_span (Set.range (algebraMap R₀ R)) (fun r => ?_) _ ?_ (hs v)
  · have hpo : IsBaseChange Q (IsScalarTower.toAlgHom P R₀ R).toLinearMap := Algebra.IsPushout.out
    induction r using hpo.inductionOn with
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul s n h => exact Submodule.smul_mem _ s h
    | add a b ha hb => exact Submodule.add_mem _ ha hb
  · rintro _ ⟨c, rfl⟩ _ ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := hU c x
    refine ⟨x', ?_⟩
    change φ (u x') = _
    rw [hx', map_smul]
    exact (algebraMap_smul R c _).symm

theorem relOm_le_span {K R₀ R : Type} [CommRing K] [CommRing R₀] [CommRing R] [Algebra K R₀] [Algebra K R]
    (θ : R₀ →ₐ[K] R)
    (hD : ∀ ω : Ω[R⁄K], ω ∈ Submodule.span R (Set.range fun h => KaehlerDifferential.D K R (θ h)))
    (I₀ : Ideal R₀) (J : Ideal R) (hJ : J ≤ Ideal.span (θ '' (I₀ : Set R₀))) (a : ℕ) :
    relOm K J a ≤ Submodule.span R (Set.range fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) := by
  set T := Submodule.span R (Set.range fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) with hT
  have hgen : ∀ (h₀ : R₀) (h : Fin a → R₀), (h₀ ∈ I₀ ∨ ∃ k, h k ∈ I₀) →
      form K (θ h₀) (fun k => θ (h k)) ∈ T := fun h₀ h hh =>
    Submodule.subset_span ⟨⟨form K h₀ h, Submodule.subset_span ⟨h₀, h, hh, rfl⟩⟩, omMap_form θ h₀ h⟩
  have hW : ∀ (Y : Fin a → Set R₀) (c : R),
      (∀ h : Fin a → R₀, (∀ i, h i ∈ Y i) →
        c • exteriorPower.ιMulti R a (fun i => KaehlerDifferential.D K R (θ (h i))) ∈ T) →
      ∀ v : Fin a → Ω[R⁄K], (∀ i, v i ∈ Submodule.span R ((fun y => KaehlerDifferential.D K R (θ y)) '' Y i)) →
      c • exteriorPower.ιMulti R a v ∈ T := by
    intro Y c hP v hv
    have := multilinear_mem_of_span (exteriorPower.ιMulti R a (M := Ω[R⁄K])).toMultilinearMap
      (fun i => (fun y => KaehlerDifferential.D K R (θ y)) '' Y i) (T.comap (c • LinearMap.id)) (fun w hw => by
        choose h hh hw using hw
        have e : w = fun i => KaehlerDifferential.D K R (θ (h i)) := funext fun i => (hw i).symm
        subst e
        exact hP h hh) v hv
    exact this
  have hJ1 : ∀ g₀ ∈ J, ∀ v : Fin a → Ω[R⁄K], g₀ • exteriorPower.ιMulti R a v ∈ T := by
    intro g₀ hg v
    have hg' := hJ hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine hW (fun _ => Set.univ) (θ y) (fun h _ => hgen y h (Or.inl hy)) v fun i => ?_
      rw [Set.image_univ]
      exact hD (v i)
    | zero => rw [zero_smul]; exact T.zero_mem
    | add x y _ _ hx hy => rw [add_smul]; exact T.add_mem hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_smul]; exact T.smul_mem c hx
  set W := Submodule.span R ((fun y => KaehlerDifferential.D K R (θ y)) '' (I₀ : Set R₀)) with hWdef
  have hDy : ∀ y ∈ I₀, KaehlerDifferential.D K R (θ y) ∈ W := fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hWs : ∀ y ∈ I₀, ∀ ω : Ω[R⁄K], θ y • ω ∈ W := by
    intro y hy ω
    have hω := hD ω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have e : KaehlerDifferential.D K R (θ (y * h)) =
          θ y • KaehlerDifferential.D K R (θ h) + θ h • KaehlerDifferential.D K R (θ y) := by
        rw [map_mul, Derivation.leibniz]
      have e2 : θ y • KaehlerDifferential.D K R (θ h) =
          KaehlerDifferential.D K R (θ (y * h)) - θ h • KaehlerDifferential.D K R (θ y) := by
        rw [e, add_sub_cancel_right]
      change θ y • KaehlerDifferential.D K R (θ h) ∈ W
      rw [e2]
      exact W.sub_mem (hDy _ (I₀.mul_mem_right h hy)) (W.smul_mem _ (hDy y hy))
    | zero => rw [smul_zero]; exact W.zero_mem
    | add x z _ _ hx hz => rw [smul_add]; exact W.add_mem hx hz
    | smul c x _ hx => rw [smul_comm]; exact W.smul_mem c hx
  have hJ2 : ∀ g ∈ J, KaehlerDifferential.D K R g ∈ W ∧ ∀ ω : Ω[R⁄K], g • ω ∈ W := by
    intro g hg
    have hg' := hJ hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨hDy y hy, hWs y hy⟩
    | zero => exact ⟨by rw [map_zero]; exact W.zero_mem, fun ω => by rw [zero_smul]; exact W.zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨by rw [map_add (f := _)]; exact W.add_mem hx.1 hy.1, fun ω => by rw [add_smul]; exact W.add_mem (hx.2 ω) (hy.2 ω)⟩
    | smul c x _ hx =>
      refine ⟨?_, fun ω => ?_⟩
      · rw [smul_eq_mul, Derivation.leibniz]
        exact W.add_mem (W.smul_mem c hx.1) (hx.2 _)
      · rw [smul_eq_mul, mul_smul]
        exact W.smul_mem c (hx.2 ω)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g₀, g, hg, rfl⟩
  rcases hg with hg | ⟨k, hk⟩
  · exact hJ1 g₀ hg _
  · have h3 := hW (fun i => if i = k then (I₀ : Set R₀) else Set.univ) 1 (fun h hh => by
      have h4 := hgen 1 h (Or.inr ⟨k, by simpa using hh k⟩)
      rw [map_one] at h4
      exact h4) (fun i => KaehlerDifferential.D K R (g i)) (fun i => by
      by_cases hi : i = k
      · subst hi
        simpa using (hJ2 _ hk).1
      · simp only [if_neg hi, Set.image_univ]
        exact hD _)
    rw [one_smul] at h3
    exact T.smul_mem g₀ h3

theorem isBaseChange_relOm {K P Q R₀ R : Type} [CommRing K] [CommRing P] [CommRing Q] [CommRing R₀] [CommRing R]
    [Algebra K R₀] [Algebra K R] [Algebra P Q] [Algebra P R₀] [Algebra P R] [Algebra Q R] [IsScalarTower P Q R]
    [Algebra.Etale P Q] (θ : R₀ →ₐ[K] R) (hθ : ∀ p, θ (algebraMap P R₀ p) = algebraMap P R p)
    (f : R₀ →ₗ[P] R) (hf : ∀ x, f x = θ x) (hb : IsBaseChange Q f)
    (I₀ : Ideal R₀) (J : Ideal R) (hJ : J ≤ Ideal.span (θ '' (I₀ : Set R₀))) (a : ℕ)
    {V : Type} [AddCommGroup V] [Module P V] [Module Q V] [IsScalarTower P Q V] (j : V →+ Om K R a)
    (hj : Function.Injective j) (hq : ∀ (q : Q) v, j (q • v) = algebraMap Q R q • j v)
    (hr : ∀ v, j v ∈ relOm K J a) (g : relOm K I₀ a →ₗ[P] V)
    (hg : ∀ x, j (g x) = omMap θ a (x : Om K R₀ a)) : IsBaseChange Q g := by
  letI : Algebra R₀ R := θ.toRingHom.toAlgebra
  haveI : IsScalarTower K R₀ R := .of_algHom θ
  haveI : IsScalarTower P R₀ R := .of_algebraMap_eq fun p => (hθ p).symm
  haveI hpo : Algebra.IsPushout P Q R₀ R := ⟨by
    have e : (IsScalarTower.toAlgHom P R₀ R).toLinearMap = f := LinearMap.ext fun x => (hf x).symm
    rw [e]
    exact hb⟩
  haveI : Algebra.IsPushout P R₀ Q R := Algebra.IsPushout.symm hpo
  haveI : Algebra.FormallyEtale R₀ R := Algebra.FormallyEtale.of_equiv (Algebra.IsPushout.equiv P R₀ Q R)
  have h1 := KaehlerDifferential.isBaseChange_of_formallyEtale K R₀ R
  have hD : ∀ ω : Ω[R⁄K], ω ∈ Submodule.span R (Set.range fun h => KaehlerDifferential.D K R (θ h)) := by
    intro ω
    induction ω using h1.inductionOn with
    | smul s n h => exact Submodule.smul_mem _ s h
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul m =>
      have hm : m ∈ (⊤ : Submodule R₀ Ω[R₀⁄K]) := trivial
      rw [← KaehlerDifferential.span_range_derivation] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨y, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        rw [map_smul, ← algebraMap_smul R c]
        exact Submodule.smul_mem _ _ hx
  have h2 := GlobalTheory.TopForm.isBaseChange_exteriorPower h1 a
  have he : ∀ ω : Om K R₀ a, GlobalTheory.exteriorPowerMapOver R a (KaehlerDifferential.map K K R₀ R) ω = omMap θ a ω := by
    intro ω
    have hs : ω ∈ (⊤ : Submodule R₀ (Om K R₀ a)) := trivial
    rw [← exteriorPower.ιMulti_span] at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [GlobalTheory.exteriorPowerMapOver_ιMulti, omMap_ιMulti]
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [map_smul, omMap_smul, hx]
      exact (algebraMap_smul R c _).symm
  refine isBaseChange_core (R₀ := R₀) (R := R) _ h2 ((relOm K I₀ a).subtype.restrictScalars P) Subtype.val_injective
    (fun c x => ⟨c • x, rfl⟩) g j hj hq (fun x => by rw [hg]; exact (he _).symm) fun v => ?_
  have h3 := relOm_le_span θ hD I₀ J hJ a (hr v)
  have hfun : (fun x : relOm K I₀ a => omMap θ a (x : Om K R₀ a)) =
      fun x : relOm K I₀ a => GlobalTheory.exteriorPowerMapOver R a (KaehlerDifferential.map K K R₀ R) (x : Om K R₀ a) :=
    funext fun x => (he _).symm
  rw [hfun] at h3
  exact h3

end RelBC

theorem isBaseChange_psi {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d)
    {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b))
    (hb : IsBaseChange (Aa C) (thetaLin C θ hθ)) (a : ℕ) : IsBaseChange (Aa C) (psi C θ hθ a) := by
  haveI := etale_Aa C
  letI i1 : Algebra (Aa C) (C.R S) := inferInstanceAs (Algebra (Aa C) (Rb C S))
  letI i2 : Algebra (Bp K n d) (C.R S) := inferInstanceAs (Algebra (Bp K n d) (Rb C S))
  haveI i3 : IsScalarTower (Bp K n d) (Aa C) (C.R S) := inferInstanceAs (IsScalarTower (Bp K n d) (Aa C) (Rb C S))
  have hJ : C.I S ≤ Ideal.span (θ '' (I0 n K S : Set (R0 K n d S))) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine Ideal.subset_span ⟨mon K (oneE (Sum.inr k)) (oneE_mem S _), Ideal.subset_span ⟨k, hk, rfl⟩, ?_⟩
    rw [← poly_X, hθ]
    simp [toR, phi]
  exact RelBC.isBaseChange_relOm (K := K) (P := Bp K n d) (Q := Aa C) (R₀ := R0 K n d S) (R := C.R S) θ hθ
    (thetaLin C θ hθ) (fun _ => rfl) hb (I0 n K S) (C.I S) hJ a
    (V := relA C S a) (AddSubgroupClass.subtype (relOm K (C.I S) a)) Subtype.val_injective (fun _ _ => rfl)
    (fun v => v.2) (psi C θ hθ a) (fun _ => rfl)

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChangeStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_forms_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) → ∀ a : ℕ, IsBaseChange (Aa C) (psi C θ hθ a) := by
  intro K _ n d A _ _ C S θ hθ hb a
  exact GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi C θ hθ hb a
end
end

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

variable {K : Type} [Field K] {n d : ℕ}

theorem exists_theta {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) :
    ∃ (θ : ∀ S, R0 K n d S →ₐ[K] C.R S) (hθ : ∀ S b, θ S (poly n K S b) = toR C S (phi C b)),
      (∀ {S T : Finset (Fin d)} (h : S ⊆ T) y, C.res h (θ S y) = θ T (incl (cone_mono h) y)) ∧
      ∀ S, IsBaseChange (Aa C) (thetaLin C (θ S) (hθ S)) := by
  have key : ∀ S, ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
    · exact GlobalTheory.T.chart_empty_base_change C
    · obtain ⟨θ₁, h₁, hu, hb⟩ := GlobalTheory.T.chart_singleton_base_change C k
      exact GlobalTheory.T.chart_extend_base_change C S k hk θ₁ h₁ hu hb
  choose θ hθ bc using key
  refine ⟨θ, hθ, ?_, bc⟩
  intro S T h y
  have := GlobalTheory.T.chart_base_change_map_unique C ((C.res h).comp (θ S)) ((θ T).comp (incl (cone_mono h)))
    (fun b => by rw [AlgHom.comp_apply, hθ, res_toR]) (fun b => by rw [AlgHom.comp_apply, incl_poly h, hθ]) (θ T) (hθ T) (bc T)
  exact DFunLike.congr_fun this y

theorem Tset_ne_univ (g : Gam n d) (D : Finset (E n d)) (h : good g D) : Tset g D ≠ Finset.univ := by
  intro hu
  have hneg : ∀ j, g (Sum.inr j) ≤ 0 := fun j => by
    have : j ∈ Tset g D := hu ▸ Finset.mem_univ j
    rcases (Finset.mem_filter.1 this).2 with h | h
    · exact h.le
    · exact h.1.le
  have : tdeg g ≤ 0 := Finset.sum_nonpos fun j _ => hneg j
  have := h.2
  omega

theorem model_ex (a : ℕ) : ExP (fun S : Finset (Fin d) => relOm K (I0 n K S) a)
    (fun {S T} h => relMap (incl (cone_mono h)) (cone_ideal_map_mono (S := S) (T := T) h) a) := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.monomial_forms_basis (K := K) (n := n) (d := d) a
  refine GlobalTheory.T.finset_system_injective_extension (K := K) b (fun p => good p.1 p.2.1) (fun p => Tset p.1 p.2.1) (fun p h => Tset_ne_univ _ _ h) _ _
    (fun S => ((omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a).toAddMonoidHom).comp
      (relOm K (I0 n K S) a).subtype.toAddMonoidHom) ?_ ?_ ?_
  · intro S x y hxy
    exact Subtype.ext (GlobalTheory.T.cone_forms_map_injective S a hxy)
  · intro S S' h x
    change omMap _ a (omMap _ a (x : Om K (R0 K n d S) a)) = omMap _ a (x : Om K (R0 K n d S) a)
    rw [omMap_comp, incl_comp]
  · intro S w
    have hset : (b '' {l | good l.1 l.2.1 ∧ Tset l.1 l.2.1 ⊆ S}) =
        {w | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, p.2, hp.1, hp.2, hb p⟩
      · rintro ⟨g, D, h1, h2, rfl⟩
        exact ⟨(g, D), ⟨h1, h2⟩, hb _⟩
    rw [hset]
    constructor
    · rintro ⟨x, rfl⟩
      exact GlobalTheory.T.relative_forms_map_mem_span S a _ x.2
    · intro hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, D, h1, h2, rfl⟩ := hw
        obtain ⟨ω, hω, e⟩ := GlobalTheory.T.monomial_form_in_relative_image (K := K) S a g D h1 h2
        exact ⟨⟨ω, hω⟩, e⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
      | smul c x _ hx =>
        obtain ⟨x', rfl⟩ := hx
        exact ⟨c • x', map_smul (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) c _⟩

theorem h4a : ChartFormsCechExact := by
  intro K _ _ A _ _ n d hd C a P e he
  obtain ⟨θ, hθ, nat, bc⟩ := exists_theta C
  haveI := etale_Aa C
  have h1 := model_ex (K := K) (n := n) (d := d) a
  have h2 : ExP (fun S => relA C S a) (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) := by
    refine GlobalTheory.T.finset_system_scalar_tower_ext (B := Bp K n d) (A := Aa C) (fun S => relOm K (I0 n K S) a) (fun S => relA C S a) _ ?_ _ ?_
      (fun S => psi C (θ S) (hθ S) a) (fun S => GlobalTheory.T.chart_forms_base_change C (θ S) (hθ S) (bc S) a) ?_ h1
    · intro S T h
      refine ⟨map_add _, fun b ω => Subtype.ext ?_⟩
      change omMap (incl (cone_mono h)) a ((b • ω : relOm K (I0 n K S) a) : Om K (R0 K n d S) a) =
        ((b • relMap (incl (cone_mono h)) (cone_ideal_map_mono h) a ω : relOm K (I0 n K T) a) : Om K (R0 K n d T) a)
      have e1 : ∀ (U : Finset (Fin d)) (ω' : relOm K (I0 n K U) a), ((b • ω' : relOm K (I0 n K U) a) : Om K (R0 K n d U) a) =
          poly n K U b • (ω' : Om K (R0 K n d U) a) := fun U ω' =>
        (algebraMap_smul (R0 K n d U) b (ω' : Om K (R0 K n d U) a)).symm
      rw [e1, e1, omMap_smul, incl_poly h]
      rfl
    · intro S T h
      refine ⟨map_add _, fun c y => Subtype.ext ?_⟩
      change omMap (C.res h) a (toR C S c • (y : relOm K (C.I S) a).1) = toR C T c • omMap (C.res h) a (y : relOm K (C.I S) a).1
      rw [omMap_smul]
      exact congrArg (· • omMap (C.res h) a (y : relOm K (C.I S) a).1) (res_toR C h c)
    · intro S T h ω
      refine Subtype.ext ?_
      change omMap (C.res h) a (omMap (θ S) a (ω : Om K (R0 K n d S) a)) =
        omMap (θ T) a (omMap (incl (cone_mono h)) a (ω : Om K (R0 K n d S) a))
      have e2 : (C.res h).comp (θ S) = (θ T).comp (incl (cone_mono h)) := AlgHom.ext fun y => nat h y
      rw [omMap_comp, omMap_comp, e2]
  refine GlobalTheory.T.pm_exactness_of_exP P (GlobalTheory.T.exP_of_compatible_equiv _ _ (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) _
    (fun S => ((e S).symm.toAddEquiv : relA C S a ≃+ P.M S)) ?_ h2)
  intro S T h x
  apply (e T).injective
  refine Subtype.ext ?_
  have := he h ((e S).symm x)
  simp only [LinearEquiv.apply_symm_apply] at this
  have h3 := LinearEquiv.apply_symm_apply (e T) (relMap (C.res h) (res_mem_I C h) a x)
  exact (congrArg Subtype.val h3).trans this.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
