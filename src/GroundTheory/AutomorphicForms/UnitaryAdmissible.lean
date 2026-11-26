module

public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.KTypeExist
public import GroundTheory.AutomorphicForms.TensorProductTheorem.NonemptyAdelicDecomposition
public import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.UnitaryAdmissible.Scalar
namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open Module Set GKTensor

attribute [local instance 100] LieRing.ofAssociativeRing

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G}

section Scalar

variable [CompactSpace K] {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L] {V : Type*} [AddCommGroup V]
  [Module ℂ V]

theorem exists_eq_smul_one (Mx : GKLModule h K L V) (hirr : Mx.IsIrreducible)
    (T : Module.End ℂ V) (hρ : ∀ X, Mx.gk.ρ X * T = T * Mx.gk.ρ X)
    (hσ : ∀ k, Mx.gk.σ k * T = T * Mx.gk.σ k) (hτ : ∀ g, Mx.τ g * T = T * Mx.τ g)
    (hfin : ∀ v : V, ∃ F : Submodule ℂ V, FiniteDimensional ℂ F ∧ v ∈ F ∧ ∀ w ∈ F, T w ∈ F) :
    ∃ c : ℂ, T = c • 1 := by
  have : IsSimpleOrder (Subrepresentation Mx.fullRep) := hirr
  have hnt : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply (bot_ne_top : (⊥ : Subrepresentation Mx.fullRep) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext w
    simp [Subsingleton.elim w 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨F, hFd, hvF, hTF⟩ := hfin v
  set T' : Module.End ℂ F := T.restrict hTF
  have : Nontrivial F := ⟨⟨⟨v, hvF⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T'
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hcomm : ∀ p, Mx.fullRep p * T = T * Mx.fullRep p := by
    rintro ⟨a, g⟩
    show Mx.gk.rep a * Mx.τ g * T = T * (Mx.gk.rep a * Mx.τ g)
    rw [mul_assoc, hτ, ← mul_assoc, Mx.gk.rep_comm hρ hσ a, mul_assoc]
  let Y : Subrepresentation Mx.fullRep :=
    ⟨LinearMap.ker (T - c • 1), fun p x hx => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply] at hx ⊢
      have e := congrArg (fun f : Module.End ℂ V => f x) (hcomm p)
      simp only [Module.End.mul_apply] at e
      rw [← e, ← map_smul, ← map_sub, hx, map_zero]⟩
  have hwT : T (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
  rcases IsSimpleOrder.eq_bot_or_eq_top Y with hY | hY
  · exfalso
    have hmem : (w : V) ∈ Y.toSubmodule := by
      show (w : V) ∈ LinearMap.ker (T - c • 1)
      simp [hwT]
    rw [hY] at hmem
    exact hw0 hmem
  · refine ⟨c, LinearMap.ext fun x => ?_⟩
    have hmem : x ∈ Y.toSubmodule := by rw [hY]; trivial
    have hx : (T - c • 1) x = 0 := hmem
    simpa [sub_eq_zero] using hx

end Scalar

section Casimir

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]

noncomputable def casimirOp (M : h.GKModule K V) (b : Module.Basis ι ℝ h.lieSubalgebra) (ε : ι → ℝ) :
    Module.End ℂ V :=
  ∑ i, ε i • (M.ρ (b i) * M.ρ (b i))

theorem σ_mul_ρ (M : h.GKModule K V) (k : K) (Y : h.lieSubalgebra) :
    M.σ k * M.ρ Y = M.ρ (h.AdLie (k : G) Y) * M.σ k :=
  LinearMap.ext fun v => M.map_ρ k (h.ofLie Y) v

theorem AdLie_AdLie_inv (g : G) (Y : h.lieSubalgebra) : h.AdLie g (h.AdLie g⁻¹ Y) = Y := by
  show h.toLie (h.Ad g (h.Ad g⁻¹ (h.ofLie Y))) = Y
  have e := h.Ad_inv_Ad g⁻¹ (h.ofLie Y)
  rw [inv_inv] at e
  rw [e]
  rfl

theorem σ_mul_casimirOp [DecidableEq ι] (M : h.GKModule K V)
    {B : LinearMap.BilinForm ℝ h.lieSubalgebra} {b : Module.Basis ι ℝ h.lieSubalgebra} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y, B X Y = B Y X)
    (hAd : ∀ k : K, ∀ X Y, B (h.AdLie (k : G) X) (h.AdLie (k : G) Y) = B X Y) (k : K) :
    M.σ k * casimirOp M b ε = casimirOp M b ε * M.σ k := by
  set A := h.AdLie (k : G)
  set f : ι → h.lieSubalgebra := fun i => A (b i) with hf

  have hexp : ∀ Y, Y = ∑ i, (ε i * B Y (f i)) • f i := by
    intro Y
    have e := eq_sum_of_orthogonal hε horth (h.AdLie ((k : G)⁻¹) Y)
    have e2 := congrArg A e
    rw [AdLie_AdLie_inv] at e2
    conv_lhs => rw [e2]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 2
    rw [← hAd k (b i) (h.AdLie ((k : G)⁻¹) Y), AdLie_AdLie_inv, hsymm]

  have hsum : ∀ j l, ∑ i, ε i * B (b j) (f i) * B (b l) (f i) = B (b j) (b l) := by
    intro j l
    conv_rhs => rw [hexp (b l)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl]
    intro i _
    rw [map_smul, smul_eq_mul]
    ring

  have hρf : ∀ i, M.ρ (f i) = ∑ j, (ε j * B (b j) (f i)) • M.ρ (b j) := by
    intro i
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (f i)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  have hcas : ∑ i, ε i • (M.ρ (f i) * M.ρ (f i)) = casimirOp M b ε := by
    simp_rw [hρf, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    unfold casimirOp
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have e : ∀ l, ∑ i, (ε i * (ε j * B (b j) (f i) * (ε l * B (b l) (f i)))) •
        (M.ρ (b j) * M.ρ (b l)) = (if j = l then ε j else 0) • (M.ρ (b j) * M.ρ (b l)) := by
      intro l
      rw [← Finset.sum_smul]
      congr 1
      have := hsum j l
      rw [horth] at this
      calc ∑ i, ε i * (ε j * B (b j) (f i) * (ε l * B (b l) (f i)))
          = ε l * ε j * ∑ i, ε i * B (b j) (f i) * B (b l) (f i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = if j = l then ε j else 0 := by
            rw [this]
            split_ifs with hjl
            · subst hjl
              have := hε j
              linear_combination (ε j) * this
            · ring
    rw [Finset.sum_congr rfl fun l _ => e l]
    simp
  conv_rhs => rw [← hcas]
  unfold casimirOp
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, σ_mul_ρ, mul_assoc, σ_mul_ρ, ← mul_assoc]

end Casimir

section KType

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem ρ_mem_of_stable (M : h.GKModule K V) {F : Submodule ℂ V}
    (hF : ∀ k, ∀ v ∈ F, M.σ k v ∈ F) {Z : h.lieSubalgebra}
    (hZ : ∀ t : ℝ, h.expG (t • h.ofLie Z) ∈ K) {v : V} (hv : v ∈ F) : M.ρ Z v ∈ F := by
  by_contra hnot
  obtain ⟨ψ, hψ, hψF⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hd := M.hasDerivAt_coeff (h.ofLie Z) hZ ψ v
  have h0 : (fun t : ℝ => ψ (M.σ ⟨h.expG (t • h.ofLie Z), hZ t⟩ v)) = fun _ => 0 := by
    funext t
    have hm : ψ (M.σ ⟨_, hZ t⟩ v) ∈ F.map ψ := ⟨_, hF _ v hv, rfl⟩
    rw [hψF] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  rw [h0] at hd
  exact hψ (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

theorem map_ρ_of_equivariant (M : h.GKModule K V) {F : Submodule ℂ V}
    (hF : ∀ k, ∀ v ∈ F, M.σ k v ∈ F) (f : F →ₗ[ℂ] V)
    (hf : ∀ k (v : F), f ⟨M.σ k v, hF k v v.2⟩ = M.σ k (f v)) {Z : h.lieSubalgebra}
    (hZ : ∀ t : ℝ, h.expG (t • h.ofLie Z) ∈ K) (v : F) (hv : M.ρ Z v ∈ F) :
    f ⟨M.ρ Z v, hv⟩ = M.ρ Z (f v) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ψ
  rw [map_sub, sub_eq_zero]
  obtain ⟨ψ', hψ'⟩ := LinearMap.exists_extend (ψ ∘ₗ f)
  have e : ∀ w : F, ψ' w = ψ (f w) := fun w => congrArg (fun g => g w) hψ'
  have h1 := M.hasDerivAt_coeff (h.ofLie Z) hZ ψ' v
  have h2 := M.hasDerivAt_coeff (h.ofLie Z) hZ ψ (f v)
  have e2 : (fun t : ℝ => ψ' (M.σ ⟨h.expG (t • h.ofLie Z), hZ t⟩ v)) =
      fun t => ψ (M.σ ⟨h.expG (t • h.ofLie Z), hZ t⟩ (f v)) := by
    funext t
    rw [← hf ⟨h.expG (t • h.ofLie Z), hZ t⟩ v]
    exact e ⟨_, _⟩
  rw [e2] at h1
  have := h1.unique h2
  rw [← e ⟨_, hv⟩]
  exact this

def toSub (M : h.GKModule K V) (m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule) :
    Submodule ℂ V where
  carrier := {v | M.σ.asModuleEquiv.symm v ∈ m}
  add_mem' {x y} hx hy := by
    show M.σ.asModuleEquiv.symm (x + y) ∈ m
    rw [map_add (f := _)]
    exact m.add_mem hx hy
  zero_mem' := by
    show M.σ.asModuleEquiv.symm 0 ∈ m
    rw [map_zero]
    exact m.zero_mem
  smul_mem' c x hx := by
    show M.σ.asModuleEquiv.symm (c • x) ∈ m
    rw [Representation.asModuleEquiv_symm_map_smul]
    exact m.smul_mem _ hx

theorem mem_toSub (M : h.GKModule K V) {m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule} {v : V} :
    v ∈ toSub M m ↔ M.σ.asModuleEquiv.symm v ∈ m := Iff.rfl

theorem σ_mem_toSub (M : h.GKModule K V) (m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule) (k : K)
    {v : V} (hv : v ∈ toSub M m) : M.σ k v ∈ toSub M m := by
  rw [mem_toSub, Representation.asModuleEquiv_symm_map_rho]
  exact m.smul_mem _ hv

def ofStable (M : h.GKModule K V) (O : Submodule ℂ V) (hO : ∀ k, ∀ v ∈ O, M.σ k v ∈ O) :
    Submodule (MonoidAlgebra ℂ K) M.σ.asModule where
  carrier := {x | M.σ.asModuleEquiv x ∈ O}
  add_mem' {x y} hx hy := by
    show M.σ.asModuleEquiv (x + y) ∈ O
    rw [map_add (f := _)]
    exact O.add_mem hx hy
  zero_mem' := by
    show M.σ.asModuleEquiv 0 ∈ O
    rw [map_zero]
    exact O.zero_mem
  smul_mem' a x hx := by
    induction a using MonoidAlgebra.induction_on with
    | of k =>
      show M.σ.asModuleEquiv (MonoidAlgebra.of ℂ K k • x) ∈ O
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
      exact hO k _ hx
    | add a b ha hb =>
      rw [add_smul]
      show M.σ.asModuleEquiv (a • x + b • x) ∈ O
      rw [map_add (f := _)]
      exact O.add_mem ha hb
    | smul r a ha =>
      rw [smul_assoc]
      show M.σ.asModuleEquiv (r • (a • x)) ∈ O
      rw [map_smul]
      exact O.smul_mem r ha

theorem mem_ofStable (M : h.GKModule K V) (O : Submodule ℂ V) (hO : ∀ k, ∀ v ∈ O, M.σ k v ∈ O)
    {x : M.σ.asModule} : x ∈ ofStable M O hO ↔ M.σ.asModuleEquiv x ∈ O := Iff.rfl

theorem sumSq_mem_of_stable (M : h.GKModule K V) {ι : Type*} [Fintype ι]
    (Z : ι → h.lieSubalgebra) (hZ : ∀ i (t : ℝ), h.expG (t • h.ofLie (Z i)) ∈ K) {F : Submodule ℂ V}
    (hF : ∀ k, ∀ v ∈ F, M.σ k v ∈ F) {v : V} (hv : v ∈ F) :
    (∑ i, M.ρ (Z i) * M.ρ (Z i)) v ∈ F := by
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ =>
    ρ_mem_of_stable M hF (hZ i) (ρ_mem_of_stable M hF (hZ i) hv)

theorem aeval_eq_zero_of_equiv (M : h.GKModule K V) {ι : Type*} [Fintype ι]
    (Z : ι → h.lieSubalgebra) (hZ : ∀ i (t : ℝ), h.expG (t • h.ofLie (Z i)) ∈ K)
    {S m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule} (g : m ≃ₗ[MonoidAlgebra ℂ K] S)
    (q : Polynomial ℂ)
    (hq : ∀ v ∈ toSub M S, Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q v = 0)
    {x : M.σ.asModule} (hx : x ∈ m) :
    Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q (M.σ.asModuleEquiv x) = 0 := by
  have hFs : ∀ k, ∀ v ∈ toSub M S, M.σ k v ∈ toSub M S := fun k v hv => σ_mem_toSub M S k hv
  have hCF : ∀ v ∈ toSub M S, (∑ i, M.ρ (Z i) * M.ρ (Z i)) v ∈ toSub M S :=
    fun v hv => sumSq_mem_of_stable M Z hZ hFs hv
  let fm : toSub M S →ₗ[ℂ] V :=
    { toFun := fun w => M.σ.asModuleEquiv (g.symm ⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ : m)
      map_add' := fun w w' => by
        have e : (⟨M.σ.asModuleEquiv.symm ((w + w' : toSub M S) : V), (w + w').2⟩ : S) =
            ⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ + ⟨M.σ.asModuleEquiv.symm (w' : V), w'.2⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e, map_add (f := _), Submodule.coe_add, map_add (f := _)]
      map_smul' := fun a w => by
        have e : (⟨M.σ.asModuleEquiv.symm ((a • w : toSub M S) : V), (a • w).2⟩ : S) =
            a • (⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ : S) :=
          Subtype.ext (map_smul _ _ _)
        have e2 : g.symm (a • (⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ : S)) =
            a • g.symm ⟨M.σ.asModuleEquiv.symm (w : V), w.2⟩ := by
          rw [← algebraMap_smul (MonoidAlgebra ℂ K) a, map_smul, algebraMap_smul]
        rw [e, e2, Submodule.coe_smul_of_tower, map_smul]
        rfl }
  have hfm : ∀ k (v : toSub M S), fm ⟨M.σ k v, hFs k v v.2⟩ = M.σ k (fm v) := by
    intro k v
    have e : (⟨M.σ.asModuleEquiv.symm (M.σ k v), hFs k v v.2⟩ : S) =
        MonoidAlgebra.of ℂ K k • (⟨M.σ.asModuleEquiv.symm (v : V), v.2⟩ : S) :=
      Subtype.ext (by rw [Submodule.coe_smul]; exact Representation.asModuleEquiv_symm_map_rho _ _ _)
    show M.σ.asModuleEquiv (g.symm ⟨M.σ.asModuleEquiv.symm (M.σ k v), _⟩ : m) = _
    rw [e, map_smul, Submodule.coe_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
    rfl
  set A : Module.End ℂ (toSub M S) := LinearMap.restrict _ hCF with hA
  have hAC : ∀ w : toSub M S, fm (A w) = (∑ i, M.ρ (Z i) * M.ρ (Z i)) (fm w) := by
    intro w
    have e : A w = ∑ i, (⟨M.ρ (Z i) (M.ρ (Z i) w),
        ρ_mem_of_stable M hFs (hZ i) (ρ_mem_of_stable M hFs (hZ i) w.2)⟩ : toSub M S) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      show (∑ i, M.ρ (Z i) * M.ρ (Z i)) (w : V) = _
      rw [LinearMap.sum_apply]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.End.mul_apply]
    rw [map_ρ_of_equivariant M hFs fm hfm (hZ i) ⟨_, ρ_mem_of_stable M hFs (hZ i) w.2⟩,
      map_ρ_of_equivariant M hFs fm hfm (hZ i) w]
  have hAsub : ∀ w : toSub M S, ((Polynomial.aeval A q w : toSub M S) : V) =
      Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q (w : V) :=
    AutomorphicForm.map_aeval_apply_of_intertwine (toSub M S).subtype (fun _ => rfl) q
  set y : S := g ⟨x, hx⟩ with hy
  have hyF : M.σ.asModuleEquiv (y : M.σ.asModule) ∈ toSub M S := by
    rw [mem_toSub, LinearEquiv.symm_apply_apply]
    exact y.2
  have hfy : fm ⟨_, hyF⟩ = M.σ.asModuleEquiv x := by
    show M.σ.asModuleEquiv (g.symm ⟨M.σ.asModuleEquiv.symm
      (M.σ.asModuleEquiv (y : M.σ.asModule)), _⟩ : m) = _
    have e : (⟨M.σ.asModuleEquiv.symm (M.σ.asModuleEquiv (y : M.σ.asModule)), hyF⟩ : S) = y :=
      Subtype.ext (LinearEquiv.symm_apply_apply _ _)
    rw [e, hy, LinearEquiv.symm_apply_apply]
  have h0 : Polynomial.aeval A q ⟨_, hyF⟩ = 0 :=
    Subtype.ext ((hAsub _).trans (hq _ hyF))
  have h3 := AutomorphicForm.map_aeval_apply_of_intertwine fm hAC q ⟨_, hyF⟩
  rw [h0, map_zero, hfy] at h3
  exact h3.symm

theorem finiteDimensional_toSub_of_isSimpleModule (M : h.GKModule K V)
    {S : Submodule (MonoidAlgebra ℂ K) M.σ.asModule} (hS : IsSimpleModule (MonoidAlgebra ℂ K) S) :
    FiniteDimensional ℂ (toSub M S) ∧ Nontrivial (toSub M S) := by
  have hSnt : Nontrivial S := IsSimpleModule.nontrivial (MonoidAlgebra ℂ K) S
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  set O := Submodule.span ℂ (range fun k : K => M.σ k (M.σ.asModuleEquiv (s₀ : M.σ.asModule)))
    with hOdef
  have hOfin : FiniteDimensional ℂ O := M.locallyFinite _
  have hOs : ∀ k, ∀ v ∈ O, M.σ k v ∈ O := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨k * k', rfl⟩
    | zero => rw [map_zero]; exact O.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact O.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact O.smul_mem a hx
  have hs₀O : M.σ.asModuleEquiv (s₀ : M.σ.asModule) ∈ O :=
    Submodule.subset_span ⟨1, show M.σ 1 _ = _ by rw [map_one, Module.End.one_apply]⟩
  have hatom : IsAtom S := (isSimpleModule_iff_isAtom).1 hS
  have hSN : S ≤ ofStable M O hOs := by
    rcases hatom.le_iff.1 (inf_le_right : ofStable M O hOs ⊓ S ≤ S) with h0 | h1
    · exfalso
      have hmem : (s₀ : M.σ.asModule) ∈ ofStable M O hOs ⊓ S := ⟨hs₀O, s₀.2⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact hs₀ (Subtype.ext hmem)
    · rw [← h1]
      exact inf_le_left
  have hFO : toSub M S ≤ O := fun v hv => by
    exact (mem_ofStable M O hOs).1 (hSN hv)
  refine ⟨Submodule.finiteDimensional_of_le hFO, ?_⟩
  have hs₀F : M.σ.asModuleEquiv (s₀ : M.σ.asModule) ∈ toSub M S := by
    rw [mem_toSub, LinearEquiv.symm_apply_apply]
    exact s₀.2
  refine ⟨⟨⟨_, hs₀F⟩, 0, fun he => hs₀ ?_⟩⟩
  have h0 : M.σ.asModuleEquiv (s₀ : M.σ.asModule) = 0 := congrArg Subtype.val he
  apply Subtype.ext
  rw [Submodule.coe_zero]
  exact M.σ.asModuleEquiv.injective (h0.trans (map_zero _).symm)

theorem exists_aeval_eq_zero_of_mem_isotypic (M : h.GKModule K V) {ι : Type*} [Fintype ι]
    (Z : ι → h.lieSubalgebra) (hZ : ∀ i (t : ℝ), h.expG (t • h.ofLie (Z i)) ∈ K)
    {c : Submodule (MonoidAlgebra ℂ K) M.σ.asModule}
    (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) M.σ.asModule) :
    ∃ q : Polynomial ℂ, q.Monic ∧ 0 < q.natDegree ∧
      ∀ v : V, M.σ.asModuleEquiv.symm v ∈ c →
        Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) q v = 0 := by
  obtain ⟨S, hS, rfl⟩ := hc
  obtain ⟨hFfin, hFnt⟩ := finiteDimensional_toSub_of_isSimpleModule M hS
  have hFs : ∀ k, ∀ v ∈ toSub M S, M.σ k v ∈ toSub M S := fun k v hv => σ_mem_toSub M S k hv
  have hCF : ∀ v ∈ toSub M S, (∑ i, M.ρ (Z i) * M.ρ (Z i)) v ∈ toSub M S :=
    fun v hv => sumSq_mem_of_stable M Z hZ hFs hv
  let A : Module.End ℂ (toSub M S) := LinearMap.restrict _ hCF
  refine ⟨A.charpoly, LinearMap.charpoly_monic A, ?_, ?_⟩
  · rw [LinearMap.charpoly_natDegree]
    exact Module.finrank_pos
  have hvanF : ∀ v ∈ toSub M S, Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) A.charpoly v = 0 := by
    intro v hv
    have := AutomorphicForm.map_aeval_apply_of_intertwine (toSub M S).subtype (A := A)
      (B := ∑ i, M.ρ (Z i) * M.ρ (Z i)) (fun _ => rfl) A.charpoly ⟨v, hv⟩
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at this
    exact this.symm
  intro v hv
  have hv' : M.σ.asModuleEquiv.symm v ∈ ⨆ m : {m : Submodule (MonoidAlgebra ℂ K) M.σ.asModule |
      Nonempty (m ≃ₗ[MonoidAlgebra ℂ K] S)}, m.1 := by
    rw [← sSup_eq_iSup']
    exact hv
  have key := Submodule.iSup_induction _ (motive := fun x =>
    Polynomial.aeval (∑ i, M.ρ (Z i) * M.ρ (Z i)) A.charpoly (M.σ.asModuleEquiv x) = 0) hv'
    (fun m x hx => aeval_eq_zero_of_equiv M Z hZ m.2.some A.charpoly hvanF hx)
    (by rw [map_zero, map_zero])
    (fun x y hx hy => by rw [map_add (f := _), map_add (f := _), hx, hy, add_zero])
  rwa [LinearEquiv.apply_symm_apply] at key

end KType

end UnitaryAdmissible

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspScalar
namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open AutomorphicForm Module Set

attribute [local instance 100] LieRing.ofAssociativeRing

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable (U : Submodule ℂ (cuspForms K n))
  (hρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U) (hσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
  (hτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U)


include hρ in
theorem uActionCusp_mem (u : UEnv K n) {φ : cuspForms K n}
    (hφ : φ ∈ U) : uActionCusp K n u φ ∈ U := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ _ t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ _) u
  induction t using TensorAlgebra.induction generalizing φ with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact Submodule.smul_of_tower_mem _ r hφ
  | ι X => exact hρ X φ hφ
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact ha (hb hφ)
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]
    exact U.add_mem (ha hφ) (hb hφ)

theorem archTraceForm_AdLie (g : archGroup K n) (X Y : (isExpLieAlgebra K n).lieSubalgebra) :
    archTraceForm K n ((isExpLieAlgebra K n).AdLie g X) ((isExpLieAlgebra K n).AdLie g Y) =
      archTraceForm K n X Y := by
  rw [archTraceForm_apply, archTraceForm_apply]
  congr 1
  have hgi : (((g⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) *
      (((g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hgi' : mat (((g⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) *
      mat (((g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) = 1 := by
    exact hgi
  set A := mat (((g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  set C := mat (((g⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)
  change Matrix.trace (A * mat (X : ArchMatrix K n) * C * (A * mat (Y : ArchMatrix K n) * C)) =
    Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))
  have e : A * mat (X : ArchMatrix K n) * C * (A * mat (Y : ArchMatrix K n) * C) =
      A * (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n)) * C := by
    rw [show A * mat (X : ArchMatrix K n) * C * (A * mat (Y : ArchMatrix K n) * C) =
      A * mat (X : ArchMatrix K n) * (C * A) * mat (Y : ArchMatrix K n) * C by
        simp only [Matrix.mul_assoc], hgi', Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hgi', Matrix.one_mul]

theorem exists_uActionCusp_eq_smul (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible) (u : UEnv K n)
    (hu : u ∈ (isExpLieAlgebra K n).centerU)
    (hcomm : ∀ k φ, archCompactRepCusp K n k (uActionCusp K n u φ) =
      uActionCusp K n u (archCompactRepCusp K n k φ)) :
    ∃ c : ℂ, ∀ φ ∈ U, uActionCusp K n u φ = c • φ := by
  set T : Module.End ℂ U := (uActionCusp K n u).restrict fun φ hφ => uActionCusp_mem U hρ u hφ
  obtain ⟨c, hc⟩ := exists_eq_smul_one (cuspSubmodule K n U hρ hσ hτ) hirr T
    (fun X => LinearMap.ext fun φ => Subtype.ext (by
      show uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ X) (uActionCusp K n u φ) =
        uActionCusp K n u (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ X) φ)
      rw [← Module.End.mul_apply, ← map_mul, Subalgebra.mem_center_iff.1 hu, map_mul,
        Module.End.mul_apply]))
    (fun k => LinearMap.ext fun φ => Subtype.ext (hcomm k φ))
    (fun g => LinearMap.ext fun φ => Subtype.ext (by
      show finRepCusp K n g (uActionCusp K n u φ) = uActionCusp K n u (finRepCusp K n g φ)
      rw [uActionCusp_finRepCusp]))
    (fun v => by
      set S₀ := Submodule.span ℂ ((fun z => uActionCusp K n z (v : cuspForms K n)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) with hS₀
      have hle : cuspForms K n ≤ archSmooth K n :=
        cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth
      have hinc : Function.Injective (Submodule.inclusion hle) :=
        Submodule.inclusion_injective _
      have hS₀fin : FiniteDimensional ℂ S₀ := by
        have hZ := (v : cuspForms K n).2.1.isZFinite
        have e : S₀.map (Submodule.inclusion hle) =
            Submodule.span ℂ ((fun z => uAction z (⟨(v : cuspForms K n), (v : cuspForms K n).2.1.isSmooth.1⟩ :
              archSmooth K n)) ''
              ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := by
          rw [hS₀, Submodule.map_span, Set.image_image]
          rfl
        have : FiniteDimensional ℂ (S₀.map (Submodule.inclusion hle)) := by
          rw [e]; exact hZ
        exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hinc S₀).symm
      refine ⟨S₀.comap U.subtype, ?_, ?_, ?_⟩
      · have h1 : (S₀.comap U.subtype).map U.subtype ≤ S₀ :=
          Submodule.map_comap_le _ _
        have : FiniteDimensional ℂ ((S₀.comap U.subtype).map U.subtype) :=
          Submodule.finiteDimensional_of_le h1
        exact Module.Finite.equiv
          (Submodule.equivMapOfInjective _ U.injective_subtype _).symm
      · show (v : cuspForms K n) ∈ S₀
        refine Submodule.subset_span ⟨1, Subalgebra.one_mem _, ?_⟩
        show uActionCusp K n 1 (v : cuspForms K n) = v
        rw [map_one, Module.End.one_apply]
      · have key : ∀ x ∈ S₀, uActionCusp K n u x ∈ S₀ := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨z, hz, rfl⟩ := hx
            refine Submodule.subset_span ⟨u * z, Subalgebra.mul_mem _ hu hz, ?_⟩
            show uActionCusp K n (u * z) (v : cuspForms K n) = _
            rw [map_mul, Module.End.mul_apply]
          | zero => rw [map_zero]; exact S₀.zero_mem
          | add x y _ _ hx hy => rw [map_add (f := _)]; exact S₀.add_mem hx hy
          | smul a x _ hx => rw [map_smul]; exact S₀.smul_mem a hx
        intro w hw
        exact key _ hw)
  refine ⟨c, fun φ hφ => ?_⟩
  have := congrArg (fun f : Module.End ℂ U => ((f ⟨φ, hφ⟩ : U) : cuspForms K n)) hc
  simpa [T] using this

theorem casimirOp_gkModuleCusp {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : ι → ℝ) :
    casimirOp (gkModuleCusp K n) b ε = uActionCusp K n (casimir b ε) := by
  unfold casimirOp casimir
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul]
  rfl

theorem exists_casimir_eq_smul (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : ι → ℝ)
    (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, archTraceForm K n (b i) (b j) = if i = j then ε i else 0) :
    ∃ c : ℂ, ∀ φ ∈ U, uActionCusp K n (casimir b ε) φ = c • φ := by
  refine exists_uActionCusp_eq_smul U hρ hσ hτ hirr _
    (casimir_mem_center hε horth archTraceForm_symm archTraceForm_lie) fun k φ => ?_
  have := σ_mul_casimirOp (gkModuleCusp K n) hε horth archTraceForm_symm
    (fun k X Y => archTraceForm_AdLie (k : archGroup K n) X Y) k
  rw [casimirOp_gkModuleCusp] at this
  exact congrArg (fun f : Module.End ℂ (cuspForms K n) => f φ) this

theorem exists_lieActionCusp_eq_smul (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible)
    (Z₀ : (isExpLieAlgebra K n).lieSubalgebra)
    (hZ : ∀ X : (isExpLieAlgebra K n).lieSubalgebra, ⁅Z₀, X⁆ = 0)
    (hAd : ∀ g : archGroup K n, (isExpLieAlgebra K n).Ad g ((isExpLieAlgebra K n).ofLie Z₀) =
      (isExpLieAlgebra K n).ofLie Z₀) :
    ∃ c : ℂ, ∀ φ ∈ U, lieActionCusp K n Z₀ φ = c • φ := by
  refine exists_uActionCusp_eq_smul U hρ hσ hτ hirr (UniversalEnvelopingAlgebra.ι ℝ Z₀)
    (mem_center_of_forall_ι_commute fun X => ?_) fun k φ => ?_
  · have e : ⁅UniversalEnvelopingAlgebra.ι ℝ X, UniversalEnvelopingAlgebra.ι ℝ Z₀⁆ = 0 := by
      rw [← LieHom.map_lie, ← lie_skew, hZ, neg_zero, map_zero]
    rw [Ring.lie_def, sub_eq_zero] at e
    exact e
  · have := (gkModuleCusp K n).map_ρ k ((isExpLieAlgebra K n).ofLie Z₀) φ
    rw [hAd] at this
    exact this

noncomputable def lapZ {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (ε : Fin d → ℝ) (i : Fin d) : (isExpLieAlgebra K n).lieSubalgebra :=
  Real.sqrt (1 - ε i) • b i

theorem lapZ_mem {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (ε : Fin d → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n)
    (i : Fin d) (t : ℝ) :
    (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (lapZ b ε i)) ∈ archCompact K n := by
  rcases hε i with e | e
  · have h0 : lapZ b ε i = 0 := by simp [lapZ, e]
    rw [h0]
    have : (isExpLieAlgebra K n).ofLie (0 : (isExpLieAlgebra K n).lieSubalgebra) = 0 := rfl
    rw [this, smul_zero, IsExpLieAlgebra.expG_zero]
    exact (archCompact K n).one_mem
  · have := hK i e (t * Real.sqrt (1 - ε i))
    convert this using 2
    rw [mul_smul]
    rfl

theorem aeval_apply_eq_of_eqOn {V : Type*} [AddCommGroup V] [Module ℂ V] (A B : Module.End ℂ V)
    (W : Submodule ℂ V) (hA : ∀ w ∈ W, A w ∈ W) (hAB : ∀ w ∈ W, A w = B w) (q : Polynomial ℂ)
    {w : V} (hw : w ∈ W) : Polynomial.aeval A q w = Polynomial.aeval B q w := by
  have h1 := AutomorphicForm.map_aeval_apply_of_intertwine W.subtype (A := A.restrict hA) (B := A)
    (fun _ => rfl) q ⟨w, hw⟩
  have h2 := AutomorphicForm.map_aeval_apply_of_intertwine W.subtype (A := A.restrict hA) (B := B)
    (fun x => hAB x x.2) q ⟨w, hw⟩
  exact h1.symm.trans h2

theorem aeval_laplacian_eq_zero {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (ω : ℂ) (hω : ∀ φ ∈ U, uActionCusp K n (casimir b ε) φ = ω • φ) (q : Polynomial ℂ) {φ : U}
    (hq : Polynomial.aeval (∑ i, (cuspSubmodule K n U hρ hσ hτ).gk.ρ (lapZ b ε i) *
      (cuspSubmodule K n U hρ hσ hτ).gk.ρ (lapZ b ε i)) q φ = 0) :
    Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (q.comp (Polynomial.X - Polynomial.C ω))
      (φ : cuspForms K n) = 0 := by
  set M := (cuspSubmodule K n U hρ hσ hτ).gk
  set L := uActionCusp K n (laplacianU K n b)
  set B : Module.End ℂ (cuspForms K n) := ∑ i,
    uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (lapZ b ε i)) *
      uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (lapZ b ε i))
  have hsq : ∀ i, (1 - ε i) = Real.sqrt (1 - ε i) * Real.sqrt (1 - ε i) := fun i =>
    (Real.mul_self_sqrt (by rcases hε i with e | e <;> rw [e] <;> norm_num)).symm
  have hAB : ∀ ψ ∈ U, (L - ω • 1) ψ = B ψ := by
    intro ψ hψ
    have e1 : L ψ = ω • ψ + ∑ i, (1 - ε i) • uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (b i))
          (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ (b i)) ψ) := by
      show uActionCusp K n (laplacianU K n b) ψ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [laplacianU_eq_casimir_add b ε, map_add (f := _), LinearMap.add_apply, hω _ hψ, map_sum,
        LinearMap.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_mul, LinearMap.smul_apply, Module.End.mul_apply]
    rw [LinearMap.sub_apply, e1, LinearMap.smul_apply, Module.End.one_apply, add_sub_cancel_left,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.End.mul_apply]
    simp only [lapZ, map_smul, LinearMap.smul_apply]
    rw [LinearMap.map_smul_of_tower, smul_smul, ← hsq]
  have hAU : ∀ ψ ∈ U, (L - ω • 1) ψ ∈ U := by
    intro ψ hψ
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact U.sub_mem (uActionCusp_mem U hρ _ hψ) (U.smul_mem ω hψ)
  rw [Polynomial.aeval_comp]
  have e2 : Polynomial.aeval L (Polynomial.X - Polynomial.C ω) = L - ω • 1 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  rw [e2, aeval_apply_eq_of_eqOn (L - ω • 1) B U hAU hAB q φ.2]
  have h3 := AutomorphicForm.map_aeval_apply_of_intertwine U.subtype
    (A := ∑ i, M.ρ (lapZ b ε i) * M.ρ (lapZ b ε i)) (B := B) (fun x => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [B, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      rfl) q φ
  rw [Submodule.subtype_apply, Submodule.subtype_apply, hq] at h3
  exact h3.symm.trans rfl

end UnitaryAdmissible

end GroundTheory.Automorphic
end

namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open AutomorphicForm Module Set GKTensor CompactRep

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem finiteDimensional_of_map_subtype_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    {U : Submodule ℂ V} (R : Submodule ℂ U) {S : Submodule ℂ V} [FiniteDimensional ℂ S]
    (h : R.map U.subtype ≤ S) : FiniteDimensional ℂ R := by
  have : FiniteDimensional ℂ (R.map U.subtype) := Submodule.finiteDimensional_of_le h
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ U.injective_subtype R).symm

theorem isAdmissible_cuspSubmodule (U : Submodule ℂ (cuspForms K n))
    (hρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U) (hσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
    (hτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U)
    (hirr : (cuspSubmodule K n U hρ hσ hτ).IsIrreducible) :
    (cuspSubmodule K n U hρ hσ hτ).IsAdmissible := by
  set Mx := cuspSubmodule K n U hρ hσ hτ with hMx

  refine ⟨fun v => ?_, fun H hHc hHo c hc => ?_⟩
  · obtain ⟨W, -, hW⟩ := AutomorphicForm.exists_openSubgroup_rightInvariant
      (v : cuspForms K n).2.1.isSmooth (v : cuspForms K n).2.1.isKFinite
    refine Subgroup.isOpen_mono (H₁ := W.toSubgroup) (fun u hu => ?_) W.isOpen
    show Mx.τ u v = v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hW g u hu

  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := K) (n := n)
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n := by
    intro i hi t
    refine expG_mem_archCompact_of_skew _ ?_
    have h := hskew i hi
    rw [mem_archSkew] at h
    show Matrix.conjTranspose (t • mat (b i : ArchMatrix K n)) = -(t • mat (b i : ArchMatrix K n))
    rw [Matrix.conjTranspose_smul, star_trivial, h, smul_neg]

  obtain ⟨ω, hω⟩ := exists_casimir_eq_smul U hρ hσ hτ hirr b ε hε2 horth
  obtain ⟨lam, hlam⟩ := exists_lieActionCusp_eq_smul U hρ hσ hτ hirr (centralZ K n) lie_centralZ
    Ad_centralZ

  obtain ⟨q, hqm, hqd, hq⟩ :=
    exists_aeval_eq_zero_of_mem_isotypic Mx.gk (lapZ b ε) (lapZ_mem b ε hε hK) hc
  set P := q.comp (Polynomial.X - Polynomial.C ω) with hP
  have hPm : P.Monic :=
    hqm.comp (Polynomial.monic_X_sub_C ω) (by rw [Polynomial.natDegree_X_sub_C]; exact one_ne_zero)
  have hPd : 0 < P.natDegree := by
    rw [hP, Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
    exact hqd

  set U₀ : Subgroup (AdelicGLn.integralFiniteGL K n) :=
    H.comap (AdelicGLn.integralFiniteGL K n).subtype with hU₀
  have hU₀o : IsOpen (U₀ : Set (AdelicGLn.integralFiniteGL K n)) :=
    hHo.preimage continuous_subtype_val

  set S : Submodule ℂ (cuspForms K n) :=
    LinearMap.ker (Polynomial.aeval (uActionCusp K n (laplacianU K n b)) P) ⊓
      LinearMap.ker (lieActionCusp K n (centralZ K n) - lam • 1) ⊓
        ⨅ u ∈ U₀, LinearMap.ker (finRepCusp K n (u : AdelicGLn.FiniteAdelicGL K n) - 1) with hS
  have hSfin : FiniteDimensional ℂ S := by
    refine finiteDimensional_of_eigen b P hPm hPd lam U₀ hU₀o S fun φ hφ => ?_
    rw [hS, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf] at hφ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hφ
    refine ⟨h1, ?_, fun u hu => ?_⟩
    · have := LinearMap.mem_ker.1 h2
      rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
    · have := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (h3 u) hu)
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this

  refine finiteDimensional_of_map_subtype_le _ (S := S) ?_
  rintro _ ⟨v, ⟨w, rfl⟩, rfl⟩
  have hvc : (kProj Mx.gk.isKFinite hc (w : U) : Mx.gk.σ.asModule) ∈ c :=
    kProj_mem_component Mx.gk.isKFinite hc _
  rw [hS, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨⟨?_, ?_⟩, fun u => (Submodule.mem_iInf _).2 fun hu => ?_⟩
  · exact aeval_laplacian_eq_zero U hρ hσ hτ b ε hε ω hω q (hq _ hvc)
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
    exact hlam _ (kProj Mx.gk.isKFinite hc (w : U)).2
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hcomm : ∀ k, Mx.τ (u : AdelicGLn.FiniteAdelicGL K n) * Mx.gk.σ k =
        Mx.gk.σ k * Mx.τ (u : AdelicGLn.FiniteAdelicGL K n) := fun k => (Mx.comm_σ k _).symm
    have hfix : Mx.τ (u : AdelicGLn.FiniteAdelicGL K n) (kProj Mx.gk.isKFinite hc (w : U)) =
        kProj Mx.gk.isKFinite hc (w : U) := by
      rw [← kProj_comm Mx.gk.isKFinite hc hcomm]
      congr 1
      exact w.2 _ hu
    exact congrArg Subtype.val hfix

end UnitaryAdmissible

end GroundTheory.Automorphic
