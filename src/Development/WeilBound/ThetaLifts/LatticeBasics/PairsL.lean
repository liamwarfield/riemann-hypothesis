module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.PairsD
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dens

open Polynomial Cardinal

section Schur

variable {R V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V] [Module R V]
  [IsScalarTower ℂ R V] [IsSimpleModule R V]

theorem exists_eq_algebraMap_of_aeval_eq_zero (φ : Module.End R V) {p : ℂ[X]} (hp : p ≠ 0)
    (hφ : aeval φ p = 0) : ∃ c : ℂ, φ = algebraMap ℂ (Module.End R V) c := by
  induction hn : p.natDegree generalizing p with
  | zero =>
    exfalso
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have hc : c ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hnt : Nontrivial V := IsSimpleModule.nontrivial R V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    rw [aeval_C] at hφ
    have h3 := LinearMap.congr_fun hφ v
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply] at h3
    exact hv ((smul_eq_zero.mp h3).resolve_left hc)
  | succ n ih =>
    have hdeg : p.degree ≠ 0 := by
      intro h
      rw [Polynomial.degree_eq_natDegree hp] at h
      norm_cast at h
      omega
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
    have hpq : p = (X - C a) * (p /ₘ (X - C a)) := (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm
    have hq0 : p /ₘ (X - C a) ≠ 0 := by
      intro h
      apply hp
      rw [hpq, h, mul_zero]
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      have h3 := congrArg Polynomial.natDegree hpq
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0, Polynomial.natDegree_X_sub_C] at h3
      omega
    rw [hpq, map_mul, map_sub, aeval_X, aeval_C] at hφ
    rcases LinearMap.injective_or_eq_zero (φ - algebraMap ℂ (Module.End R V) a) with hinj | h0
    · apply ih hq0 _ hqdeg
      ext v
      apply hinj
      rw [LinearMap.zero_apply, map_zero]
      exact LinearMap.congr_fun hφ v
    · exact ⟨a, sub_eq_zero.mp h0⟩

theorem exists_smul_of_rank_le_aleph0 (hV : Module.rank ℂ V ≤ ℵ₀) (φ : Module.End R V) :
    ∃ c : ℂ, ∀ m, φ m = c • m := by
  classical
  by_contra hne
  push Not at hne
  have hnt : Nontrivial V := IsSimpleModule.nontrivial R V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0 := by
    intro p hp h0
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_aeval_eq_zero φ hp h0
    obtain ⟨m, hm⟩ := hne c
    exact hm (by rw [hc, Module.algebraMap_end_apply])
  have hv0 : ∀ p : ℂ[X], aeval φ p v = 0 → p = 0 := by
    intro p hpv
    by_contra hp
    rcases LinearMap.injective_or_eq_zero (aeval φ p) with hinj | h0
    · exact hv (hinj (by rw [hpv, map_zero]))
    · exact htr p hp h0
  have hsurj : ∀ a : ℂ, Function.Surjective (aeval φ (X - C a)) := by
    intro a
    rcases LinearMap.bijective_or_eq_zero (aeval φ (X - C a)) with hb | h0
    · exact hb.2
    · exact absurd h0 (htr _ (Polynomial.X_sub_C_ne_zero a))
  choose w hw using fun a => hsurj a v
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have key : ∀ k ∈ s, aeval φ (∏ j ∈ s, (X - C j)) (w k) = aeval φ (∏ j ∈ s.erase k, (X - C j)) v := by
      intro k hk
      rw [← Finset.prod_erase_mul _ _ hk, map_mul, Module.End.mul_apply, hw]
    have h3 := congrArg (aeval φ (∏ j ∈ s, (X - C j))) hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h3
    simp only [LinearMap.map_smul_of_tower] at h3
    rw [Finset.sum_congr rfl (fun k hk => by rw [key k hk])] at h3
    have h4 : aeval φ (∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j)) v = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h3, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
    have hP := hv0 _ h4
    have h5 := congrArg (Polynomial.eval i) hP
    have hz : ∀ k ∈ s.erase i, Polynomial.eval i (C (g k) * ∏ j ∈ s.erase k, (X - C j)) = 0 := by
      intro k hk
      have hki := Finset.ne_of_mem_erase hk
      have him : i ∈ s.erase k := Finset.mem_erase_of_ne_of_mem (Ne.symm hki) hi
      rw [Polynomial.eval_mul, Polynomial.eval_prod, Finset.prod_eq_zero him (by simp), mul_zero]
    rw [Polynomial.eval_finsetSum, ← Finset.sum_erase_add _ _ hi, Finset.sum_eq_zero hz, zero_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_zero] at h5
    have hne2 : ∏ j ∈ s.erase i, Polynomial.eval i (X - C j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    exact (mul_eq_zero.mp h5).resolve_right hne2
  have hc := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at hc
  exact absurd (hc.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)

end Schur

theorem exists_mem_adjoin_eq {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (O : Set (Module.End ℂ V)) (hV : Module.rank ℂ V ≤ ℵ₀)
    (hirr : ∀ N : Submodule ℂ V, (∀ T ∈ O, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ T ∈ Algebra.adjoin ℂ O, ∀ x ∈ s, T x = f x := by
  classical
  let A := Algebra.adjoin ℂ O
  haveI : IsSimpleOrder (Submodule A V) := by
    refine ⟨fun N => ?_⟩
    have hst : ∀ T ∈ O, ∀ x ∈ N.restrictScalars ℂ, T x ∈ N.restrictScalars ℂ := by
      intro T hT x hx
      exact N.smul_mem (⟨T, Algebra.subset_adjoin hT⟩ : A) hx
    rcases hirr (N.restrictScalars ℂ) hst with h | h
    · left
      rw [← Submodule.restrictScalars_eq_bot_iff ℂ]
      exact h
    · right
      rw [← Submodule.restrictScalars_eq_top_iff ℂ]
      exact h
  haveI : IsSimpleModule A V := ⟨⟩
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun ψ x => by
        obtain ⟨c, hc⟩ := exists_smul_of_rank_le_aleph0 (R := A) hV ψ
        show f (ψ x) = ψ (f x)
        rw [hc, hc, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun x hx => (hr x hx).symm⟩

theorem exists_tmul_mem {α : Type} [Finite α] [DecidableEq α] {A : Type} [AddCommGroup A]
    [Module ℂ A] {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (O : ∀ i, Set (Module.End ℂ (X i))) (hrank : ∀ i, Module.rank ℂ (X i) ≤ Cardinal.aleph0)
    (hnt : ∀ i, Nontrivial (X i))
    (hirr : ∀ i (N : Submodule ℂ (X i)), (∀ T ∈ O i, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (N : Submodule ℂ (A ⊗[ℂ] PiTensorProduct ℂ X))
    (hN : ∀ i, ∀ T ∈ O i, ∀ x ∈ N, LinearMap.lTensor A (PiTensorProduct.map
      (Function.update (fun j => (LinearMap.id : X j →ₗ[ℂ] X j)) i T)) x ∈ N)
    (x : A ⊗[ℂ] PiTensorProduct ℂ X) (hxN : x ∈ N) (hx0 : x ≠ 0) :
    ∃ a₀ : A, a₀ ≠ 0 ∧ ∀ y, a₀ ⊗ₜ[ℂ] y ∈ N := by
  classical
  cases nonempty_fintype α
  have hcomp : ∀ (f g : ∀ a, X a →ₗ[ℂ] X a) (y : A ⊗[ℂ] PiTensorProduct ℂ X),
      LinearMap.lTensor A (PiTensorProduct.map fun a => f a ∘ₗ g a) y =
        LinearMap.lTensor A (PiTensorProduct.map f) (LinearMap.lTensor A (PiTensorProduct.map g) y) := by
    intro f g y
    rw [PiTensorProduct.map_comp, LinearMap.lTensor_comp_apply]
  let Asub : ∀ a, Subalgebra ℂ (Module.End ℂ (X a)) := fun i =>
    { carrier := {T | ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map
        (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) i T)) y ∈ N}
      mul_mem' := fun {a b} ha hb y hy => by
        have := ha _ (hb y hy)
        rw [← hcomp] at this
        convert this using 4
        funext ρ
        by_cases hρ : ρ = i
        · subst hρ; simp [Module.End.mul_eq_comp]
        · simp [Function.update_of_ne hρ]
      add_mem' := fun {a b} ha hb y hy => by
        rw [PiTensorProduct.map_update_add, LinearMap.lTensor_add]
        exact N.add_mem (ha y hy) (hb y hy)
      algebraMap_mem' := fun c y hy => by
        rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul, LinearMap.lTensor_smul]
        have : Function.update (fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)) i (1 : Module.End ℂ (X i)) =
            fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ) := Function.update_eq_self i _
        rw [this, PiTensorProduct.map_id, LinearMap.lTensor_id]
        exact N.smul_mem c hy }
  have hA : ∀ a, Algebra.adjoin ℂ (O a) ≤ Asub a := fun a =>
    Algebra.adjoin_le fun T hT y hy => hN a T hT y hy
  have h3 : ∀ T : ∀ a, Module.End ℂ (X a), (∀ a, T a ∈ Asub a) →
      ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map T) y ∈ N := by
    intro T hT
    have h2 : ∀ s : Finset α, ∀ y ∈ N, LinearMap.lTensor A
        (PiTensorProduct.map (fun a => if a ∈ s then T a else LinearMap.id)) y ∈ N := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y hy
        simpa using hy
      | insert j s hj ih =>
        intro y hy
        have := hT j _ (ih y hy)
        rw [← hcomp] at this
        convert this using 4
        funext b
        by_cases hb : b = j
        · subst hb; simp [hj]
        · simp [hb]
    intro y hy
    simpa using h2 Finset.univ y hy
  let b := fun a => Module.Free.chooseBasis ℂ (X a)
  let B := Basis.piTensorProduct b
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) B
  obtain ⟨p, hp⟩ : ∃ p, e x p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (e.map_eq_zero_iff.1 (Finsupp.ext hcon))
  refine ⟨e x p, hp, ?_⟩
  have hsum : x = (e x).sum fun q a => a ⊗ₜ[ℂ] B q := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hcoef : ∀ (t : PiTensorProduct ℂ X) (y : A ⊗[ℂ] PiTensorProduct ℂ X),
      LinearMap.lTensor A ((B.coord p).smulRight t) y = e y p ⊗ₜ[ℂ] t := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, TensorProduct.smul_tmul']
    | add y z hy hz => simp [hy, hz, TensorProduct.add_tmul]
  have hpure : ∀ v : ∀ i, X i, e x p ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v ∈ N := by
    intro v
    let f : ∀ a, Module.End ℂ (X a) := fun a => ((b a).coord (p a)).smulRight (v a)
    have hT : ∀ a, ∃ T ∈ Asub a, ∀ y ∈ (e x).support.image (fun q => b a (q a)), T y = f a y :=
      fun a => by
        haveI := hnt a
        obtain ⟨T, hT1, hT2⟩ := exists_mem_adjoin_eq (O a) (hrank a) (hirr a) (f a)
          ((e x).support.image (fun q => b a (q a)))
        exact ⟨T, hA a hT1, hT2⟩
    choose T hTA hTf using hT
    have hf : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext w
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.smulRight_apply, Module.Basis.coord_apply, B, f,
        Basis.piTensorProduct_repr_tprod_apply]
      exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
    have hmap : LinearMap.lTensor A (PiTensorProduct.map T) x =
        LinearMap.lTensor A (PiTensorProduct.map f) x := by
      rw [hsum, map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr fun q hq => ?_
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Basis.piTensorProduct_apply,
        PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
      congr 2
      funext a
      exact hTf a _ (Finset.mem_image_of_mem _ hq)
    have h4 := h3 T hTA x hxN
    rwa [hmap, hf, hcoef] at h4
  have hall : (⊤ : Submodule ℂ (PiTensorProduct ℂ X)) ≤
      N.comap (TensorProduct.mk ℂ A (PiTensorProduct ℂ X) (e x p)) := by
    rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hpure v
  exact fun y => hall (Submodule.mem_top (x := y))

private theorem dite_update_eq_update_dite {ι : Type} [DecidableEq ι] {X : ι → Type} (T T₁ : Finset ι) (hT : T ⊆ T₁)
    (s : ∀ i, X i) [DecidableEq T] (m : ∀ v : T, X v) (i : T) (z : X i) :
    (fun v : T₁ => if h : (v : ι) ∈ T then Function.update m i z ⟨v, h⟩ else s v) =
      Function.update (fun v : T₁ => if h : (v : ι) ∈ T then m ⟨v, h⟩ else s v) ⟨i, hT i.2⟩ z := by
  funext v
  by_cases hv : (v : ι) ∈ T
  · by_cases hvi : (v : ι) = i
    · have hv' : v = ⟨i, hT i.2⟩ := Subtype.ext hvi
      subst hv'
      simp
    · have h1 : (⟨v, hv⟩ : T) ≠ i := fun h => hvi (by rw [← h])
      have h2 : v ≠ ⟨i, hT i.2⟩ := fun h => hvi (by rw [h])
      rw [dite_eq_left hv, Function.update_of_ne h1, Function.update_of_ne h2, dite_eq_left hv]
  · have h2 : v ≠ ⟨i, hT i.2⟩ := fun h => hv (by rw [h]; exact i.2)
    rw [dite_eq_right hv, Function.update_of_ne h2, dite_eq_right hv]

theorem exists_ext {ι : Type} [DecidableEq ι] {X : ι → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (T T₁ : Finset ι) (hT : T ⊆ T₁) (s : ∀ i, X i) :
    ∃ e : (PiTensorProduct ℂ fun v : T => X v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => X v,
      ∀ u : ∀ i, X i, (∀ i ∉ T, u i = s i) →
        e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v := by
  classical
  let f : MultilinearMap (RingHom.id ℂ) (fun v : T => X v) (PiTensorProduct ℂ fun v : T₁ => X v) :=
    { toFun := fun m => PiTensorProduct.tprod ℂ fun v : T₁ => if h : (v : ι) ∈ T then m ⟨v, h⟩ else s v
      map_update_add' := fun m i x y => by
        simp only [dite_update_eq_update_dite T T₁ hT s]
        exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun m i c x => by
        simp only [dite_update_eq_update_dite T T₁ hT s]
        exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }
  refine ⟨PiTensorProduct.lift f, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ _ = _
  congr 1
  funext v
  by_cases hv : (v : ι) ∈ T
  · rw [dite_eq_left hv]
  · rw [dite_eq_right hv, hu v hv]

end GlobalTheory.ThK.Dbl.Dens
end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Prs

open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ Y W} {o : Rep σ Y W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
  {p : SInf F (Fin n × Fin d) →ₗ[ℂ] R.Pi} {q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Rf.Pi v} {T T₁ : Finset (Pl F)}


variable (R Rf T) in
abbrev PiT : Type := R.Pi ⊗[ℂ] PiTensorProduct ℂ fun v : T => Rf.Pi v


variable (B M T) in
def Dat (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  f ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ v ∈ SB _) ∧ ∀ v ∉ T, φ v = M.vac v


variable (B M p q T) in
def Cl : Submodule ℂ (Fn F n d × PiT R Rf T) :=
  Submodule.span ℂ {z | ∃ f φ, Dat B M T f φ ∧ z = (pure f φ, p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v))}

theorem Dat.cof {f φ} (h : Dat B M T f φ) : ∀ᶠ v in cofinite, φ v = M.vac v :=
  T.eventually_cofinite_notMem.mono h.2.2

theorem Dat.pureA (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) :
    ∃ g ∈ SB (Fin n × Fin d → Af F), ∀ f' : SInf F (Fin n × Fin d), pure f' φ = pureA F f' g :=
  PositivityTheory.ThKG.pure_eq_pureA hM φ h.2.1 h.cof

theorem Dat.sch (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) : pure f φ ∈ schA F _ := by
  obtain ⟨g, hg, e⟩ := h.pureA hM
  exact Submodule.subset_span ⟨f, g, hg, e f⟩

theorem gen_mem {f φ} (h : Dat B M T f φ) :
    (pure f φ, p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v)) ∈ Cl B M p q T := Submodule.subset_span ⟨f, φ, h, rfl⟩

theorem mem_cl {Φ ξ} : (Φ, ξ) ∈ Cl B M p q T ↔ ∃ (m : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, Dat B M T (f i) (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) ∧
      ξ = ∑ i, p (f i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ i v) := by
  constructor
  · intro h
    obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
    choose f φ hd hg using fun i => (g i).2
    have e1 : ∀ i, pure (c i • f i) (φ i) = c i • pure (f i) (φ i) := fun i => funext fun x => by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hd i).1, (hd i).2⟩, ?_, ?_⟩
    · simpa [hg, e1, Prod.fst_sum] using (congrArg Prod.fst e).symm
    · simpa [hg, Prod.snd_sum, TensorProduct.smul_tmul'] using (congrArg Prod.snd e).symm
  · rintro ⟨m, f, φ, hd, rfl, rfl⟩
    rw [prod_mk_sum]
    exact Submodule.sum_mem _ fun i _ => gen_mem (hd i)

theorem cl_map (A : Fn F n d →ₗ[ℂ] Fn F n d) (Ω : PiT R Rf T →ₗ[ℂ] PiT R Rf T₁)
    (h : ∀ f φ, Dat B M T f φ →
      (A (pure f φ), Ω (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v))) ∈ Cl B M p q T₁)
    {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) : (A Φ, Ω ξ) ∈ Cl B M p q T₁ :=
  (Submodule.span_le (p := (Cl B M p q T₁).comap (A.prodMap Ω))).2 (by rintro _ ⟨f, φ, hd, rfl⟩; exact h f φ hd) hz

theorem cl_ext (hT : T ⊆ T₁) (e : (PiTensorProduct ℂ fun v : T => Rf.Pi v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T₁ => Rf.Pi v)
    (s : ∀ v, Rf.Pi v) (he : ∀ u : ∀ v, Rf.Pi v, (∀ v ∉ T, u v = s v) →
      e (PiTensorProduct.tprod ℂ fun v : T => u v) = PiTensorProduct.tprod ℂ fun v : T₁ => u v)
    (hs : ∀ v ∉ T, q v (M.vac v) = s v) {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) : (Φ, e.lTensor _ ξ) ∈ Cl B M p q T₁ :=
  cl_map LinearMap.id _ (fun f φ hd => by
    rw [LinearMap.lTensor_tmul, he (fun v => q v (φ v)) fun v hv => by rw [hd.2.2 v hv, hs v hv]]
    exact gen_mem ⟨hd.1, hd.2.1, fun v hv => hd.2.2 v fun h => hv (hT h)⟩) hz


variable (R) in
def opAt (v : T) (Op : Module.End ℂ (Rf.Pi v)) : PiT R Rf T →ₗ[ℂ] PiT R Rf T :=
  LinearMap.lTensor R.Pi (PiTensorProduct.map (Function.update (fun j : T => (LinearMap.id : Rf.Pi j →ₗ[ℂ] Rf.Pi j)) v Op))

theorem cl_fin (hP : PureAct) (hM : M.IsGood B.ψ) (v : T) (A : Fn F n d →ₗ[ℂ] Fn F n d) (Op : Module.End ℂ (Rf.Pi v))
    (h : ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) A φ φ₁ ∧ Op (q v φ) = q v φ₁) {Φ ξ} (hz : (Φ, ξ) ∈ Cl B M p q T) :
    (A Φ, opAt R v Op ξ) ∈ Cl B M p q T := by
  refine cl_map A _ (fun f φ hd => ?_) hz
  obtain ⟨φ₁, s1, a1, e1⟩ := h _ (hd.2.1 v)
  have d₂ : Dat B M T f (Function.update φ v φ₁) := by
    refine ⟨hd.1, fun w => ?_, fun w hw => ?_⟩
    · by_cases hw : w = v
      · subst hw; simpa using s1
      · simpa [Function.update_of_ne hw] using hd.2.1 w
    · rw [Function.update_of_ne (fun e : w = v => hw (by rw [e]; exact v.2)), hd.2.2 w hw]
  convert gen_mem (p := p) (q := q) d₂ using 2
  · exact (hP F _ v A f φ hd.2.1 ((hd.cof.and hM.std).mono fun _ k => k.1.trans k.2)).2.2 _ a1
  · simp only [opAt, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext w
    by_cases hw : w = v
    · subst hw; simpa using e1
    · simp [Function.update_of_ne hw, Function.update_of_ne (show (w : Pl F) ≠ v from fun e => hw (Subtype.ext e))]

def finPart {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ := ∏ᶠ v, φ v fun i => evFin F v (x i)

theorem finPart_add {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  have e : ∀ (v : Pl F) i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
    have h : (1 : Af F) * (z i).2 = 0 :=
      congrArg Prod.snd (congrFun (hz ((0, 1) : Ainf F × Af F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i)
    have h3 : evFin F v (z i) = 0 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
      rw [← one_mul (z i).2, h, map_zero]
    rw [Pi.add_apply, map_add (f := _), h3, add_zero]
  simp only [finPart, e]

theorem Dat.rest (hM : M.IsGood B.ψ) {f φ} (h : Dat B M T f φ) : Rest (evI F) f (finPart φ) := ⟨finPart_add φ, h.sch hM⟩

theorem cl_inf (hM : M.IsGood B.ψ) (A : Fn F n d →ₗ[ℂ] Fn F n d) (Op : Module.End ℂ R.Pi)
    (h : ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb, Acts (evI F) A f f₁ ∧ Op (p f) = p f₁) {Φ ξ}
    (hz : (Φ, ξ) ∈ Cl B M p q T) : (A Φ, Op.rTensor _ ξ) ∈ Cl B M p q T := by
  refine cl_map A _ (fun f φ hd => ?_) hz
  obtain ⟨f₁, s1, a1, e1⟩ := h _ hd.1
  rw [LinearMap.rTensor_tmul, e1, show A (pure f φ) = pure f₁ φ from a1 _ (hd.rest hM)]
  exact gen_mem ⟨s1, hd.2⟩

theorem loc_op (hL : LocRepEx) {χ χ' r s r' s'} (hp : IsPair B M χ χ' o r s r' s') {v : Pl F} {h : UA σ W.J}
    (hh : h ∈ UAt σ W (evFin F v)) : ∃ A : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
      ∀ φ ∈ SB _, A φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (A φ) := by
  obtain ⟨ω, ρ, L⟩ := hL F E σ n d B Y W M o ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, _, _, hp.weil⟩ v
  have o1 : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]
  exact ⟨ω (1, h), fun φ hφ => ⟨L.pres 1 o1 h hh _ hφ, (L.acts 1 o1 h hh _ hφ _).2 rfl⟩⟩

theorem inf_op (hA : ArchOp) {χ χ' r s r' s'} (hp : IsPair B M χ χ' o r s r' s') {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ A : Module.End ℂ (SInf F (Fin n × Fin d)), ∀ f ∈ M.Pol B.ψ B.emb, A f ∈ M.Pol B.ψ B.emb ∧ Acts (evI F) (o (1, k)) f (A f) := by
  have o1 : (1 : UA σ Y.J) ∈ KInf σ Y B.emb :=
    ⟨fun u _ => by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero], fun w => by
      rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp 1 o1.1 k hk.1
  exact ⟨A, fun f hf => ⟨a2 o1 hk f hf, a1.2 f⟩⟩

theorem common_op {V V' P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup P] [Module ℂ P]
    {S : Submodule ℂ V} {S' : Submodule ℂ V'} {p : V →ₗ[ℂ] P} {p' : V' →ₗ[ℂ] P} (h : S.map p = ⊤) (A : S →ₗ[ℂ] V)
    (A' : S' →ₗ[ℂ] V') (e : ∀ x x', p x.1 = p' x'.1 → p (A x) = p' (A' x')) :
    ∃ Op : Module.End ℂ P, (∀ x, Op (p x.1) = p (A x)) ∧ ∀ x', Op (p' x'.1) = p' (A' x') := by
  have hq : Function.Surjective (p.domRestrict S) := fun u => by
    obtain ⟨x, h1, h2⟩ : u ∈ S.map p := h ▸ Submodule.mem_top
    exact ⟨⟨x, h1⟩, h2⟩
  obtain ⟨s, hs⟩ := (p.domRestrict S).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have k : ∀ x : S, p (A (s (p x.1))) = p (A x) := fun x => by
    have := e (s (p x.1) - x) 0 (by simpa [sub_eq_zero] using LinearMap.congr_fun hs (p x.1))
    simpa [sub_eq_zero] using this
  exact ⟨p ∘ₗ A ∘ₗ s, k, fun x' => e _ _ (LinearMap.congr_fun hs _)⟩

variable {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem fin_ops (hL : LocRepEx) (hm : IsMatched B G X om om' R Rf) {v : Pl F} {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    ∃ Op : Module.End ℂ (Rf.Pi v), (∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ ∧ Op (Rf.p v φ) = Rf.p v φ₁) ∧
      (∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → Op (Rf.p v φ) = Rf.p v φ₁) ∧
      ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ Op (Rf.p' v φ) = Rf.p' v φ₁ := by
  obtain ⟨A, hA⟩ := loc_op hL (PositivityTheory.ThKG.pairV hm.triple) hh
  obtain ⟨A', hA'⟩ := loc_op hL (PositivityTheory.ThKG.pairV' hm.triple) hh
  obtain ⟨Op, h1, h2⟩ := common_op (hm.fin.onto v) (A.domRestrict _) (A'.domRestrict (SB _)) fun x x' e =>
    hm.fin.equiv v h hh _ x.2 _ x'.2 _ (hA _ x.2).1 _ (hA' _ x'.2).1 (hA _ x.2).2 (hA' _ x'.2).2 e
  refine ⟨Op, fun φ hφ => ⟨_, (hA _ hφ).1, (hA _ hφ).2, h1 ⟨φ, hφ⟩⟩, fun φ hφ φ₁ h₁ e => ?_,
    fun φ hφ => ⟨_, (hA' _ hφ).1, (hA' _ hφ).2, h2 ⟨φ, hφ⟩⟩⟩
  obtain ⟨φ', s', e'⟩ : Rf.p v φ ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
  rw [hm.fin.equiv v h hh _ hφ _ s' _ h₁ _ (hA' _ s').1 e (hA' _ s').2 e'.symm, ← e']
  exact h2 ⟨φ', s'⟩

theorem inf_ops (hO : ArchOp) (hm : IsMatched B G X om om' R Rf) {k : UA σ G.W.J} (hk : k ∈ KInf σ G.W B.emb) :
    ∃ Op : Module.End ℂ R.Pi,
      (∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (1, k)) f f₁ ∧ Op (R.p f) = R.p f₁) ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → Op (R.p f) = R.p f₁) ∧
      ∀ f ∈ G.M'.Pol B.ψ B.emb, ∃ f₁ ∈ G.M'.Pol B.ψ B.emb, Acts (evI F) (om' (1, k)) f f₁ ∧ Op (R.p' f) = R.p' f₁ := by
  obtain ⟨A, hA⟩ := inf_op hO (PositivityTheory.ThKG.pairV hm.triple) hk
  obtain ⟨A', hA'⟩ := inf_op hO (PositivityTheory.ThKG.pairV' hm.triple) hk
  obtain ⟨Op, h1, h2⟩ := common_op hm.real.quot.onto (A.domRestrict _) (A'.domRestrict (G.M'.Pol B.ψ B.emb)) fun x x' e =>
    hm.real.cpt k hk _ x.2 _ x'.2 _ _ (hA _ x.2).2 (hA' _ x'.2).2 e
  refine ⟨Op, fun f hf => ⟨_, (hA _ hf).1, (hA _ hf).2, h1 ⟨f, hf⟩⟩, fun f hf f₁ e => ?_,
    fun f hf => ⟨_, (hA' _ hf).1, (hA' _ hf).2, h2 ⟨f, hf⟩⟩⟩
  obtain ⟨f', s', e'⟩ : R.p f ∈ (G.M'.Pol B.ψ B.emb).map R.p' := hm.real.quot'.onto ▸ Submodule.mem_top
  rw [hm.real.cpt k hk _ hf _ s' _ _ e (hA' _ s').2 e'.symm, ← e']
  exact h2 ⟨f', s'⟩

theorem polMatch_iff {Φ Φ'} : PolMatch B G X R Rf Φ Φ' ↔
    ∃ T, X.T ⊆ T ∧ ∃ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T ∧ (Φ', ξ) ∈ Cl B G.M' R.p' Rf.p' T := by
  refine exists_congr fun T => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩
    exact ⟨_, mem_cl.2 ⟨m, f, φ, h1, e1, rfl⟩, mem_cl.2 ⟨m', f', φ', h2, e2, e3⟩⟩
  · rintro ⟨ξ, h, h'⟩
    obtain ⟨m, f, φ, h1, e1, e3⟩ := mem_cl.1 h
    obtain ⟨m', f', φ', h2, e2, e4⟩ := mem_cl.1 h'
    exact ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3.symm.trans e4⟩

theorem enlarge (hm : IsMatched B G X om om' R Rf) (hX : X.T ⊆ T) (hT : T ⊆ T₁) : ∃ e : PiT R Rf T →ₗ[ℂ] PiT R Rf T₁,
    (∀ Φ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T → (Φ, e ξ) ∈ Cl B G.M R.p Rf.p T₁) ∧
      ∀ Φ ξ, (Φ, ξ) ∈ Cl B G.M' R.p' Rf.p' T → (Φ, e ξ) ∈ Cl B G.M' R.p' Rf.p' T₁ := by
  obtain ⟨e, he⟩ := exists_ext (X := Rf.Pi) T T₁ hT fun v => Rf.p v (G.M.vac v)
  exact ⟨_, fun _ _ => cl_ext hT e _ he fun _ _ => rfl,
    fun _ _ => cl_ext hT e _ he fun v hv => (hm.fin.sph v fun h => hv (hX h)).1.symm⟩

theorem polMatch_big (hm : IsMatched B G X om om' R Rf) {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') :
    ∃ T₀, X.T ⊆ T₀ ∧ ∀ T, T₀ ⊆ T → ∃ ξ, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T ∧ (Φ', ξ) ∈ Cl B G.M' R.p' Rf.p' T := by
  obtain ⟨T₀, hT, ξ, h1, h2⟩ := polMatch_iff.1 h
  refine ⟨T₀, hT, fun T h0 => ?_⟩
  obtain ⟨e, e1, e2⟩ := enlarge hm hT h0
  exact ⟨_, e1 _ _ h1, e2 _ _ h2⟩

theorem polMatch_add_smul (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (h : PolMatch B G X R Rf Φ Φ')
    (h' : PolMatch B G X R Rf Ψ Ψ') (c : ℂ) : PolMatch B G X R Rf (Φ + c • Ψ) (Φ' + c • Ψ') := by
  obtain ⟨T, hT, H⟩ := polMatch_big hm h
  obtain ⟨T', -, H'⟩ := polMatch_big hm h'
  obtain ⟨ξ, h1, h2⟩ := H _ (Finset.subset_union_left (s₂ := T'))
  obtain ⟨η, h3, h4⟩ := H' _ (Finset.subset_union_right (s₁ := T))
  exact polMatch_iff.2 ⟨_, hT.trans Finset.subset_union_left, ξ + c • η, add_mem h1 (Submodule.smul_mem _ c h3),
    add_mem h2 (Submodule.smul_mem _ c h4)⟩

end GlobalTheory.ThK.Dbl.Prs

end
