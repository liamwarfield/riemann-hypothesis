module

public import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
public import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot

@[expose] public section

section -- merged from ReciprocityTheory.GroupCohomology.CardLenStatement
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

def IsZHat (G : Type u) [Group G] [TopologicalSpace G] (s : G) : Prop :=
  Dense (Subgroup.zpowers s : Set G) ∧ ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k

def ZHatStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (s : G), IsZHat G s → ∀ (M : TRep R G) [DiscreteTopology M.V], (∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) →
  (∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
    ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s)) ∧
  (∀ n, 1 < n → Subsingleton (M.H n)) ∧ (IsFiniteLength R M.V → M.coch.FinLen 1 ∧ M.coch.chi 1 = 0)

def ShiftStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (N : ℕ),
  (∀ (M : TRep R G) [DiscreteTopology M.V], (∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) → Subsingleton (M.H N)) →
  ∀ (M : TRep R G) [DiscreteTopology M.V], (∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) →
    ∀ n, N ≤ n → Subsingleton (M.H n)

end

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

universe u

section AdmAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem pair_hom_f_coe_of_id {M M' : TRep R G} (P : Pair M M') (h : P.φ = MonoidHom.id G) (n : ℕ)
    (x : M.coch.X n) : (P.hom.f n x).1 = fun g => P.u (x.1 g) := by
  funext g
  show P.u (x.1 fun i => P.φ (g i)) = P.u (x.1 g)
  rw [h]
  rfl

end AdmAux

theorem admissibility_holds : AdmStatement.{u} := by
  intro R _ G _ _ _ A B C i p h
  refine ⟨fun n x y hxy => ?_, fun n => ?_, fun n => ?_⟩
  · refine Subtype.ext (funext fun g => h.emb.injective ?_)
    have hg := congrArg (fun z => z.1 g) hxy
    simp only [pair_hom_f_coe_of_id i h.i_id] at hg
    exact hg
  · intro y
    constructor
    · intro hy
      have hy' : ∀ g, p.u (y.1 g) = 0 := fun g => by
        have hg := congrArg (fun z => z.1 g) hy
        simp only [pair_hom_f_coe_of_id p h.p_id] at hg
        exact hg
      have hex : ∀ g, ∃ a, i.u a = y.1 g := fun g => (h.exact (y.1 g)).1 (hy' g)
      choose x hx using hex
      have hxc : Continuous x := by
        rw [h.emb.continuous_iff]
        have hfx : (i.u ∘ x) = y.1 := funext hx
        rw [hfx]
        exact y.2
      exact ⟨⟨x, hxc⟩, Subtype.ext ((pair_hom_f_coe_of_id i h.i_id n _).trans (funext hx))⟩
    · rintro ⟨x, rfl⟩
      refine Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans ?_)
      funext g
      rw [pair_hom_f_coe_of_id i h.i_id]
      exact (h.exact (i.u (x.1 g))).2 ⟨x.1 g, rfl⟩
  · intro c
    obtain ⟨s, hs, hps⟩ := h.sec
    exact ⟨⟨s ∘ c.1, hs.comp c.2⟩,
      Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans (funext fun g => hps _))⟩

theorem limRep_holds : LimRepStatement.{u} := by
  intro R _ G _ _ _ A _ τ L π hτ hemb hlift
  have cτ : ∀ m n (x : (A (m + 1)).coch.X n), ((τ m).hom.f n x).1 = fun g => (τ m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (τ m) (hτ m).1 n x
  have cπ : ∀ m n (x : L.coch.X n), ((π m).hom.f n x).1 = fun g => (π m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (π m) (hτ m).2.1 n x
  refine ⟨fun m n c => ?_, fun m n x => ?_, fun n x hx => ?_, fun n y hy => ?_⟩
  · choose s hs using (hτ m).2.2.1
    exact ⟨⟨s ∘ c.1, (continuous_of_discreteTopology (f := s)).comp c.2⟩,
      Subtype.ext ((cτ m n _).trans (funext fun g => hs _))⟩
  · refine Subtype.ext ?_
    rw [cτ, cπ, cπ]
    funext g
    exact (hτ m).2.2.2 _
  · refine Subtype.ext (funext fun g => ?_)
    apply hemb.injective
    funext m
    have hg := congrArg (fun z => z.1 g) (hx m)
    simp only [cπ] at hg
    refine hg.trans ?_
    show (0 : (A m).V) = (π m).u 0
    rw [map_zero]
  · have hy' : ∀ g m, (τ m).u ((y (m + 1)).1 g) = (y m).1 g := fun g m => by
      have hg := congrArg (fun z => z.1 g) (hy m)
      simp only [cτ] at hg
      exact hg
    choose x hx using fun g => hlift (fun m => (y m).1 g) (hy' g)
    have hxc : Continuous x := by
      rw [hemb.continuous_iff]
      have hfx : ((fun (x : L.V) m => (π m).u x) ∘ x) = fun g m => (y m).1 g :=
        funext fun g => funext (hx g)
      rw [hfx]
      exact continuous_pi fun m => by exact (y m).2
    exact ⟨⟨x, hxc⟩, fun m => Subtype.ext ((cπ m n _).trans (funext fun g => hx g m))⟩

section ColimAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end ColimAux

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.Localise
section -- merged from ReciprocityTheory.GroupCohomology.LocaliseA
namespace ReciprocityTheory.Coh

open Cx Function

universe u

section Alg

variable {R : Type u} [CommRing R] {A B : Cx R}

theorem cx_smul_d {n : ℕ} (t : R) (x : B.X n) : B.d n (t • x) = t • B.d n x := map_smul _ _ _

theorem bij_H_of_bij (t : R) (ht : ∀ n, Bijective fun x : B.X n => t • x) (n : ℕ) :
    Bijective (algebraMap R (Module.End R (B.H n)) t) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Module.algebraMap_end_apply, cls_smul, cls_eq_zero_iff] at hc
      rw [cls_eq_zero_iff]
      cases n with
      | zero =>
        have h0 : t • x = 0 := hc
        exact (ht 0).1 (h0.trans (smul_zero t).symm)
      | succ n =>
        obtain ⟨y, hy⟩ := hc
        obtain ⟨y', rfl⟩ := (ht n).2 y
        refine ⟨y', (ht (n + 1)).1 ?_⟩
        show t • B.d n y' = t • x
        rw [← cx_smul_d, hy]
  · intro c
    induction c using H_ind with
    | h x hx =>
      obtain ⟨x', rfl⟩ := (ht n).2 x
      have hx' : B.d n x' = 0 := (ht (n + 1)).1 (by
        show t • B.d n x' = t • 0
        rw [← cx_smul_d, smul_zero]; exact hx)
      exact ⟨B.cls n x' hx', by rw [Module.algebraMap_end_apply, cls_smul]⟩

theorem isLocalized_of_cx (j : Hom A B) (t : R) (hj : ∀ n, Injective (j.f n))
    (ht : ∀ n, Bijective fun x : B.X n => t • x)
    (hc : ∀ n (x : B.X n), ∃ (m : ℕ) (y : A.X n), j.f n y = t ^ m • x) (n : ℕ) :
    IsLocalizedModule (Submonoid.powers t) (j.H n) := by
  constructor
  case map_units =>
    rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap R (Module.End R (B.H n)) (t ^ k))
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht n)).pow k
  case surj =>
    intro y
    induction y using H_ind with
    | h x hx =>
      obtain ⟨m, a, ha⟩ := hc n x
      have ha0 : A.d n a = 0 := (hj (n + 1)) (by
        rw [j.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
      refine ⟨(A.cls n a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
      show (t ^ m) • B.cls n x hx = j.H n (A.cls n a ha0)
      rw [cls_smul, Hom.H_cls]
      exact cls_congr _ _ ha.symm
  case exists_of_eq =>
    have key : ∀ z : A.H n, j.H n z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
      intro z hz
      induction z using H_ind with
      | h g hg =>
        rw [Hom.H_cls, cls_eq_zero_iff] at hz
        cases n with
        | zero =>
          have h0 : j.f 0 g = 0 := hz
          refine ⟨1, ?_⟩
          rw [one_smul, cls_eq_zero_iff]
          exact (hj 0) (h0.trans (map_zero _).symm)
        | succ n =>
          obtain ⟨h, hh⟩ := hz
          obtain ⟨m, k, hk⟩ := hc n h
          refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
          show (t ^ m) • A.cls (n + 1) g hg = 0
          rw [cls_smul, cls_eq_zero_iff]
          refine ⟨k, (hj (n + 1)) ?_⟩
          rw [j.comm, hk, cx_smul_d, hh, map_smul]
    intro x₁ x₂ h
    obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
    exact ⟨c, by rw [smul_sub, sub_eq_zero] at hc'; exact hc'⟩

end Alg

section Trunc

variable {R : Type u} [CommRing R] (A : Cx R) (L : Submodule R (A.H 1))

end Trunc

end ReciprocityTheory.Coh
end

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  have localiseCx {A B : Cx R} (f : Hom A B) (hj : ∀ k, Injective (f.f k))
      (ht : ∀ k, Bijective fun x : B.X k => t • x)
      (hc : ∀ k (x : B.X k), ∃ (m : ℕ) (y : A.X k), f.f k y = t ^ m • x)
      (k : ℕ) : IsLocalizedModule (Submonoid.powers t) (f.H k) := by
    constructor
    · rintro ⟨_, m, rfl⟩
      show IsUnit (algebraMap R (Module.End R (B.H k)) (t ^ m))
      rw [map_pow]
      exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht k)).pow m
    · intro y
      induction y using H_ind with
      | h x hx =>
        obtain ⟨m, a, ha⟩ := hc k x
        have ha0 : A.d k a = 0 := (hj (k + 1)) (by
          rw [f.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
        refine ⟨(A.cls k a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
        show (t ^ m) • B.cls k x hx = f.H k (A.cls k a ha0)
        rw [cls_smul, Hom.H_cls]
        exact cls_congr _ _ ha.symm
    · have key : ∀ z : A.H k, f.H k z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
        intro z hz
        induction z using H_ind with
        | h g hg =>
          rw [Hom.H_cls, cls_eq_zero_iff] at hz
          cases k with
          | zero =>
            have h0 : f.f 0 g = 0 := hz
            refine ⟨1, ?_⟩
            rw [one_smul, cls_eq_zero_iff]
            exact (hj 0) (h0.trans (map_zero _).symm)
          | succ k =>
            obtain ⟨h, hh⟩ := hz
            obtain ⟨m, a, ha⟩ := hc k h
            refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
            show (t ^ m) • A.cls (k + 1) g hg = 0
            rw [cls_smul, cls_eq_zero_iff]
            refine ⟨a, (hj (k + 1)) ?_⟩
            rw [f.comm, ha, cx_smul_d, hh, map_smul]
      intro x₁ x₂ h
      obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
      exact ⟨c, sub_eq_zero.mp (by simpa only [smul_sub] using hc')⟩
  refine localiseCx j.hom ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.LowHolds
namespace ReciprocityTheory.Coh

universe u

theorem low_holds : LowStatement.{u} := by
  intro R _ G _ _ _ M
  refine ⟨fun n => ⟨LowDeg.hEquiv M n, fun x hx => ⟨_, LowDeg.hEquiv_cls M n x hx⟩⟩,
    ⟨LowDeg.cohomZeroEquivContinuous M, fun x hx => LowDeg.cohomZeroEquivContinuous_cls_apply M x hx⟩,
    ⟨LowDeg.h1EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩, ⟨LowDeg.h2EquivOfOrderTwo M, fun x hx => ⟨_, rfl⟩⟩⟩

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.HomogIso
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace HomogeneousCochainIso

theorem hgi_val {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) = i + j + 1) ∨
      ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) + 1 = i + j) := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

theorem hgi_sign {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ (i.succAbove j : ℕ) * (-1) ^ (j.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ)) := by
  rw [← pow_add, ← pow_add]
  rcases hgi_val i j with h | h
  · rw [h, pow_succ]; ring
  · rw [← h, pow_succ]; ring

theorem hd_hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) :
    hd (n + 1) (hd n F) = 0 := by
  funext x
  simp only [hd, Finset.smul_sum, smul_smul, Pi.zero_apply]
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun (i : Fin (n + 3)) (j : Fin (n + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • F fun k => x (i.succAbove (j.succAbove k)))]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_succAbove_predAbove, hgi_sign, neg_smul]
    exact add_neg_cancel _
  · rintro ⟨i, j⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    exact Fin.succAbove_ne i j h.1
  · intros; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def hdL (R : Type u) [CommRing R] {V X : Type u} [AddCommGroup V] [Module R V] (n : ℕ) :
    ((Fin (n + 1) → X) → V) →ₗ[R] ((Fin (n + 2) → X) → V) where
  toFun := hd n
  map_add' F F' := by funext x; simp [hd, Finset.sum_add_distrib]
  map_smul' r F := by
    funext x
    simp only [hd, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem hd_mem (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ)
    (F : (Fin (n + 1) → X) → M.V) (hF : F ∈ hcoch M X n) : hd n F ∈ hcoch M X (n + 1) := by
  refine ⟨?_, fun g x => ?_⟩
  · exact continuous_finsetSum _ fun i _ => (continuous_const_smul ((-1 : ℤ) ^ (i : ℕ))).comp
      (hF.1.comp (continuous_pi fun j => continuous_apply (i.succAbove j)))
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [hd, hF.2, map_sum, map_zsmul]

def hcx (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] : Cx R where
  X n := hcoch M X n
  d n := (hdL R n).restrict fun F hF => hd_mem M X n F hF
  dd n F := Subtype.ext (hd_hd n F.1)

theorem continuous_partialProd' {m : ℕ} (i : Fin (m + 1)) :
    Continuous fun g : Fin m → G => Fin.partialProd g i := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialProd_zero]; exact continuous_const
  | succ i ih => simp only [Fin.partialProd_succ]; exact ih.mul (continuous_apply i)

def eFun (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 1) → G) : M.V :=
  M.rho (x 0) (f fun i => (x i.castSucc)⁻¹ * x i.succ)

theorem eFun_mem (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (hf : Continuous f) :
    eFun M n f ∈ hcoch M G n := by
  refine ⟨?_, fun g x => ?_⟩
  · exact M.cont.comp (f := fun x : Fin (n + 1) → G => (x 0, f fun i => (x i.castSucc)⁻¹ * x i.succ))
      ((continuous_apply 0).prodMk (hf.comp (continuous_pi fun i =>
        ((continuous_apply _).inv).mul (continuous_apply _))))
  · simp only [eFun, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul,
      Module.End.mul_apply]

def eIso (M : TRep R G) (n : ℕ) : M.coch.X n ≃ₗ[R] hcoch M G n where
  toFun f := ⟨eFun M n f.1, eFun_mem M n f.1 f.2⟩
  map_add' f f' := Subtype.ext (funext fun x => by
    show M.rho (x 0) ((f.1 + f'.1) fun i => _) = _
    rw [Pi.add_apply, map_add (f := _)]; rfl)
  map_smul' r f := Subtype.ext (funext fun x => by
    show M.rho (x 0) ((r • f.1) fun i => _) = _
    rw [Pi.smul_apply, map_smul]; rfl)
  invFun F := ⟨fun g => F.1 (Fin.partialProd g),
    F.2.1.comp (continuous_pi fun i => continuous_partialProd' i)⟩
  left_inv f := Subtype.ext (funext fun g => by
    simp [eFun, Fin.partialProd_zero, Fin.partialProd_right_inv])
  right_inv F := Subtype.ext (funext fun x => by
    show M.rho (x 0) (F.1 (Fin.partialProd fun i => (x i.castSucc)⁻¹ * x i.succ)) = F.1 x
    rw [← F.2.2]
    conv_rhs => rw [← Fin.partialProd_left_inv x]
    rfl)

theorem hgi_negpow (V : Type u) [AddCommGroup V] [Module R V] (k : ℕ) (v : V) :
    (-1 : R) ^ k • v = (-1 : ℤ) ^ k • v := by
  rw [← Int.cast_smul_eq_zsmul R]; push_cast; rfl

theorem eFun_zero (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 2) → G) :
    eFun M n f (fun k => x (Fin.succAbove 0 k)) =
      M.rho (x 0) (M.rho ((x (0 : Fin (n + 1)).castSucc)⁻¹ * x (0 : Fin (n + 1)).succ)
        (f fun i => (x i.succ.castSucc)⁻¹ * x i.succ.succ)) := by
  rw [← Module.End.mul_apply, ← map_mul, Fin.castSucc_zero, mul_inv_cancel_left]
  simp only [eFun, Fin.succAbove_zero, Fin.succ_castSucc]

theorem eFun_succ (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 2) → G)
    (j : Fin (n + 1)) :
    eFun M n f (fun k => x (j.succ.succAbove k)) =
      M.rho (x 0) (f (Fin.contractNth j (· * ·) fun i => (x i.castSucc)⁻¹ * x i.succ)) := by
  have key : (fun i : Fin n => (x (j.succ.succAbove i.castSucc))⁻¹ * x (j.succ.succAbove i.succ)) =
      Fin.contractNth j (· * ·) fun i => (x i.castSucc)⁻¹ * x i.succ := by
    have hp : ∀ c, Fin.partialProd (fun i => (x i.castSucc)⁻¹ * x i.succ) c = (x 0)⁻¹ * x c := by
      intro c
      have h := congrFun (Fin.partialProd_left_inv x) c
      simp only [Pi.smul_apply, smul_eq_mul] at h
      exact eq_inv_mul_of_mul_eq h
    funext k
    rw [← Fin.inv_partialProd_mul_eq_contractNth, ← Fin.succ_succAbove_succ, hp, hp]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  simp only [eFun, Fin.succ_succAbove_zero]
  rw [key]

theorem eFun_dn (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) :
    eFun M (n + 1) (dn M.rho n f) = hd n (eFun M n f) := by
  funext x
  rw [hd, Fin.sum_univ_succ, eFun_zero]
  simp only [eFun_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  show M.rho (x 0) (dn M.rho n f _) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dn_apply, map_add (f := _), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hgi_negpow, map_zsmul]

end HomogeneousCochainIso

open HomogeneousCochainIso

theorem homogExists_holds : HomogExistsStatement.{u} := by
  intro R _ G _ _ _ M X _ _
  exact ⟨hcx M X, fun n => LinearEquiv.refl R _, fun n a => rfl⟩

theorem homogIso_holds : HomogIsoStatement.{u} := by
  intro R _ G _ _ _ M
  refine ⟨eIso M, fun n a => ?_, fun n f x => rfl, fun n f g => ?_⟩
  · exact eFun_dn M n a.1
  · show f.1 g = M.rho (Fin.partialProd g 0) (f.1 fun i => _)
    simp [Fin.partialProd_zero, Fin.partialProd_right_inv]

end

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.ContractNthCastAddCastSucc
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

noncomputable section

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section S1
variable {G : Type u} [Group G]

theorem prod_ofFn_eq_partialProd {n : ℕ} (f : Fin n → G) : (List.ofFn f).prod = Fin.partialProd f (Fin.last n) := by
  simp only [Fin.partialProd, Fin.val_last]
  rw [List.take_of_length_le (by simp)]

theorem prod_ofFn_contractNth {m : ℕ} (h : Fin (m + 1) → G) (j : Fin m) :
    (List.ofFn (Fin.contractNth j.castSucc (· * ·) h)).prod = (List.ofFn h).prod := by
  rw [prod_ofFn_eq_partialProd, prod_ofFn_eq_partialProd, Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  ext
  simp [Fin.succAbove]

theorem apply_eq_of_val_eq {n : ℕ} (g : Fin n → G) {i j : Fin n} (h : (i : ℕ) = j) : g i = g j :=
  congrArg g (Fin.ext h)

theorem mul_eq_mul_of_val_eq {n : ℕ} (g : Fin n → G) {i j k l : Fin n} (h : (i : ℕ) = j) (h' : (k : ℕ) = l) :
    g i * g k = g j * g l := by rw [apply_eq_of_val_eq g h, apply_eq_of_val_eq g h']

variable {p q : ℕ} (e : p + 1 + q = p + q + 1) (g : Fin (p + q + 1) → G)

theorem contractNth_castAdd_castSucc (j i : Fin p) : (Fin.castAdd (q + 1) j).contractNth (· * ·) g (Fin.castAdd q i) =
    (Fin.castSucc j).contractNth (· * ·) (fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))) i := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)

theorem contractNth_castAdd_natAdd (j : Fin p) (k : Fin q) : (Fin.castAdd (q + 1) j).contractNth (· * ·) g (Fin.natAdd p k) =
    g (Fin.natAdd p k).succ := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)

theorem contractNth_natAdd_castAdd (k : Fin (q + 1)) (i : Fin p) : (Fin.natAdd p k).contractNth (· * ·) g (Fin.castAdd q i) =
    g (Fin.castAdd (q + 1) i) := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)

theorem contractNth_natAdd_natAdd (k : Fin (q + 1)) (l : Fin q) : (Fin.natAdd p k).contractNth (· * ·) g (Fin.natAdd p l) =
    k.contractNth (· * ·) (fun j : Fin (q + 1) => g (Fin.natAdd p j)) l := by
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)

theorem cast_castAdd_succ (i : Fin p) : g (Fin.cast e (Fin.castAdd q i.succ)) = g (Fin.castAdd q i).succ :=
  apply_eq_of_val_eq g (by simp)

theorem cast_natAdd_succ (j : Fin q) : g (Fin.cast e (Fin.natAdd (p + 1) j)) = g (Fin.natAdd p j).succ :=
  apply_eq_of_val_eq g (by simp; omega)

theorem contractNth_last_cast : (Fin.last p).contractNth (· * ·) (fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))) =
    fun i => g (Fin.castAdd (q + 1) i) := by
  funext i
  simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd, Fin.val_last]
  split_ifs <;> first | omega | exact apply_eq_of_val_eq g (by simp <;> omega) | exact mul_eq_mul_of_val_eq g (by simp <;> omega) (by simp <;> omega)

theorem cast_castAdd_zero : g (Fin.cast e (Fin.castAdd q 0)) = g 0 := apply_eq_of_val_eq g (by simp)

theorem prod_ofFn_cast_zero : (List.ofFn fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))).prod =
    g 0 * (List.ofFn fun i : Fin p => g (Fin.castAdd q i).succ).prod := by
  rw [List.ofFn_succ, List.prod_cons, cast_castAdd_zero e g]
  simp only [cast_castAdd_succ e g]

theorem prod_ofFn_cast_last : (List.ofFn fun i : Fin (p + 1) => g (Fin.cast e (Fin.castAdd q i))).prod =
    (List.ofFn fun i : Fin p => g (Fin.castAdd (q + 1) i)).prod * g (Fin.natAdd p (0 : Fin (q + 1))) := by
  rw [List.ofFn_succ', List.prod_concat]
  congr 1
  all_goals first | exact apply_eq_of_val_eq g (by simp) | (congr 1; funext i; exact apply_eq_of_val_eq g (by simp)) | (congr 2; funext i; exact apply_eq_of_val_eq g (by simp))

end S1

section S2
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cupProduct_abelian_identity {V : Type*} [AddCommGroup V] {a b s1 s1' s2 s2' l f : V} (h0 : s1 = s1') (h1 : a = b) (h2 : s2 = s2')
    (h3 : l + f = 0) : a + (s1 + s2) = b + (s1' + l) + (f + s2') := by
  subst h0 h1 h2
  rw [eq_neg_of_add_eq_zero_left h3]
  abel

theorem cupProduct_leibniz {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (f : (Fin p → G) → M.V)
    (f' : (Fin q → G) → N.V) (g : Fin (p + q + 1) → G) :
    dn P.rho (p + q) (cupFun b p q f f') g =
    cupFun b (p + 1) q (dn M.rho p f) f' (fun i => g (i.cast (by omega))) +
      (-1 : R) ^ p • cupFun b p (q + 1) f (dn N.rho q f') g := by
  have e : p + 1 + q = p + q + 1 := by omega
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dn_apply, cupFun, map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_add, Finset.smul_sum, smul_smul]
  rw [Fin.sum_univ_castSucc (n := p)]
  rw [show ∀ F : Fin (p + q + 1) → P.V, ∑ j, F j = ∑ j : Fin p, F (Fin.castAdd (q + 1) j) +
    ∑ k : Fin (q + 1), F (Fin.natAdd p k) from fun F => Fin.sum_univ_add (a := p) (b := q + 1) F]
  simp only [contractNth_castAdd_castSucc e g, contractNth_castAdd_natAdd g, contractNth_natAdd_castAdd g, contractNth_natAdd_natAdd g, cast_castAdd_succ e g, cast_natAdd_succ e g, contractNth_last_cast e g, cast_castAdd_zero e g,
    prod_ofFn_contractNth, Fin.val_castAdd, Fin.val_castSucc, Fin.val_natAdd, Fin.val_last]
  refine cupProduct_abelian_identity rfl ?_ ?_ ?_
  · rw [prod_ofFn_cast_zero e g, map_mul, Module.End.mul_apply, b.equiv]
  · exact Finset.sum_congr rfl fun x _ => by rw [← pow_add, add_assoc]
  · have hu : (fun j : Fin q => g (Fin.natAdd p j).succ) = fun i => g (Fin.natAdd p i.succ) :=
      funext fun j => apply_eq_of_val_eq g (by simp <;> omega)
    rw [prod_ofFn_cast_last e g, map_mul, Module.End.mul_apply, hu, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]

end S2

section S3
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cupProduct_continuous {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) {f : (Fin p → G) → M.V}
    {f' : (Fin q → G) → N.V} (hf : Continuous f) (hf' : Continuous f') :
    Continuous (cupFun b p q f f') := by
  have hpr : Continuous fun g : Fin (p + q) → G => (List.ofFn fun i => g (Fin.castAdd q i)).prod := by
    simp only [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply _
  exact b.cont.comp (f := fun g : Fin (p + q) → G => (f fun i => g (Fin.castAdd q i),
      N.rho (List.ofFn fun i => g (Fin.castAdd q i)).prod (f' fun j => g (Fin.natAdd p j))))
    ((hf.comp (continuous_pi fun i => continuous_apply _)).prodMk
      (N.cont.comp (f := fun g : Fin (p + q) → G => ((List.ofFn fun i => g (Fin.castAdd q i)).prod,
        f' fun j => g (Fin.natAdd p j)))
        (hpr.prodMk (hf'.comp (continuous_pi fun j => continuous_apply _)))))

theorem cochain_add_val (M : TRep R G) (n : ℕ) (x y : M.coch.X n) : (x + y).1 = x.1 + y.1 := rfl
theorem cochain_smul_val (M : TRep R G) (n : ℕ) (r : R) (x : M.coch.X n) : (r • x).1 = r • x.1 := rfl
theorem cochain_zero_val (M : TRep R G) (n : ℕ) : (0 : M.coch.X n).1 = 0 := rfl

def cupCoch {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) :
    M.coch.X p →ₗ[R] N.coch.X q →ₗ[R] P.coch.X (p + q) :=
  LinearMap.mk₂ R (fun x y => ⟨cupFun b p q x.1 y.1, cupProduct_continuous b p q x.2 y.2⟩)
    (fun x x' y => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))
    (fun r x y => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))
    (fun x y y' => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))
    (fun r x y => Subtype.ext (funext fun g => by simp [cupFun, cochain_add_val, cochain_smul_val] <;> rfl))

theorem cupCoch_val {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p) (y : N.coch.X q) :
    (cupCoch b p q x y).1 = cupFun b p q x.1 y.1 := rfl

theorem cochain_differential_val (M : TRep R G) (n : ℕ) (z : M.coch.X n) : (M.coch.d n z).1 = dn M.rho n z.1 := rfl

theorem mem_coboundaries_of_eq_d {P : TRep R G} {m n : ℕ} (h : m = n + 1) (z : P.coch.X m) (w : P.coch.X n)
    (hz : ∀ g, z.1 g = dn P.rho n w.1 fun i => g (Fin.cast h.symm i)) : z ∈ P.coch.B m := by
  subst h
  exact ⟨w, Subtype.ext (funext fun g => (hz g).symm)⟩

theorem cupProduct_coboundary_left {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p)
    (hx : x ∈ M.coch.B p) (y : N.coch.X q) (hy : N.coch.d q y = 0) :
    cupCoch b p q x y ∈ P.coch.B (p + q) := by
  rcases p with _ | p
  · have h0 : x = 0 := (Submodule.mem_bot R).1 hx
    subst h0
    rw [map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · obtain ⟨u, rfl⟩ := hx
    have hy' : dn N.rho q y.1 = 0 := congrArg Subtype.val hy
    refine mem_coboundaries_of_eq_d (by omega) _ (cupCoch b p q u y) fun g => ?_
    rw [cupCoch_val, cupCoch_val, cochain_differential_val, cupProduct_leibniz, hy']
    simp [cupFun]

theorem cupProduct_coboundary_right {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p)
    (hx : M.coch.d p x = 0) (y : N.coch.X q) (hy : y ∈ N.coch.B q) :
    cupCoch b p q x y ∈ P.coch.B (p + q) := by
  rcases q with _ | q
  · have h0 : y = 0 := (Submodule.mem_bot R).1 hy
    subst h0
    rw [map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨v, rfl⟩ := hy
    have hx' : dn M.rho p x.1 = 0 := congrArg Subtype.val hx
    refine mem_coboundaries_of_eq_d (n := p + q) rfl _ ((-1 : R) ^ p • cupCoch b p q x v) fun g => ?_
    rw [cupCoch_val, cochain_differential_val, cochain_smul_val, cupCoch_val, map_smul, Pi.smul_apply, cupProduct_leibniz, hx']
    simp only [cupFun, Pi.zero_apply, map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← mul_pow,
      mul_neg_one, neg_neg, one_pow, one_smul]
    rfl

end S3

section S4
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem cupProduct_cocycle {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) (x : M.coch.X p)
    (hx : M.coch.d p x = 0) (y : N.coch.X q) (hy : N.coch.d q y = 0) :
    P.coch.d (p + q) (cupCoch b p q x y) = 0 := by
  have hx' : dn M.rho p x.1 = 0 := congrArg Subtype.val hx
  have hy' : dn N.rho q y.1 = 0 := congrArg Subtype.val hy
  refine Subtype.ext (funext fun g => ?_)
  rw [cochain_differential_val, cupCoch_val, cupProduct_leibniz, hx', hy', cochain_zero_val]
  simp [cupFun]

def cupCocyc {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) :
    M.coch.Z p →ₗ[R] N.coch.Z q →ₗ[R] P.coch.Z (p + q) :=
  LinearMap.mk₂ R (fun x y => ⟨cupCoch b p q x.1 y.1,
      LinearMap.mem_ker.2 (cupProduct_cocycle b p q x.1 (LinearMap.mem_ker.1 x.2) y.1 (LinearMap.mem_ker.1 y.2))⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))
    (fun x y y' => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))

def cupCoh {M N P : TRep R G} (b : Pairing M N P) (p q : ℕ) : M.H p →ₗ[R] N.H q →ₗ[R] P.H (p + q) :=
  LinearMap.liftQ₂ _ _ ((cupCocyc b p q).compr₂ (Submodule.mkQ _))
    (fun x hx => LinearMap.mem_ker.2 (LinearMap.ext fun y => by
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact cupProduct_coboundary_left b p q x.1 hx y.1 (LinearMap.mem_ker.1 y.2)))
    (fun y hy => LinearMap.mem_ker.2 (LinearMap.ext fun x => by
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact cupProduct_coboundary_right b p q x.1 (LinearMap.mem_ker.1 x.2) y.1 hy))

theorem cupCoh_isCup {M N P : TRep R G} (b : Pairing M N P) : IsCup b (cupCoh b) := by
  intro p q x y hx hy
  exact ⟨cupCoch b p q x y, cupProduct_cocycle b p q x hx y hy, rfl, rfl⟩

end S4

section S5

end S5

end

end ReciprocityTheory.Coh
end
