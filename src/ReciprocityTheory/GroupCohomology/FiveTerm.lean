module

public import ReciprocityTheory.GroupCohomology.InfRes

@[expose] public section

section -- merged from ReciprocityTheory.GroupCohomology.Transgression
section -- merged from ReciprocityTheory.GroupCohomology.TransgressionB
section -- merged from ReciprocityTheory.GroupCohomology.TransgressionA
namespace ReciprocityTheory.Coh.InflationTransgression

open ReciprocityTheory.Gal ReciprocityTheory.Coh

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_cont_select {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {Y : Type u} [TopologicalSpace Y] [DiscreteTopology Y] [Nonempty Y]
    (P : X → Y → Prop) (hP : ∀ y, IsOpen {x | P x y}) (hex : ∀ x, ∃ y, P x y) :
    ∃ ψ : X → Y, Continuous ψ ∧ ∀ x, P x (ψ x) := by
  classical
  have hb : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} := by
    first
      | exact isTopologicalBasis_isClopen
      | exact isTopologicalBasis_clopen
  choose yx hyx using hex
  have hnb : ∀ x, ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ C ⊆ {x' | P x' (yx x)} := by
    intro x
    obtain ⟨C, hC, hxC, hCs⟩ := hb.exists_subset_of_mem_open (hyx x) (hP (yx x))
    exact ⟨C, hC, hxC, hCs⟩
  choose C hCc hxC hCs using hnb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover C (fun x => (hCc x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxC x⟩)
  have key : ∀ s : Finset X, ∃ ψ : X → Y, Continuous ψ ∧ ∀ x ∈ s, ∀ z ∈ C x, P z (ψ z) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨fun _ => Classical.arbitrary Y, continuous_const, by simp⟩
    · intro a s _ ih
      obtain ⟨ψ, hψc, hψ⟩ := ih
      refine ⟨fun z => if z ∈ C a then yx a else ψ z, ?_, ?_⟩
      · apply continuous_if
        · intro x hx
          have hfr : frontier {x | x ∈ C a} = ∅ := (hCc a).frontier_eq
          rw [hfr] at hx
          simp at hx
        · exact continuous_const.continuousOn
        · exact hψc.continuousOn
      · intro x hx z hz
        by_cases hza : z ∈ C a
        · dsimp only
          rw [if_pos hza]
          exact hCs a hza
        · dsimp only
          rw [if_neg hza]
          rcases Finset.mem_insert.1 hx with rfl | hx'
          · exact absurd hz hza
          · exact hψ x hx' z hz
  obtain ⟨ψ, hψc, hψ⟩ := key t
  refine ⟨ψ, hψc, fun z => ?_⟩
  obtain ⟨x, hx, hz⟩ : ∃ x ∈ t, z ∈ C x := by simpa using ht (Set.mem_univ z)
  exact hψ x hx z hz

def cj (N : Subgroup G) [N.Normal] (s : G) (n : N) : N :=
  ⟨s⁻¹ * n * s, by simpa using (inferInstance : N.Normal).conj_mem n n.2 s⁻¹⟩

@[simp] theorem cj_coe (N : Subgroup G) [N.Normal] (s : G) (n : N) : (cj N s n : G) = s⁻¹ * n * s := rfl

theorem isOpen_setOf_conj_eq (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal]
    (hNc : IsClosed (N : Set G)) [CompactSpace G] (f : N → M.V) (hf : Continuous f) (m : M.V) :
    IsOpen {s : G | ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m} := by
  have hact : Continuous (fun q : G × M.V => M.rho q.1 q.2) := M.cont
  haveI : CompactSpace N := isCompact_iff_compactSpace.mp hNc.isCompact
  have hcj : Continuous (fun p : G × N => cj N p.1 p.2) := by
    apply Continuous.subtype_mk
    exact (continuous_fst.inv.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst
  have hΦ : Continuous (fun p : G × N =>
      M.rho p.1 (f (cj N p.1 p.2)) - f p.2 - (M.rho (p.2 : G) m - m)) := by
    refine ((hact.comp (continuous_fst.prodMk (hf.comp hcj))).sub (hf.comp continuous_snd)).sub ?_
    exact (hact.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)).sub
      continuous_const
  have hO : IsOpen {p : G × N | M.rho p.1 (f (cj N p.1 p.2)) - f p.2 - (M.rho (p.2 : G) m - m) = 0} :=
    hΦ.isOpen_preimage {0} (isOpen_discrete _)
  rw [isOpen_iff_mem_nhds]
  intro s0 hs0
  have hev : ∀ᶠ s in nhds s0, ∀ n ∈ (Set.univ : Set N),
      M.rho s (f (cj N s n)) - f n - (M.rho (n : G) m - m) = 0 := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro n _
    exact hO.mem_nhds (sub_eq_zero.mpr (hs0 n))
  filter_upwards [hev] with s hs n
  exact sub_eq_zero.mp (hs n (Set.mem_univ n))

theorem exists_ext_cochain [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal] (hNc : IsClosed (N : Set G))
    (f : N → M.V) (hf : Continuous f) (hfc : ∀ a b : N, f (a * b) = f a + M.rho a (f b))
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m) :
    ∃ y : G → M.V, Continuous y ∧ (∀ n : N, y n = f n) ∧
      (∀ g (n : N), y (g * n) = y g + M.rho g (f n)) ∧
      (∀ (n : N) g, y (n * g) = f n + M.rho n (y g)) := by
  have : Nonempty M.V := ⟨0⟩
  obtain ⟨ψ, hψc, hψ⟩ := exists_cont_select
    (fun s m => ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m)
    (isOpen_setOf_conj_eq M N hNc f hf) hinv
  obtain ⟨r, hrc, hr1, hr⟩ := groupSection_holds G N hNc
  have hf1 : f 1 = 0 := by
    have e := hfc 1 1
    simp only [mul_one, OneMemClass.coe_one, map_one, Module.End.one_apply] at e
    exact (left_eq_add.1 e)
  have hψ1 : ∀ n : N, M.rho n (ψ 1) = ψ 1 := fun n => by
    have e := hψ 1 n
    have hc : cj N 1 n = n := Subtype.ext (by simp)
    rw [hc, map_one, Module.End.one_apply, sub_self] at e
    exact (sub_eq_zero.1 e.symm)
  have hrσ : ∀ g, r ((r g : G)⁻¹ * g) = 1 := fun g => by
    have e := hr (r g)⁻¹ g
    rw [InvMemClass.coe_inv] at e
    rw [e, inv_mul_cancel]
  set σ : G → G := fun g => (r g : G)⁻¹ * g with hσ
  set y : G → M.V := fun g => f (r g) + M.rho (r g) (ψ (σ g)) - ψ 1 with hy
  have hσn : ∀ (n : N) g, σ (n * g) = σ g := fun n g => by
    simp only [hσ, hr n g, Subgroup.coe_mul, mul_inv_rev]; group
  have h3 : ∀ (n : N) g, y (n * g) = f n + M.rho n (y g) := fun n g => by
    simp only [hy, hσn, hr n g, hfc, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add (f := _),
      map_sub, hψ1]
    abel
  have h2 : ∀ g (n : N), y (g * n) = y g + M.rho g (f n) := fun g n => by
    set t := σ g with ht
    let n'' : N := ⟨t * n * t⁻¹, (inferInstance : N.Normal).conj_mem n n.2 t⟩
    have hg : (r g : G) * t = g := by simp [ht, hσ]
    have e1 : g * n = ((r g * n'' : N) : G) * t := by
      simp only [Subgroup.coe_mul, n'']
      calc g * n = (r g : G) * t * n := by rw [hg]
        _ = _ := by group
    have hrgn : r (g * n) = r g * n'' := by rw [e1, hr, hrσ g, mul_one]
    have hσgn : σ (g * n) = t := by
      show ((r (g * n) : G))⁻¹ * (g * n) = t
      rw [hrgn, e1]; group
    have hc : cj N t n'' = n := Subtype.ext (by simp [n'']; group)
    have e2 := hψ t n''
    rw [hc] at e2
    have e3 : f n'' + M.rho n'' (ψ t) = M.rho t (f n) + ψ t := by
      rw [sub_eq_sub_iff_add_eq_add] at e2
      rw [add_comm (f n''), ← e2]
    have hrg : M.rho g = M.rho (r g) * M.rho t := by rw [← map_mul, hg]
    show f (r (g * n)) + M.rho (r (g * n)) (ψ (σ (g * n))) - ψ 1 = y g + M.rho g (f n)
    rw [hrgn, hσgn, hfc]
    calc _ = f (r g) + M.rho (r g) (f n'' + M.rho n'' (ψ t)) - ψ 1 := by
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add (f := _)]; abel
      _ = f (r g) + M.rho (r g) (M.rho t (f n) + ψ t) - ψ 1 := by rw [e3]
      _ = _ := by rw [map_add (f := _), hrg, Module.End.mul_apply, hy]; simp only [← ht]; abel
  have hy1 : y 1 = 0 := by simp [hy, hr1, hf1, hσ]
  refine ⟨y, ?_, fun n => by simpa [hy1] using h3 n 1, h2, h3⟩
  have hr' : Continuous fun g => (r g : G) := continuous_subtype_val.comp hrc
  exact ((hf.comp hrc).add (M.cont.comp (hr'.prodMk (hψc.comp (hr'.inv.mul continuous_id))))).sub
    continuous_const

def D1 (M : TRep R G) (y : G → M.V) (a b : G) : M.V := M.rho a (y b) - y (a * b) + y a

structure InflD (M : TRep R G) (N : Subgroup G) (D : G → G → M.V) : Prop where
  right : ∀ a b (n : N), D a (b * n) = D a b
  left : ∀ a b (n : N), D (a * n) b = D a b
  inv : ∀ a b (n : N), M.rho n (D a b) = D a b

theorem inflD_of_ext (M : TRep R G) (N : Subgroup G) [N.Normal] (f : N → M.V) (y : G → M.V)
    (h2 : ∀ g (n : N), y (g * n) = y g + M.rho g (f n))
    (h3 : ∀ (n : N) g, y (n * g) = f n + M.rho n (y g)) : InflD M N (D1 M y) := by
  have hc : ∀ (c : G) (n : N), M.rho n (y c) = y c + M.rho c (f (cj N c n)) - f n := by
    intro c n
    have e : (n : G) * c = c * (cj N c n : G) := by rw [cj_coe]; group
    have h := h3 n c
    rw [e, h2] at h
    exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))
  refine ⟨?_, ?_, ?_⟩
  · intro a b n
    simp only [D1]
    rw [h2 b n, ← mul_assoc, h2 (a * b) n]
    simp only [map_add (f := _), map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro a b n
    simp only [D1]
    have e : a * (n : G) * b = a * b * (cj N b n : G) := by rw [cj_coe]; group
    rw [e, h2 (a * b), h2 a n]
    simp only [map_mul, Module.End.mul_apply]
    rw [hc b n]
    simp only [map_add (f := _), map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro a b n
    simp only [D1, map_add (f := _), map_sub]
    rw [hc (a * b) n, hc a n]
    have e : (n : G) * a = a * (cj N a n : G) := by rw [cj_coe]; group
    have e2 : M.rho n (M.rho a (y b)) = M.rho a (M.rho (cj N a n) (y b)) := by
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    have e3 : cj N b (cj N a n) = cj N (a * b) n := by
      apply Subtype.ext
      simp only [cj_coe]
      group
    rw [e2, hc b (cj N a n), e3]
    simp only [map_add (f := _), map_sub, map_mul, Module.End.mul_apply]
    abel

section
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (y : G → M.V) (hy1 : y 1 = 0)
  (hD : InflD M N (D1 M y))
include hy1 hD

theorem inflD_mul_right (a : G) (n : N) : y (a * n) = y a + M.rho a (y n) := by
  have h := hD.right a 1 n
  simp only [D1, one_mul, mul_one, hy1, map_zero] at h
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))

theorem inflD_mul_left (n : N) (a : G) : y (n * a) = y n + M.rho n (y a) := by
  have h := hD.left 1 a n
  simp only [D1, one_mul, hy1, map_one, Module.End.one_apply] at h
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h.symm))

theorem inflD_conj (s : G) (n : N) : M.rho s (y (cj N s n)) - y n = M.rho n (y s) - y s := by
  have h1 := inflD_mul_right M N y hy1 hD s (cj N s n)
  have h2 := inflD_mul_left M N y hy1 hD n s
  have he : s * (cj N s n : G) = (n : G) * s := by rw [cj_coe]; group
  rw [he, h2] at h1
  exact sub_eq_zero.mp (Eq.trans (by abel) (sub_eq_zero.mpr h1.symm))

theorem inflD_of_zero (hz : ∀ n : N, y n = 0) :
    (∀ a (n : N), y (a * n) = y a) ∧ ∀ a (n : N), M.rho n (y a) = y a := by
  refine ⟨fun a n => ?_, fun a n => ?_⟩
  · rw [inflD_mul_right M N y hy1 hD a n, hz, map_zero, add_zero]
  · have h := inflD_conj M N y hy1 hD a n
    simp only [hz, map_zero, sub_zero] at h
    exact sub_eq_zero.mp h.symm

end

end

end ReciprocityTheory.Coh.InflationTransgression
end

namespace ReciprocityTheory.Coh.InflationTransgression

open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def ev1 (M : TRep R G) (N : Subgroup G) (f0 : (M.resSub N).coch.X 1) (n : N) : M.V := f0.1 (e1 n)

def conjN (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) : Pair (M.resSub N) (M.resSub N) where
  φ := { toFun := cj N s
         map_one' := Subtype.ext (by simp)
         map_mul' := fun a b => Subtype.ext (by simp only [cj_coe, Subgroup.coe_mul]; group) }
  u := M.rho s
  φ_cont := Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  u_cont := by
    have h := M.cont.comp (Continuous.prodMk (continuous_const (y := s)) (continuous_id (X := M.V)))
    exact h
  equiv g m := by
    have key : ∀ (g : G) (m : M.V), M.rho s (M.rho (s⁻¹ * g * s) m) = M.rho g (M.rho s m) := by
      intro g m
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
    exact key g m

theorem conj_fix_iff (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) (f0 : (M.resSub N).coch.X 1)
    (hf : (M.resSub N).coch.d 1 f0 = 0) :
    (conjN M N s).hom.H 1 ((M.resSub N).coch.cls 1 f0 hf) = (M.resSub N).coch.cls 1 f0 hf ↔
      ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m := by
  rw [Cx.Hom.H_cls, Cx.cls_eq_iff, mem_oneCoboundaries_iff]
  rfl

theorem pair_fix (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) (c : Pair (M.resSub N) (M.resSub N))
    (hφ : ∀ g, (c.φ g : G) = s⁻¹ * g * s) (hu : ∀ m, c.u m = M.rho s m) (f0 : (M.resSub N).coch.X 1)
    (hf : (M.resSub N).coch.d 1 f0 = 0) (m : M.V)
    (hm : ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    c.hom.H 1 ((M.resSub N).coch.cls 1 f0 hf) = (M.resSub N).coch.cls 1 f0 hf := by
  rw [Cx.Hom.H_cls, Cx.cls_eq_iff, mem_oneCoboundaries_iff]
  refine ⟨m, fun n => ?_⟩
  have he : (fun i => c.φ (e1 n i)) = e1 (cj N s n) := by
    funext i
    exact Subtype.ext (hφ _)
  show c.u (f0.1 fun i => c.φ (e1 n i)) - f0.1 (e1 n) = _
  rw [he, hu]
  exact hm n

section
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP

theorem phi_apply (a : G) : P.φ a = (a : G ⧸ N) := by
  rw [hP.1]
  rfl

theorem hom_f_injective (n : ℕ) : Injective (P.hom.f n) := by
  intro f f' h
  apply Subtype.ext
  funext x
  obtain ⟨g, rfl⟩ : ∃ g : Fin n → G, (fun i => (g i : G ⧸ N)) = x :=
    ⟨fun i => (x i).out, funext fun i => QuotientGroup.out_eq' (x i)⟩
  have h1 : P.u (f.1 fun i => P.φ (g i)) = P.u (f'.1 fun i => P.φ (g i)) := congrArg (fun F => F.1 g) h
  have h2 := hP.2.1.injective h1
  simpa [phi_apply M N Q P hP] using h2

theorem inflation_hom_degree_two_apply (z : Q.coch.X 2) (a b : G) :
    (P.hom.f 2 z).1 ![a, b] = P.u (z.1 ![(a : G ⧸ N), b]) := by
  show P.u (z.1 fun i => P.φ (![a, b] i)) = _
  have e : (fun i => P.φ (![a, b] i)) = ![(a : G ⧸ N), (b : G ⧸ N)] := by
    funext i
    fin_cases i <;> simp [phi_apply M N Q P hP]
  rw [e]

theorem inflation_hom_degree_one_apply (v : Q.coch.X 1) (a : G) :
    (P.hom.f 1 v).1 (e1 a) = P.u (v.1 (e1 (a : G ⧸ N))) := by
  show P.u (v.1 fun i => P.φ (e1 a i)) = _
  have e : (fun i => P.φ (e1 a i)) = e1 (a : G ⧸ N) := by
    funext i
    simp [e1, phi_apply M N Q P hP]
  rw [e]

theorem inflD_of_d (y : M.coch.X 1) (z : Q.coch.X 2) (h : M.coch.d 1 y = P.hom.f 2 z) :
    InflD M N (D1 M fun g => y.1 (e1 g)) := by
  have key : ∀ a b, D1 M (fun g => y.1 (e1 g)) a b = P.u (z.1 ![(a : G ⧸ N), b]) := by
    intro a b
    show M.rho a (y.1 (e1 b)) - y.1 (e1 (a * b)) + y.1 (e1 a) = _
    rw [← oneDifferential_val, h, inflation_hom_degree_two_apply M N Q P hP z a b]
  refine ⟨fun a b n => ?_, fun a b n => ?_, fun a b n => ?_⟩
  · rw [key, key, QuotientGroup.mk_mul_of_mem b n.2]
  · rw [key, key, QuotientGroup.mk_mul_of_mem a n.2]
  · rw [key]
    exact (hP.2.2 _).1 ⟨_, rfl⟩ n n.2

theorem descend1 (w : G → M.V) (hw : Continuous w) (hr : ∀ a (n : N), w (a * n) = w a)
    (hi : ∀ a (n : N), M.rho n (w a) = w a) :
    ∃ v : Q.coch.X 1, ∀ a : G, P.u (v.1 (e1 (a : G ⧸ N))) = w a := by
  letI : Setoid G := QuotientGroup.leftRel N
  have hw' : ∀ a b : G, a ≈ b → w a = w b := by
    intro a b hab
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
    have e := hr a ⟨a⁻¹ * b, hab'⟩
    simp only [mul_inv_cancel_left] at e
    exact e.symm
  let wq : G ⧸ N → M.V := Quotient.lift w hw'
  have hwq : Continuous wq := hw.quotient_lift hw'
  have hmem : ∀ x : G ⧸ N, wq x ∈ LinearMap.range P.u := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a => exact (hP.2.2 (w a)).2 fun g hg => hi a ⟨g, hg⟩
  let v0 : G ⧸ N → Q.V := fun x => (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨wq x, hmem x⟩
  have hv0u : ∀ x, P.u (v0 x) = wq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨wq x, hmem x⟩
    exact congrArg Subtype.val this
  have hv0 : Continuous v0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ v0) = wq := funext hv0u
    rw [e]
    exact hwq
  refine ⟨⟨fun g => v0 (g 0), hv0.comp (continuous_apply 0)⟩, fun a => ?_⟩
  exact hv0u _

theorem descend2 (D : G → G → M.V) (hD : Continuous fun p : G × G => D p.1 p.2) (hI : InflD M N D) :
    ∃ z : Q.coch.X 2, ∀ a b : G, P.u (z.1 ![(a : G ⧸ N), b]) = D a b := by
  have hout : ∀ a b : G, D (Quotient.out (a : G ⧸ N)) (Quotient.out (b : G ⧸ N)) = D a b := by
    intro a b
    obtain ⟨h1, e1'⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨h2, e2'⟩ := QuotientGroup.mk_out_eq_mul N b
    rw [e1', e2', hI.left, hI.right]
  let Dq : (G ⧸ N) × (G ⧸ N) → M.V := fun x => D x.1.out x.2.out
  have hq : Topology.IsQuotientMap (Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N)) :=
    (QuotientGroup.isOpenMap_coe.prodMap QuotientGroup.isOpenMap_coe).isQuotientMap
      (continuous_quot_mk.prodMap continuous_quot_mk)
      (QuotientGroup.mk_surjective.prodMap QuotientGroup.mk_surjective)
  have hDq : Continuous Dq := by
    rw [hq.continuous_iff]
    have e : Dq ∘ Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N) =
        fun p : G × G => D p.1 p.2 := funext fun p => hout p.1 p.2
    rw [e]
    exact hD
  have hmem : ∀ x, Dq x ∈ LinearMap.range P.u := fun x =>
    (hP.2.2 (Dq x)).2 fun g hg => hI.inv _ _ ⟨g, hg⟩
  let z0 : (G ⧸ N) × (G ⧸ N) → Q.V := fun x =>
    (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨Dq x, hmem x⟩
  have hz0u : ∀ x, P.u (z0 x) = Dq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨Dq x, hmem x⟩
    exact congrArg Subtype.val this
  have hz0 : Continuous z0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ z0) = Dq := funext hz0u
    rw [e]
    exact hDq
  refine ⟨⟨fun g => z0 (g 0, g 1), hz0.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩, fun a b => ?_⟩
  show P.u (z0 ((a : G ⧸ N), (b : G ⧸ N))) = D a b
  rw [hz0u]
  exact hout a b

theorem exists_lift [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [DiscreteTopology M.V]
    (hNc : IsClosed (N : Set G)) (f0 : (M.resSub N).coch.X 1) (hf : (M.resSub N).coch.d 1 f0 = 0)
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), M.coch.d 1 y = P.hom.f 2 z ∧
      (Pair.res M N.subtype continuous_subtype_val).hom.f 1 y = f0 := by
  have hfc := (wach_d1_eq_zero_iff (M.resSub N) f0).1 hf
  obtain ⟨y0, hy0c, hy0N, h2, h3⟩ := exists_ext_cochain M N hNc (ev1 M N f0)
    ((show Continuous f0.1 from f0.2).comp (continuous_pi fun _ => continuous_id)) (fun a b => hfc a b) hinv
  have hDc : Continuous fun p : G × G => D1 M y0 p.1 p.2 :=
    ((M.cont.comp (continuous_fst.prodMk (hy0c.comp continuous_snd))).sub
      (hy0c.comp (continuous_fst.mul continuous_snd))).add (hy0c.comp continuous_fst)
  obtain ⟨z, hz⟩ := descend2 M N Q P hP (D1 M y0) hDc (inflD_of_ext M N _ y0 h2 h3)
  let y : M.coch.X 1 := ⟨fun g => y0 (g 0), hy0c.comp (continuous_apply 0)⟩
  have hd : M.coch.d 1 y = P.hom.f 2 z := Subtype.ext (funext fun g => by
    have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rw [hg, oneDifferential_val, inflation_hom_degree_two_apply M N Q P hP, hz]; rfl)
  have hzc : Q.coch.d 2 z = 0 := hom_f_injective M N Q P hP 3 (by
    rw [map_zero, P.hom.comm, ← hd]; exact M.coch.dd 1 y)
  refine ⟨y, z, hzc, hd, Subtype.ext (funext fun g => ?_)⟩
  show y0 (g 0 : G) = f0.1 g
  rw [hy0N]
  exact (oneCochain_apply_fin_one _ f0 g).symm

theorem cls_unique (y y' : M.coch.X 1) (z z' : Q.coch.X 2) (hz : Q.coch.d 2 z = 0)
    (hz' : Q.coch.d 2 z' = 0) (hd : M.coch.d 1 y = P.hom.f 2 z) (hd' : M.coch.d 1 y' = P.hom.f 2 z')
    (hr : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (y - y') ∈ (M.resSub N).coch.B 1) :
    Q.coch.cls 2 z hz = Q.coch.cls 2 z' hz' := by
  obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ n : N, y.1 (e1 (n : G)) - y'.1 (e1 (n : G)) = M.rho n m - m :=
    (mem_oneCoboundaries_iff _ _).1 hr
  obtain ⟨w, hw⟩ : ∃ w : M.coch.X 1, w = y - y' - M.coch.d 0 (const0 M m) := ⟨_, rfl⟩
  have hwv : ∀ a, w.1 (e1 a) = y.1 (e1 a) - y'.1 (e1 a) - (M.rho a m - m) := fun a => by
    rw [hw]
    show y.1 (e1 a) - y'.1 (e1 a) - (M.coch.d 0 (const0 M m)).1 (e1 a) = _
    rw [zeroDifferential_val]; rfl
  have hwN : ∀ n : N, w.1 (e1 n) = 0 := fun n => by
    rw [hwv, hm n, sub_self]
  have hdw : M.coch.d 1 w = P.hom.f 2 (z - z') := by
    rw [hw, map_sub, map_sub, M.coch.dd, sub_zero, hd, hd', map_sub]
  have hI := inflD_of_d M N Q P hP w (z - z') hdw
  have h1 : (fun g => w.1 (e1 g)) 1 = 0 := by
    have e := hwN 1
    rwa [OneMemClass.coe_one] at e
  obtain ⟨hr1, hr2⟩ := inflD_of_zero M N (fun g => w.1 (e1 g)) h1 hI hwN
  obtain ⟨v, hv⟩ := descend1 M N Q P hP (fun g => w.1 (e1 g))
    ((show Continuous w.1 from w.2).comp (continuous_pi fun _ => continuous_id)) hr1 hr2
  have hvw : P.hom.f 1 v = w := Subtype.ext (funext fun g => by
    rw [oneCochain_apply_fin_one M _ g, oneCochain_apply_fin_one M w g, inflation_hom_degree_one_apply M N Q P hP, hv])
  have hdv : Q.coch.d 1 v = z - z' := hom_f_injective M N Q P hP 2 (by rw [P.hom.comm, hvw, hdw])
  rw [cls_eq_iff]
  exact ⟨v, hdv⟩

end

end

end ReciprocityTheory.Coh.InflationTransgression
end

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function InflationRestrictionInvariants InflationTransgression

universe u

theorem transgression_holds : TransgressionStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ N _ hNc Q P hP I hI
  have hE : ∀ x : I, ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), ∃ hy,
      M.coch.d 1 y = P.hom.f 2 z ∧
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy := by
    intro x
    obtain ⟨f0, hf, hx⟩ := exists_cls x.1
    have hinv : ∀ s : G, ∃ m : M.V, ∀ n : N,
        M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m := fun s =>
      (conj_fix_iff M N s f0 hf).1 (by
        rw [← hx]; exact (hI x.1).1 x.2 s (conjN M N s) (fun g => rfl) (fun m => rfl))
    obtain ⟨y, z, hz, hd, hres⟩ := exists_lift M N Q P hP hNc f0 hf hinv
    exact ⟨y, z, hz, by rw [hres]; exact hf, hd, by rw [hx]; exact cls_congr _ _ hres.symm⟩
  choose yf zf hzf hyf hdf hxf using hE
  have key : ∀ (y : M.coch.X 1) (z : Q.coch.X 2) (hz : Q.coch.d 2 z = 0) hy (x : I),
      M.coch.d 1 y = P.hom.f 2 z →
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy →
      Q.coch.cls 2 (zf x) (hzf x) = Q.coch.cls 2 z hz := by
    intro y z hz hy x hd hx
    apply cls_unique M N Q P hP _ _ _ _ _ _ (hdf x) hd
    rw [map_sub, ← cls_eq_iff (hyf x) hy, ← hxf x, ← hx]
  let T : I → Q.H 2 := fun x => Q.coch.cls 2 (zf x) (hzf x)
  have hadd : ∀ x x' : I, T (x + x') = T x + T x' := fun x x' => by
    have hy : (M.resSub N).coch.d 1
        ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x + yf x')) = 0 := by
      rw [map_add (f := _)]; exact d_add_eq_zero (hyf x) (hyf x')
    refine (key (yf x + yf x') (zf x + zf x') (d_add_eq_zero (hzf x) (hzf x')) hy (x + x')
      (by rw [map_add (f := _), map_add (f := _), hdf, hdf]) ?_).trans rfl
    rw [Submodule.coe_add, hxf x, hxf x', cls_add]
    exact cls_congr _ _ (map_add _ _ _).symm
  have hsmul : ∀ (r : R) (x : I), T (r • x) = r • T x := fun r x => by
    have hy : (M.resSub N).coch.d 1
        ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (r • yf x)) = 0 := by
      rw [map_smul]; exact d_smul_eq_zero r (hyf x)
    refine (key (r • yf x) (r • zf x) (d_smul_eq_zero r (hzf x)) hy (r • x)
      (by rw [map_smul, map_smul, hdf]) ?_).trans rfl
    rw [Submodule.coe_smul, hxf x, cls_smul]
    exact cls_congr _ _ (map_smul _ _ _).symm
  let tg : I →ₗ[R] Q.H 2 := { toFun := T, map_add' := hadd, map_smul' := hsmul }
  refine ⟨tg, fun y z hz hy x hd hx => key y z hz hy x hd hx,
    fun x => ⟨yf x, zf x, hzf x, hyf x, hdf x, hxf x⟩, ?_, ?_⟩
  · intro x
    constructor
    · intro h0
      change Q.coch.cls 2 (zf x) (hzf x) = 0 at h0
      rw [cls_eq_zero_iff] at h0
      obtain ⟨v, hv⟩ := mem_B_succ.1 h0
      have hd' : M.coch.d 1 (yf x - P.hom.f 1 v) = 0 := by
        rw [map_sub, hdf, ← P.hom.comm, hv, sub_self]
      refine ⟨M.coch.cls 1 _ hd', ?_⟩
      rw [Hom.H_cls, hxf x]
      apply cls_congr
      have hc : (M.resSub N).coch.d 1
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)) = 0 := by
        have e : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) =
            (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x) -
              (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (yf x - P.hom.f 1 v) := by
          rw [map_sub, sub_sub_cancel]
        rw [e]
        exact d_sub_eq_zero (hyf x) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hd')
      have h1 := cocycle_one (M.resSub N) _ hc
      have hconst : ∀ g : Fin 1 → N,
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 g =
            ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v)).1 (e1 1) := fun g => by
        show P.u (v.1 fun i => P.φ (g i : G)) = P.u (v.1 fun _ => P.φ ((1 : N) : G))
        have e : ∀ i, P.φ (g i : G) = 1 := fun i => by
          rw [phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]
        simp only [e, OneMemClass.coe_one, map_one]
      have h0' : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (P.hom.f 1 v) = 0 :=
        Subtype.ext (funext fun g => by rw [hconst, h1]; rfl)
      rw [map_sub, h0', sub_zero]
    · rintro ⟨c, hc⟩
      obtain ⟨c0, hc0, rfl⟩ := exists_cls c
      change Q.coch.cls 2 (zf x) (hzf x) = 0
      rw [key c0 0 (map_zero _) ((Pair.res M N.subtype continuous_subtype_val).hom.d_f_eq_zero hc0) x
        (by rw [hc0, map_zero]) (by rw [← hc, Hom.H_cls])]
      rfl
  · intro w
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ := exists_cls w
      rw [Hom.H_cls, cls_eq_zero_iff] at hw
      obtain ⟨y, hy⟩ := mem_B_succ.1 hw
      let q : Q.V := z.1 ![1, 1]
      let vq : Q.coch.X 1 := ⟨fun _ => q, continuous_const⟩
      obtain ⟨z', hz'e⟩ : ∃ z', z' = z - Q.coch.d 1 vq := ⟨_, rfl⟩
      obtain ⟨y', hy'e⟩ : ∃ y', y' = y - P.hom.f 1 vq := ⟨_, rfl⟩
      have hz'c : Q.coch.d 2 z' = 0 := by rw [hz'e, map_sub, hz, Q.coch.dd, sub_zero]
      have hd' : M.coch.d 1 y' = P.hom.f 2 z' := by
        rw [hy'e, hz'e, map_sub, map_sub, hy, P.hom.comm]
      have hz'1 : z'.1 ![1, 1] = 0 := by
        rw [hz'e]
        show z.1 ![1, 1] - (Q.coch.d 1 vq).1 ![1, 1] = 0
        rw [oneDifferential_val]
        show q - (Q.rho 1 q - q + q) = 0
        simp
      have hres : (M.resSub N).coch.d 1
          ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y') = 0 := by
        rw [← (Pair.res M N.subtype continuous_subtype_val).hom.comm 1 y', hd']
        refine Subtype.ext (funext fun g => ?_)
        show P.u (z'.1 fun i => P.φ (g i : G)) = 0
        have e : (fun i => P.φ (g i : G)) = ![1, 1] := funext fun i => by
          rw [phi_apply M N Q P hP, (QuotientGroup.eq_one_iff _).2 (g i).2]
          fin_cases i <;> rfl
        rw [e, hz'1, map_zero]
      have hy'1 : (fun g => y'.1 (e1 g)) 1 = 0 := cocycle_one (M.resSub N) _ hres
      have hID := inflD_of_d M N Q P hP y' z' hd'
      have hmem : (M.resSub N).coch.cls 1 _ hres ∈ I := by
        rw [hI]
        intro s c hφ hu
        exact pair_fix M N s c hφ hu _ hres (y'.1 (e1 s)) (fun n => inflD_conj M N _ hy'1 hID s n)
      refine ⟨⟨_, hmem⟩, ?_⟩
      show Q.coch.cls 2 (zf _) (hzf _) = Q.coch.cls 2 z hz
      rw [key y' z' hz'c hres ⟨_, hmem⟩ hd' rfl, cls_eq_iff]
      exact ⟨-vq, by rw [hz'e, map_neg]; abel⟩
    · rintro ⟨x, rfl⟩
      show P.hom.H 2 (Q.coch.cls 2 (zf x) (hzf x)) = 0
      rw [Hom.H_cls, cls_eq_zero_iff]
      exact ⟨yf x, hdf x⟩

end ReciprocityTheory.Coh
end

namespace ReciprocityTheory.Coh

universe u

theorem fiveTerm_holds : FiveTermStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ N _ hN Q P hP I hI
  obtain ⟨tg, -, -, h₁, h₂⟩ := transgression_holds R G M N hN Q P hP I hI
  exact ⟨tg, h₁, h₂⟩

end ReciprocityTheory.Coh
