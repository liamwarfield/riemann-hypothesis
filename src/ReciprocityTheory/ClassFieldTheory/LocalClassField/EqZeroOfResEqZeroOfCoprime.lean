module

public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.Shapiro

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.SubsingletonHOfSubsingleton
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.HomFInjective
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.CurriedCoboundaryEq
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.IsTwoCocycleCoboundary
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

section Alg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)

def IsTwoCocycle (c : G → G → A) : Prop := ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0

def D1 (y : G → A) (g h : G) : A := ρ g (y h) - y (g * h) + y g

variable {ρ}

variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)

include hrs hr in
theorem s_mem {n : G} (hn : n ∈ N) : s n ∈ N := by
  have h : s n = (r n)⁻¹ * n := by rw [eq_inv_mul_iff_mul_eq, hrs]
  rw [h]; exact N.mul_mem (N.inv_mem (hr n)) hn


include hc hrs hr hrn hsn in
theorem stepA (h0 : ∀ n ∈ N, ∀ m ∈ N, c n m = 0) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => - c (r x) (s x)) n g = 0 := by
  have h1 := hc n (r g) (s g)
  rw [hrs, h0 n hn _ (hr g)] at h1
  simp only [D1]
  rw [hrn n hn, hsn n hn, h0 _ (hr n) _ (s_mem hrs hr hn), map_neg]
  linear_combination (norm := abel) h1

include hc in
theorem mul_left_of_zero (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (n : G) (hn : n ∈ N) (g h : G) :
    c (n * g) h = ρ n (c g h) := by
  have h1 := hc n g h
  rw [h0 n hn, h0 n hn] at h1
  linear_combination (norm := abel) - h1

include hc in
theorem theta_mul [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (g m : G) (hm : m ∈ N) (k : G) :
    c g (m * k) = c g m + ρ (g * m * g⁻¹) (c g k) := by
  have h1 := hc g m k
  have h2 := mul_left_of_zero hc h0 (g * m * g⁻¹) (‹N.Normal›.conj_mem m hm g) g k
  rw [inv_mul_cancel_right] at h2
  rw [h0 m hm, map_zero, h2] at h1
  linear_combination (norm := abel) h1


include hc hrs hr hrn hsn in
theorem stepB [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (e : G → A) (he0 : ∀ g ∈ N, e g = 0)
    (he : ∀ g, ∀ n ∈ N, c g (g⁻¹ * n * g) = e g - ρ n (e g)) (n : G) (hn : n ∈ N) (g : G) :
    c n g - D1 ρ (fun x => ρ (r x) (e (s x))) n g = 0 ∧ c g n - D1 ρ (fun x => ρ (r x) (e (s x))) g n = 0 := by
  have ha0 : ρ (r n) (e (s n)) = 0 := by rw [he0 _ (s_mem hrs hr hn), map_zero]
  constructor
  · simp only [D1]
    rw [hrn n hn, hsn n hn, ha0, h0 n hn, map_mul, Module.End.mul_apply]
    abel
  · simp only [D1]
    have hconj : g * n * g⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn g
    have h1 : g * n = (g * n * g⁻¹) * g := by group
    have h2 : c g n = ρ (r g) (e (s g)) - ρ (g * n * g⁻¹) (ρ (r g) (e (s g))) := by
      have h3 : c g n = ρ (r g) (c (s g) n) := by
        conv_lhs => rw [← hrs g]
        exact mul_left_of_zero hc h0 _ (hr g) _ _
      have h4 := he (s g) (s g * n * (s g)⁻¹) (‹N.Normal›.conj_mem n hn _)
      have h5 : (s g)⁻¹ * (s g * n * (s g)⁻¹) * s g = n := by group
      rw [h5] at h4
      rw [h3, h4, map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      have key : ∀ a b : G, a * (b * n * b⁻¹) = (a * b) * n * (a * b)⁻¹ * a := by intros; group
      have key' := key (r g) (s g)
      rw [hrs] at key'
      rw [key']
    rw [ha0, map_zero, h1, hrn _ hconj, hsn _ hconj, h2, map_mul ρ (g * n * g⁻¹) (r g), Module.End.mul_apply]
    abel


include hc in
theorem stepC [N.Normal] (h0 : ∀ n ∈ N, ∀ g, c n g = 0) (h0' : ∀ n ∈ N, ∀ g, c g n = 0) (n : G) (hn : n ∈ N)
    (g h : G) : c g (h * n) = c g h ∧ c (g * n) h = c g h ∧ ρ n (c g h) = c g h := by
  have hR : ∀ g h n, n ∈ N → c g (h * n) = c g h := fun g h n hn => by
    have h1 := hc g h n
    simp only [h0' n hn, map_zero, zero_sub, sub_zero] at h1
    linear_combination (norm := abel) h1
  have hL : ∀ g h n, n ∈ N → c g (n * h) = c g h := fun g h n hn => by
    have : n * h = h * (h⁻¹ * n * h) := by group
    rw [this, hR _ _ _ (‹N.Normal›.conj_mem' n hn h)]
  have hM : ∀ g h n, n ∈ N → c (g * n) h = c g h := fun g h n hn => by
    have h1 := hc g n h
    simp only [h0 n hn, h0' n hn, map_zero, hL _ _ _ hn, zero_sub, sub_zero] at h1
    linear_combination (norm := abel) - h1
  refine ⟨hR g h n hn, hM g h n hn, ?_⟩
  rw [← mul_left_of_zero hc h0 n hn]
  have : n * g = g * (g⁻¹ * n * g) := by group
  rw [this, hM _ _ _ (‹N.Normal›.conj_mem' n hn g)]

end Alg

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cur (M : TRep R G) (x : M.coch.X 2) (g h : G) : M.V := x.1 ![g, h]

theorem cur_sub (M : TRep R G) (x x' : M.coch.X 2) (g h : G) :
    cur M (x - x') g h = cur M x g h - cur M x' g h := rfl

theorem isTwoCocycle_curried (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) : IsTwoCocycle M.rho (cur M x) := by
  intro g h k
  have := congrFun (LowDeg.dn_eq_zero M hx) ![g, h, k]
  rw [LowDeg.dn_two_apply] at this
  exact this

theorem ext2 (M : TRep R G) {x x' : M.coch.X 2} (h : ∀ g h, cur M x g h = cur M x' g h) : x = x' := by
  refine Subtype.ext (funext fun v => ?_)
  have hv : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [hv]; exact h _ _

theorem continuous_cur (M : TRep R G) (x : M.coch.X 2) {X : Type*} [TopologicalSpace X] {f h : X → G}
    (hf : Continuous f) (hh : Continuous h) : Continuous fun t => cur M x (f t) (h t) := by
  refine (show Continuous x.1 from x.2).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact hf
  · exact hh

def mk1 (M : TRep R G) (y : G → M.V) (hy : Continuous y) : M.coch.X 1 :=
  ⟨fun v => y (v 0), hy.comp (continuous_apply 0)⟩

theorem curried_coboundary_eq (M : TRep R G) (y : G → M.V) (hy : Continuous y) (g h : G) :
    cur M (M.coch.d 1 (mk1 M y hy)) g h = D1 M.rho y g h := oneDifferential_val M _ g h

theorem d_sub_d (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) (w : M.coch.X 1) :
    M.coch.d 2 (x - M.coch.d 1 w) = 0 := by
  rw [map_sub, hx, M.coch.dd, sub_zero]

theorem continuous_comp_rep (U : Subgroup G) (hU : IsOpen (U : Set G)) {Y : Type*} [TopologicalSpace Y]
    (e : G → Y) : Continuous fun g => e (rep U g) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hn : (fun y => y * x⁻¹) ⁻¹' (U : Set G) ∈ nhds x := by
    refine (hU.preimage (continuous_mul_const _)).mem_nhds ?_
    simp [U.one_mem]
  refine (continuousAt_const (y := e (rep U x))).congr ?_
  filter_upwards [hn] with y hy
  have : y = ((⟨y * x⁻¹, hy⟩ : U) : G) * x := by simp
  rw [this, rep_mul]

variable (M : TRep R G) (N : Subgroup G)

theorem retr_mul_rep (g : G) : (retr N g : G) * rep N g = g := by simp [retr_spec]

theorem retr_mul' (n : G) (hn : n ∈ N) (g : G) : (retr N (n * g) : G) = n * retr N g :=
  congrArg Subtype.val (retr_mul N ⟨n, hn⟩ g)

theorem rep_mul' (n : G) (hn : n ∈ N) (g : G) : rep N (n * g) = rep N g := rep_mul N ⟨n, hn⟩ g

theorem continuous_retr' (hN : IsOpen (N : Set G)) : Continuous fun g => (retr N g : G) :=
  continuous_subtype_val.comp (continuous_retr N hN)

theorem norm0 (hN : IsOpen (N : Set G)) (x : M.coch.X 2)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ m ∈ N, cur M (x - M.coch.d 1 w) n m = 0 := by
  obtain ⟨y, hy⟩ := (memB _).1 hres
  have hc : Continuous fun g : G => (y.1 (e1 (retr N g * (retr N 1)⁻¹)) : M.V) :=
    (show Continuous y.1 from y.2).comp
      (continuous_pi fun _ => (continuous_retr N hN).mul continuous_const)
  have hval : ∀ n : N, retr N (n : G) * (retr N 1)⁻¹ = n := fun n => by
    have := retr_mul N n 1
    rw [mul_one] at this
    rw [this, mul_inv_cancel_right]
  obtain ⟨Y, hYc, hYv⟩ : ∃ Y : G → M.V, Continuous Y ∧ ∀ n : N, Y n = y.1 (e1 n) :=
    ⟨fun g => y.1 (e1 (retr N g * (retr N 1)⁻¹)), hc, fun n => by
      show y.1 (e1 (retr N (n : G) * (retr N 1)⁻¹)) = _
      rw [hval]⟩
  refine ⟨mk1 M Y hYc, fun n hn m hm => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  have h1 := oneDifferential_val (M.resSub N) y ⟨n, hn⟩ ⟨m, hm⟩
  rw [hy] at h1
  have h2 : ((Pair.res M N.subtype continuous_subtype_val).hom.f 2 x).1 ![⟨n, hn⟩, ⟨m, hm⟩] = cur M x n m := by
    refine congrArg x.1 (funext fun i => ?_)
    fin_cases i <;> rfl
  rw [h2] at h1
  rw [h1]
  simp only [D1]
  have e1' : Y n = y.1 (e1 ⟨n, hn⟩) := hYv ⟨n, hn⟩
  have e2' : Y m = y.1 (e1 ⟨m, hm⟩) := hYv ⟨m, hm⟩
  have e3' : Y (n * m) = y.1 (e1 (⟨n, hn⟩ * ⟨m, hm⟩)) := hYv (⟨n, hn⟩ * ⟨m, hm⟩)
  rw [e1', e2', e3']
  exact sub_self _

theorem normA (hN : IsOpen (N : Set G)) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ m ∈ N, cur M x n m = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 := by
  have hc : Continuous fun g : G => - cur M x (retr N g) (rep N g) :=
    (continuous_cur M x (continuous_retr' N hN) (continuous_rep N hN)).neg
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  exact stepA (isTwoCocycle_curried M x hx) (retr_mul_rep N)
    (fun g => (retr N g).property) (retr_mul' N) (rep_mul' N) h0 n hn g

theorem normB [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0) (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  have hC := isTwoCocycle_curried M x hx
  have hex : ∀ g : G, ∃ e : M.V, (g ∈ N → e = 0) ∧
      ∀ n ∈ N, cur M x g (g⁻¹ * n * g) = e - M.rho n e := by
    intro g
    by_cases hg : g ∈ N
    · exact ⟨0, fun _ => rfl, fun n _ => by rw [h0 g hg, map_zero, sub_zero]⟩
    · let θ : (M.resSub N).coch.X 1 := ⟨fun v => cur M x g (g⁻¹ * (v 0 : G) * g),
        continuous_cur M x continuous_const
          ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply 0))).mul continuous_const)⟩
      have hθ : (M.resSub N).coch.d 1 θ = 0 := by
        rw [wach_d1_eq_zero_iff]
        intro a b
        show cur M x g (g⁻¹ * ((a * b : N) : G) * g) =
          cur M x g (g⁻¹ * (a : G) * g) + M.rho (a : G) (cur M x g (g⁻¹ * (b : G) * g))
        have e1 : g⁻¹ * ((a * b : N) : G) * g = (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g) := by
          rw [Subgroup.coe_mul]; group
        rw [e1, theta_mul hC h0 g _ (Subgroup.Normal.conj_mem' ‹_› _ a.2 g)]
        congr 3
        group
      have hz : (Submodule.Quotient.mk ⟨θ, (memZ _).2 hθ⟩ : (M.resSub N).H 1) = 0 := Subsingleton.elim _ _
      rw [mk_eq_zero_iff, mem_oneCoboundaries_iff] at hz
      obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ a : N, cur M x g (g⁻¹ * (a : G) * g) = M.rho (a : G) m - m := hz
      refine ⟨-m, fun h => absurd h hg, fun n hn => ?_⟩
      have h' : cur M x g (g⁻¹ * n * g) = M.rho n m - m := hm ⟨n, hn⟩
      rw [h', map_neg]; abel
  choose e he0 he using hex
  have hc : Continuous fun g : G => M.rho (retr N g : G) (e (rep N g)) :=
    M.cont.comp (f := fun g : G => ((retr N g : G), e (rep N g)))
      ((continuous_retr' N hN).prodMk (continuous_comp_rep N hN e))
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq, cur_sub, curried_coboundary_eq]
  exact stepB hC (retr_mul_rep N) (fun g => (retr N g).property)
    (retr_mul' N) (rep_mul' N) h0 e he0 he n hn g

theorem norm_all [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  obtain ⟨w0, h0⟩ := norm0 M N hN x hres
  obtain ⟨w1, hA⟩ := normA M N hN _ (d_sub_d M x hx w0) h0
  obtain ⟨w2, hB⟩ := normB M N hN h1 _ (d_sub_d M _ (d_sub_d M x hx w0) w1) hA
  refine ⟨w0 + w1 + w2, ?_⟩
  have : x - M.coch.d 1 (w0 + w1 + w2) = x - M.coch.d 1 w0 - M.coch.d 1 w1 - M.coch.d 1 w2 := by
    rw [map_add (f := _), map_add (f := _)]; abel
  rw [this]
  exact hB

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem hom_f_injective {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : Surjective P.φ) (hu : Injective P.u) (n : ℕ) :
    Injective (P.hom.f n) := by
  intro t t' h
  refine Subtype.ext (funext fun v => ?_)
  choose v' hv' using fun i => hφ (v i)
  have := congrFun (congrArg Subtype.val h) v'
  have h2 : P.u (t.1 fun i => P.φ (v' i)) = P.u (t'.1 fun i => P.φ (v' i)) := this
  have h3 : (fun i => P.φ (v' i)) = v := funext hv'
  rw [h3] at h2
  exact hu h2

variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)

theorem cur_inf (hP : IsInvRep M N Q P) (z : Q.coch.X 2) (g h : G) :
    cur M (P.hom.f 2 z) g h = P.u (cur Q z (g : G ⧸ N) (h : G ⧸ N)) := by
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hP.1]; rfl
  show P.u (z.1 _) = P.u (z.1 _)
  refine congrArg (fun v => P.u (z.1 v)) (funext fun i => ?_)
  fin_cases i
  · exact hφa g
  · exact hφa h

theorem phi_surjective (hP : IsInvRep M N Q P) : Surjective P.φ := by
  rw [hP.1]; exact QuotientGroup.mk'_surjective N

theorem descend2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0 ∧ cur M x g n = 0) :
    ∃ z : Q.coch.X 2, Q.coch.d 2 z = 0 ∧ P.hom.f 2 z = x := by
  have : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  have hC := fun n hn g h => stepC (ρ := M.rho) (N := N) (c := cur M x)
    (isTwoCocycle_curried M x hx)
    (fun n hn g => (h0 n hn g).1) (fun n hn g => (h0 n hn g).2)
    n hn g h
  have hmem : ∀ g h, ∃ q, P.u q = cur M x g h := fun g h => (hP.2.2 _).2 fun n hn => (hC n hn g h).2.2
  choose F0 hF0 using hmem
  let z : Q.coch.X 2 := ⟨fun v => F0 (v 0).out (v 1).out, continuous_of_discreteTopology⟩
  have hz : P.hom.f 2 z = x := by
    refine ext2 M fun g h => ?_
    rw [cur_inf M N Q P hP]
    show P.u (F0 (g : G ⧸ N).out (h : G ⧸ N).out) = _
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul N g
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul N h
    rw [hF0, ha, hb, (hC _ a.2 _ _).2.1, (hC _ b.2 _ _).1]
  refine ⟨z, ?_, hz⟩
  apply hom_f_injective P (phi_surjective M N Q P hP) hP.2.1.injective 3
  rw [P.hom.comm, hz, hx, map_zero]

theorem exact2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((Pair.res M N.subtype continuous_subtype_val).hom.H 2) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [H_mk, mk_eq_zero_iff] at hy
    have hx := (memZ _).1 x.2
    obtain ⟨w, hw⟩ := norm_all M N hN h1 x.1 hx hy
    obtain ⟨z, hz, hzx⟩ := descend2 M N Q P hN hP _ (d_sub_d M x.1 hx w) hw
    refine ⟨Submodule.Quotient.mk ⟨z, (memZ _).2 hz⟩, ?_⟩
    rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap]
    show P.hom.f 2 z - x.1 ∈ M.coch.B 2
    rw [hzx, memB]
    exact ⟨-w, by rw [map_neg]; abel⟩
  · rintro ⟨y0, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y0
    rw [H_mk, H_mk, mk_eq_zero_iff, memB]
    have hinv : ∀ n ∈ N, M.rho n (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1) := (hP.2.2 _).1 ⟨_, rfl⟩
    refine ⟨mk1 (M.resSub N) (fun _ => P.u (cur Q z.1 1 1)) continuous_const, ?_⟩
    refine ext2 (M.resSub N) fun a b => ?_
    refine (curried_coboundary_eq (M.resSub N) _ continuous_const a b).trans ?_
    have e : cur (M.resSub N) ((Pair.res M N.subtype continuous_subtype_val).hom.Z 2 (P.hom.Z 2 z)).1 a b =
        cur M (P.hom.f 2 z.1) a b := by
      refine congrArg (P.hom.f 2 z.1).1 (funext fun i => ?_)
      fin_cases i <;> rfl
    rw [e, cur_inf M N Q P hP, (QuotientGroup.eq_one_iff _).2 a.2, (QuotientGroup.eq_one_iff _).2 b.2]
    simp only [D1]
    have := hinv a a.2
    have h' : (M.resSub N).rho a (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1) := this
    rw [h']; abel

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

theorem pair_bij {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : IsHomeomorph P.φ)
    (hu : IsHomeomorph P.u) (n : ℕ) : Bijective (P.hom.H n) := by
  refine shp_qi_of_bij P.hom (fun n => ⟨hom_f_injective P hφ.surjective hu.injective n, fun t' => ?_⟩) n
  let eφ := IsHomeomorph.homeomorph _ hφ
  let eu := IsHomeomorph.homeomorph _ hu
  have hc : Continuous fun v : Fin n → G => eu.symm (t'.1 fun i => eφ.symm (v i)) :=
    eu.symm.continuous.comp ((show Continuous t'.1 from t'.2).comp
      (continuous_pi fun i => eφ.symm.continuous.comp (continuous_apply i)))
  refine ⟨⟨_, hc⟩, Subtype.ext (funext fun g => ?_)⟩
  show eu (eu.symm (t'.1 fun i => eφ.symm (eφ (g i)))) = t'.1 g
  rw [eu.apply_symm_apply]
  exact congrArg t'.1 (funext fun i => eφ.symm_apply_apply (g i))

theorem exists_normal_index {H : Type*} [Group H] [Finite H] [Nontrivial H] (l : ℕ) [hl : Fact l.Prime]
    (hH : IsPGroup l H) : ∃ N : Subgroup H, N.Normal ∧ N.index = l := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hH
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card (α := H)).ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) l (n := j) (by rw [hk]; exact pow_dvd_pow _ (Nat.le_succ j))
  have hidx : K.index = l := by
    have := K.card_mul_index
    rw [hK, hk, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hl.1.pos j) this
  refine ⟨K, Subgroup.normal_of_index_eq_minFac_card ?_, hidx⟩
  rw [hidx, hk, Nat.Prime.pow_minFac hl.1 (Nat.succ_ne_zero j)]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open ReciprocityTheory.Coh Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

abbrev resP (M : TRep R G) (U : Subgroup G) : Pair M (M.resSub U) :=
  Pair.res M U.subtype continuous_subtype_val

theorem pair_H_bijective {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : IsHomeomorph P.φ)
    (hu : IsHomeomorph P.u) (n : ℕ) : Bijective (P.hom.H n) :=
  Deg2.pair_bij P hφ hu n

theorem infRes2_exact (M : TRep R G) (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (Q : TRep R (G ⧸ N)) (P : Pair Q M) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((resP M N).hom.H 2) :=
  Deg2.exact2 M N Q P hN hP h1

theorem exists_normal_index_eq_prime {H : Type*} [Group H] [Finite H] [Nontrivial H] (l : ℕ) [Fact l.Prime]
    (hH : IsPGroup l H) : ∃ N : Subgroup H, N.Normal ∧ N.index = l :=
  Deg2.exists_normal_index l hH

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
