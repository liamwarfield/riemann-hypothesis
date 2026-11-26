module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulMemOfOne
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.FrameMove

section Proj
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  classical
  let q : V →ₗ[𝓞 K] V ⧸ W := W.mkQ.restrictScalars (𝓞 K)
  let Lb : Submodule (𝓞 K) (V ⧸ W) := L.map q
  have hfin : Module.Finite (𝓞 K) Lb := Module.Finite.iff_fg.2 (hfg.map q)
  have hcancel : ∀ (d : 𝓞 K) (x : V ⧸ W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left (by simpa using hd)
  have hflat : Module.Flat (𝓞 K) Lb := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : 𝓞 K) • (x : V ⧸ W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  have hfp : Module.FinitePresentation (𝓞 K) Lb := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 K) Lb := Module.Flat.projective_of_finitePresentation
  let qL : L →ₗ[𝓞 K] Lb := q.submoduleMap L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qL LinearMap.id (LinearMap.submoduleMap_surjective q L)
  have hs' : ∀ y : Lb, q (s y : V) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let p0 : L →ₗ[𝓞 K] V := L.subtype - L.subtype ∘ₗ s ∘ₗ qL
  have hp0 : ∀ x : L, p0 x = (x : V) - s (qL x) := fun x => rfl
  have hden : ∀ v : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
    intro v
    have hv : v ∈ Submodule.span K (L : Set V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  have hunit : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) V) x) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
    refine ⟨hunit, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let P0 : V →ₗ[𝓞 K] V := IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype p0 hunit
  have hP0 : ∀ x : L, P0 (x : V) = p0 x := fun x => IsLocalizedModule.lift_apply _ L.subtype p0 hunit x
  let P : V →ₗ[K] V := P0.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
  have hP : ∀ v, P v = P0 v := fun v => rfl
  have hW : ∀ x : L, p0 x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    change q (p0 x) = 0
    rw [hp0, map_sub, hs']
    exact sub_self _
  refine ⟨P, fun v => ?_, fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨d, hd, hv⟩ := hden v
    rw [← Submodule.Quotient.mk_eq_zero]
    apply hcancel d _ hd
    change d • q (P0 v) = 0
    rw [← map_smul, ← map_smul, show d • v = ((⟨d • v, hv⟩ : L) : V) from rfl, hP0]
    exact (Submodule.Quotient.mk_eq_zero W).2 (hW _)
  · obtain ⟨d, hd, hv⟩ := hden w
    have h0 : qL ⟨d • w, hv⟩ = 0 := by
      apply Subtype.ext
      change q (d • w) = 0
      rw [map_smul]
      change d • (Submodule.Quotient.mk w : V ⧸ W) = 0
      rw [(Submodule.Quotient.mk_eq_zero W).2 hw, smul_zero]
    have h1 : d • P0 w = d • w := by
      rw [← map_smul, show d • w = ((⟨d • w, hv⟩ : L) : V) from rfl, hP0, hp0, h0, map_zero]
      simp
    rw [hP]
    rw [← IsScalarTower.algebraMap_smul K d, ← IsScalarTower.algebraMap_smul K d w] at h1
    exact smul_right_injective V (by simpa using hd) h1
  · rw [hP, show v = ((⟨v, hv⟩ : L) : V) from rfl, hP0, hp0]
    exact L.sub_mem hv (s _).2

end Proj

section Form
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}

theorem exists_rep [FiniteDimensional K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (f : V →ₗ[K] K) : ∃ y, ∀ x, H.B x y = f x := by
  have h1 : (LinearMap.range H.B.flip).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact H.nondeg x fun y => hx _ ⟨y, rfl⟩
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range H.B.flip)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have h3 : f ∈ LinearMap.range H.B.flip := h2 ▸ Submodule.mem_top
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, fun x => by rw [← hy]; rfl⟩

theorem swap_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by rw [← H.herm, h, star_zero]

def Hyp (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (e y : Fin r → V) : Prop :=
  (∀ a b, H.B (e a) (e b) = 0) ∧ (∀ a b, H.B (y a) (y b) = 0) ∧ ∀ a b, H.B (e a) (y b) = if a = b then 1 else 0

theorem Hyp.ye {e y : Fin r → V} (h : Hyp H e y) (a b : Fin r) : H.B (y a) (e b) = if a = b then 1 else 0 := by
  rw [← H.herm, h.2.2]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, Ne.symm hab]

theorem Hyp.pair {e y : Fin r → V} (h : Hyp H e y) (s t s' t' : Fin r → K) {n n' : V}
    (h1 : ∀ a, H.B n (e a) = 0) (h2 : ∀ a, H.B n (y a) = 0) (h3 : ∀ a, H.B n' (e a) = 0) (h4 : ∀ a, H.B n' (y a) = 0) :
    H.B (∑ a, s a • e a + ∑ a, t a • y a + n) (∑ a, s' a • e a + ∑ a, t' a • y a + n') =
      ∑ a, s a * star (t' a) + ∑ a, t a * star (s' a) + H.B n n' := by
  have h3' := fun a => swap_zero (h3 a)
  have h4' := fun a => swap_zero (h4 a)
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_add (f := _), map_sum, LinearMap.add_apply, LinearMap.sum_apply, h.1, h.2.1, h.2.2, h.ye, h1, h2, h3', h4', mul_comm]
  exact add_comm _ _

noncomputable def mid (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (e y : Fin r → V) : V →ₗ[K] V :=
  LinearMap.id - ∑ a, (H.B.flip (y a)).smulRight (e a) - ∑ a, (H.B.flip (e a)).smulRight (y a)

theorem mid_apply (e y : Fin r → V) (v : V) :
    mid H e y v = v - ∑ a, H.B v (y a) • e a - ∑ a, H.B v (e a) • y a := by
  simp [mid]

theorem Hyp.mid_e {e y : Fin r → V} (h : Hyp H e y) (v : V) (a : Fin r) : H.B (mid H e y v) (e a) = 0 := by
  simp [mid_apply, h.1, h.ye]

theorem Hyp.mid_y {e y : Fin r → V} (h : Hyp H e y) (v : V) (a : Fin r) : H.B (mid H e y v) (y a) = 0 := by
  simp [mid_apply, h.2.1, h.2.2]

noncomputable def move (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (e y e' y' : Fin r → V) : V →ₗ[K] V :=
  ∑ a, (H.B.flip (y a)).smulRight (e' a) + ∑ a, (H.B.flip (e a)).smulRight (y' a) + mid H e' y' ∘ₗ mid H e y

theorem move_apply (e y e' y' : Fin r → V) (v : V) :
    move H e y e' y' v = ∑ a, H.B v (y a) • e' a + ∑ a, H.B v (e a) • y' a + mid H e' y' (mid H e y v) := by
  simp [move]

theorem perp_of_span {e : Fin r → V} {v x : V} (h : ∀ a, H.B v (e a) = 0) (hx : x ∈ Submodule.span K (Set.range e)) :
    H.B v x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => simp
  | add x y _ _ h1 h2 => simp [h1, h2]
  | smul a x _ h1 => simp [h1]

theorem move_isom {e y e' y' : Fin r → V} (h : Hyp H e y) (h' : Hyp H e' y')
    (hs : ∀ a, e' a ∈ Submodule.span K (Set.range e)) (v w : V) :
    H.B (move H e y e' y' v) (move H e y e' y' w) = H.B v w := by
  have hd : ∀ u : V, u = ∑ a, H.B u (y a) • e a + ∑ a, H.B u (e a) • y a + mid H e y u := fun u => by
    rw [mid_apply]; abel
  have hp : ∀ u a, H.B (mid H e y u) (e' a) = 0 := fun u a => perp_of_span (h.mid_e u) (hs a)
  have hp' : ∀ u a, H.B (e' a) (mid H e y u) = 0 := fun u a => swap_zero (hp u a)
  have hm : H.B (mid H e' y' (mid H e y v)) (mid H e' y' (mid H e y w)) = H.B (mid H e y v) (mid H e y w) := by
    rw [mid_apply e' y' (mid H e y w)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, LinearMap.map_smulₛₗ, h'.mid_e, h'.mid_y, smul_zero, Finset.sum_const_zero, sub_zero]
    rw [mid_apply e' y' (mid H e y v)]
    simp [hp, hp']
  rw [move_apply, move_apply, h'.pair _ _ _ _ (h'.mid_e _) (h'.mid_y _) (h'.mid_e _) (h'.mid_y _), hm]
  conv_rhs => rw [hd v, hd w]
  rw [h.pair _ _ _ _ (h.mid_e _) (h.mid_y _) (h.mid_e _) (h.mid_y _)]

theorem Hyp.mid_span {e y : Fin r → V} (h : Hyp H e y) {x : V} (hx : x ∈ Submodule.span K (Set.range e)) :
    mid H e y x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; simp [mid_apply, h.1, h.2.2]
  | zero => simp
  | add x y _ _ h1 h2 => simp [h1, h2]
  | smul a x _ h1 => simp [h1]

theorem x_eq_span (F : FlagD H r) : F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
  unfold FlagD.X FlagD.Xa
  congr 1
  ext x
  simp

end Form

section Lat
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}

theorem mem_iff_pair {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ) (x : V) :
    x ∈ Λ ↔ ∀ x' ∈ Λ, H.B x x' ∈ (1 : Submodule (𝓞 K) K) := by
  conv_lhs => rw [← hU.2, mem_dual_iff, hU.1.2]
  simp

theorem mem_lead {F G : FlagD H r} (h : SameGr F G) {Λ : Submodule (𝓞 K) V} (a : Fin (r + 1)) {t : K} {x : V}
    (hx : x ∈ Λ) (ht : x - t • G.e a ∈ G.Xa a.val) : t ∈ lead F Λ a := by
  rw [AdaptInv.xa_eq h] at ht
  have h1 : t • F.e a - x ∈ F.Xa a.val := by
    have := Submodule.neg_mem _ (Submodule.add_mem _ ht (Submodule.smul_mem _ t (h a)))
    convert this using 1
    rw [smul_sub]; abel
  have h2 : x + (t • F.e a - x) ∈ Λ ⊔ rs (𝓞 K) (F.Xa a.val) := Submodule.add_mem_sup hx h1
  simpa [lead] using h2

theorem sum_mem_xa (G : FlagD H r) (n : ℕ) (c : Fin r → K) (hc : ∀ b : Fin r, n ≤ b.val → c b = 0) :
    ∑ b, c b • G.e b.castSucc ∈ G.Xa n := by
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : n ≤ b.val
  · simp [hc b hb]
  · exact Submodule.smul_mem _ _ (AdaptInv.e_mem_xa G b (not_le.1 hb))

theorem coeff_mem (G : FlagD H r) {Λ : Submodule (𝓞 K) V} {aa : Fin r → Submodule (𝓞 K) K}
    (h1 : ∀ (a : Fin r) (t : K), ∀ x ∈ Λ, x - t • G.e a.castSucc ∈ G.Xa a.val → t ∈ aa a)
    (h2 : ∀ a, ∀ t ∈ aa a, t • G.e a.castSucc ∈ Λ) (n : ℕ) :
    ∀ c : Fin r → K, (∀ b : Fin r, n ≤ b.val → c b = 0) → ∑ b, c b • G.e b.castSucc ∈ Λ → ∀ b, c b ∈ aa b := by
  induction n with
  | zero => intro c hc _ b; rw [hc b (Nat.zero_le _)]; exact Submodule.zero_mem _
  | succ n ih =>
    intro c hc hx
    by_cases hn : n < r
    · let a : Fin r := ⟨n, hn⟩
      have hc' : ∀ b : Fin r, n ≤ b.val → Function.update c a 0 b = 0 := by
        intro b hb
        by_cases hba : b = a
        · simp [hba]
        · rw [Function.update_of_ne hba]
          refine hc b ?_
          have : b.val ≠ n := fun e => hba (Fin.ext e)
          omega
      have he : ∑ b, Function.update c a 0 b • G.e b.castSucc = ∑ b, c b • G.e b.castSucc - c a • G.e a.castSucc := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ (fun b => c b • G.e b.castSucc) (Finset.mem_univ a)]
        rw [Function.update_self, zero_smul, zero_add, add_sub_cancel_left]
        exact Finset.sum_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
      have ha : c a ∈ aa a := h1 a _ _ hx (he ▸ sum_mem_xa G n _ hc')
      have hr := ih _ hc' (he ▸ Λ.sub_mem hx (h2 a _ ha))
      intro b
      by_cases hba : b = a
      · rw [hba]; exact ha
      · have := hr b
        rwa [Function.update_of_ne hba] at this
    · exact ih c (fun b hb => absurd (lt_of_le_of_lt hb b.2) hn) hx

theorem smul_mem_of_one {Λ : Submodule (𝓞 K) V} {t : K} (ht : t ∈ (1 : Submodule (𝓞 K) K)) {x : V} (hx : x ∈ Λ) :
    t • x ∈ Λ := by
  obtain ⟨s, rfl⟩ := Submodule.mem_one.1 ht
  rw [algebraMap_smul]
  exact Λ.smul_mem s hx

theorem exists_dual [FiniteDimensional K V] (G : FlagD H r) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    {aa : Fin r → Submodule (𝓞 K) K}
    (h1 : ∀ (a : Fin r) (t : K), ∀ x ∈ Λ, x - t • G.e a.castSucc ∈ G.Xa a.val → t ∈ aa a)
    (h2 : ∀ a, ∀ t ∈ aa a, t • G.e a.castSucc ∈ Λ)
    (h3 : ∀ (t : K), ∀ x ∈ Λ, x - t • G.z ∈ G.X → t ∈ (1 : Submodule (𝓞 K) K)) (h4 : G.z ∈ Λ) :
    ∃ y : Fin r → V, (∀ a b, H.B (G.e a.castSucc) (y b) = if a = b then 1 else 0) ∧ (∀ b, H.B G.z (y b) = 0) ∧
      ∀ x ∈ Λ, ∀ b, H.B x (y b) ∈ aa b := by
  have hL := (isLatMod_top_bot_iff Λ).1 hU.1
  let L : ((Fin r → K) × K) →ₗ[K] V :=
    (Fintype.linearCombination K fun a : Fin r => G.e a.castSucc).coprod (LinearMap.toSpanSingleton K V G.z)
  have hLa : ∀ p, L p = ∑ b, p.1 b • G.e b.castSucc + p.2 • G.z := fun p => by
    simp [L, Fintype.linearCombination_apply]
  have hinj : LinearMap.ker L = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨c, t⟩ hp
    rw [LinearMap.mem_ker, hLa] at hp
    have h5 := congrArg (fun v => H.B v G.z) hp
    have h6 : ∀ a : Fin r, H.B (G.e a.castSucc) G.z = 0 := G.zperp
    have h7 : H.B G.z G.z = -G.T := G.zz
    simp [h6, h7, G.hT] at h5
    subst h5
    simp only [zero_smul, add_zero] at hp
    have := Fintype.linearIndependent_iff.1 G.indep c hp
    have hc : c = 0 := funext this
    simp [hc]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L hinj
  have hg' : ∀ p, g (L p) = p := fun p => LinearMap.congr_fun hg p
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_proj Λ hL.1 hL.2 (LinearMap.range L)
  choose y hy using fun b : Fin r => exists_rep H (LinearMap.proj b ∘ₗ LinearMap.fst K _ K ∘ₗ g ∘ₗ P)
  have hy' : ∀ b p, H.B (L p) (y b) = p.1 b := fun b p => by
    rw [hy]; simp [hP2 _ ⟨p, rfl⟩, hg']
  refine ⟨y, fun a b => ?_, fun b => ?_, fun x hx b => ?_⟩
  · have := hy' b (Pi.single a 1, 0)
    rw [hLa] at this
    simpa [Pi.single_apply, eq_comm] using this
  · have := hy' b (0, 1)
    rw [hLa] at this
    simpa using this
  · obtain ⟨p, hp⟩ := hP1 x
    have e1 : H.B x (y b) = p.1 b := by rw [hy]; simp [← hp, hg']
    have e2 : L p ∈ Λ := hp ▸ hP3 x hx
    rw [hLa] at e2
    have e3 : p.2 ∈ (1 : Submodule (𝓞 K) K) := h3 _ _ e2 (by
      rw [add_sub_cancel_right]
      exact sum_mem_xa G r _ fun b hb => absurd b.2 (not_lt.2 hb))
    have e4 := Λ.sub_mem e2 (smul_mem_of_one e3 h4)
    rw [add_sub_cancel_right] at e4
    rw [e1]
    exact coeff_mem G h1 h2 r _ (fun b hb => absurd b.2 (not_lt.2 hb)) e4 b

theorem smul_dual_mem {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ) {e y : V} (h : ∀ x ∈ Λ, H.B x y • e ∈ Λ)
    {x : V} (hx : x ∈ Λ) : H.B x e • y ∈ Λ := by
  rw [mem_iff_pair hU]
  intro x' hx'
  have := (mem_iff_pair hU x).1 hx _ (h x' hx')
  convert this using 1
  simp [← H.herm x' y, mul_comm, starRingEnd_apply]

theorem exists_hyp [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (G : FlagD H r) {Λ : Submodule (𝓞 K) V}
    (hU : IsUnimod H Λ) {aa : Fin r → Submodule (𝓞 K) K}
    (h1 : ∀ (a : Fin r) (t : K), ∀ x ∈ Λ, x - t • G.e a.castSucc ∈ G.Xa a.val → t ∈ aa a)
    (h2 : ∀ a, ∀ t ∈ aa a, t • G.e a.castSucc ∈ Λ)
    (h3 : ∀ (t : K), ∀ x ∈ Λ, x - t • G.z ∈ G.X → t ∈ (1 : Submodule (𝓞 K) K)) (h4 : G.z ∈ Λ) :
    ∃ y : Fin r → V, Hyp H (fun a => G.e a.castSucc) y ∧ (∀ b, H.B G.z (y b) = 0) ∧
      ∀ x ∈ Λ, ∀ b, H.B x (y b) ∈ aa b := by
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_dual G hU h1 h2 h3 h4
  obtain ⟨w, hw⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram K hK
  have hw' : star (w : K) = ((1 - w : 𝓞 K) : K) := by
    have : ((1 - w : 𝓞 K) : K) = 1 - (w : K) := by simp
    rw [this, ← hw]; ring
  have hye : ∀ a b, H.B (y a) (G.e b.castSucc) = if a = b then 1 else 0 := by
    intro a b
    rw [← H.herm, hy1]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hz : ∀ a : Fin r, H.B G.z (G.e a.castSucc) = 0 := fun a => swap_zero (G.zperp a)
  refine ⟨fun a => y a - ∑ b, ((w : K) * H.B (y a) (y b)) • G.e b.castSucc, ⟨G.iso, fun a b => ?_, fun a b => ?_⟩,
    fun b => ?_, fun x hx a => ?_⟩
  · have hh : (starRingEnd K) (H.B (y b) (y a)) = H.B (y a) (y b) := H.herm _ _
    have hw2 : (w : K) + (starRingEnd K) (w : K) = 1 := hw
    simp [G.iso, hye, hy1, hh]
    linear_combination (-H.B (y a) (y b)) * hw2
  · simp [G.iso, hy1]
  · simp [hy2, hz]
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
    refine Submodule.sub_mem _ (hy3 x hx a) (Submodule.sum_mem _ fun b _ => ?_)
    have e1 := hy3 _ (smul_dual_mem hU (fun x' hx' => h2 b _ (hy3 x' hx' b)) hx) a
    have e2 := (aa a).smul_mem (1 - w) e1
    convert e2 using 1
    have hh : (starRingEnd K) (H.B (y a) (y b)) = H.B (y b) (y a) := H.herm _ _
    have hw2 : (starRingEnd K) (w : K) = ((1 - w : 𝓞 K) : K) := hw'
    rw [LinearMap.map_smulₛₗ, map_mul, hh, hw2, smul_eq_mul, Algebra.smul_def, map_smul]
    simp only [smul_eq_mul, LinearMap.smul_apply]
    change _ = ((1 - w : 𝓞 K) : K) * _
    ring

end Lat

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (aa : Fin r → Submodule (𝓞 K) K) (Λ : Submodule (𝓞 K) V), IsUnimod H Λ → IsFrame F Λ aa → SameGr F G → F.T = G.T → (∀ a, ∀ t ∈ aa a, t • F.e a.castSucc ∈ Λ ∧ t • G.e a.castSucc ∈ Λ) → F.z ∈ Λ → G.z ∈ Λ → ∃ m : V ≃ₗ[K] V, F.InN (m : V →ₗ[K] V) ∧ m • Λ = Λ ∧ ∀ a, m (F.e a) = G.e a := by
  intro K V _ _ _ _ _ _ _ _ H hK r F G aa Λ hU hF hS _ haa hz hz'
  have hFF : SameGr F F := fun a => by simp
  obtain ⟨y, hy, hyz, hyΛ⟩ := exists_hyp hK F hU (aa := aa)
    (fun a t x hx h => hF.1 a ▸ mem_lead hFF a.castSucc hx h) (fun a t ht => (haa a t ht).1)
    (fun t x hx h => hF.2 ▸ mem_lead hFF (Fin.last r) hx h) hz
  obtain ⟨y', hy', hyz', hyΛ'⟩ := exists_hyp hK G hU (aa := aa)
    (fun a t x hx h => hF.1 a ▸ mem_lead hS a.castSucc hx h) (fun a t ht => (haa a t ht).2)
    (fun t x hx h => hF.2 ▸ mem_lead hS (Fin.last r) hx h) hz'
  set e : Fin r → V := fun a => F.e a.castSucc with he
  set e' : Fin r → V := fun a => G.e a.castSucc with he'
  have hX : F.X = Submodule.span K (Set.range e) := x_eq_span F
  have hX' : F.X = Submodule.span K (Set.range e') := (AdaptInv.x_eq hS).symm.trans (x_eq_span G)
  have heX : ∀ a, e a ∈ F.X := fun a => hX ▸ Submodule.subset_span ⟨a, rfl⟩
  have heX' : ∀ a, e' a ∈ F.X := fun a => hX' ▸ Submodule.subset_span ⟨a, rfl⟩
  set M := move H e y e' y' with hM
  have hiso : ∀ v w, H.B (M v) (M w) = H.B v w := move_isom hy hy' fun a => hX ▸ heX' a
  have hinj : Function.Injective M := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact H.nondeg v fun w => by rw [← hiso, hv]; simp
  have hbij : Function.Bijective M := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  have hee : ∀ x ∈ Λ, ∀ a, H.B x (y a) • e a ∈ Λ := fun x hx a => (haa a _ (hyΛ x hx a)).1
  have hee' : ∀ x ∈ Λ, ∀ a, H.B x (y a) • e' a ∈ Λ := fun x hx a => (haa a _ (hyΛ x hx a)).2
  have he'e : ∀ x ∈ Λ, ∀ a, H.B x (y' a) • e a ∈ Λ := fun x hx a => (haa a _ (hyΛ' x hx a)).1
  have he'e' : ∀ x ∈ Λ, ∀ a, H.B x (y' a) • e' a ∈ Λ := fun x hx a => (haa a _ (hyΛ' x hx a)).2
  have hmid : ∀ e y : Fin r → V, (∀ x ∈ Λ, ∀ a, H.B x (y a) • e a ∈ Λ) → ∀ x ∈ Λ, mid H e y x ∈ Λ := by
    intro e y h x hx
    rw [mid_apply]
    exact Λ.sub_mem (Λ.sub_mem hx (Λ.sum_mem fun a _ => h x hx a))
      (Λ.sum_mem fun a _ => smul_dual_mem hU (fun x' hx' => h x' hx' a) hx)
  have hMΛ : ∀ x ∈ Λ, M x ∈ Λ := by
    intro x hx
    rw [hM, move_apply]
    exact Λ.add_mem (Λ.add_mem (Λ.sum_mem fun a _ => hee' x hx a)
      (Λ.sum_mem fun a _ => smul_dual_mem hU (fun x' hx' => he'e x' hx' a) hx)) (hmid _ _ he'e' _ (hmid _ _ hee x hx))
  have hMe : ∀ a, M (e a) = e' a := by
    intro a
    rw [hM, move_apply, hy.mid_span (Submodule.subset_span ⟨a, rfl⟩)]
    simp [hy.1, hy.2.2]
  have hMz : M F.z = G.z := by
    have h1 : ∀ a, H.B F.z (e a) = 0 := fun a => swap_zero (F.zperp a)
    have h2 : ∀ a, H.B G.z (e' a) = 0 := fun a => swap_zero (G.zperp a)
    have h3 : mid H e y F.z = F.z := by simp [mid_apply, h1, hyz]
    have h4 : mid H e' y' G.z = G.z := by simp [mid_apply, h2, hyz']
    have h5 : mid H e' y' (G.z - F.z) = 0 := hy'.mid_span (hX' ▸ hS (Fin.last r))
    rw [map_sub, h4, sub_eq_zero] at h5
    rw [hM, move_apply, h3, ← h5]
    simp [h1, hyz]
  refine ⟨LinearEquiv.ofBijective M hbij, ⟨hiso, hbij, fun a => ?_, fun v hv => ?_⟩, ?_, fun a => ?_⟩
  · change M (e a) - e a ∈ _
    rw [hMe]
    exact hS a.castSucc
  · change M v - v ∈ _
    have hv' : ∀ a, H.B v (e a) = 0 := fun a => swap_zero (hv a)
    have hp : ∀ a, H.B (mid H e y v) (e' a) = 0 := fun a => perp_of_span (hy.mid_e v) (hX ▸ heX' a)
    have : M v - v = ∑ a, H.B v (y a) • e' a - ∑ a, H.B v (y a) • e a - ∑ a, H.B (mid H e y v) (y' a) • e' a := by
      rw [hM, move_apply, mid_apply e' y']
      simp only [hp, hv', zero_smul, Finset.sum_const_zero]
      nth_rewrite 1 [mid_apply e y v]
      simp only [hv', zero_smul, Finset.sum_const_zero]
      abel
    rw [this]
    exact F.X.sub_mem (F.X.sub_mem (F.X.sum_mem fun a _ => F.X.smul_mem _ (heX' a))
      (F.X.sum_mem fun a _ => F.X.smul_mem _ (heX a))) (F.X.sum_mem fun a _ => F.X.smul_mem _ (heX' a))
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hMΛ x hx
    · intro x hx
      obtain ⟨v, rfl⟩ := hbij.2 x
      refine ⟨v, ?_, rfl⟩
      refine (mem_iff_pair hU v).2 fun x' hx' => ?_
      rw [← hiso]
      exact (mem_iff_pair hU _).1 hx _ (hMΛ x' hx')
  · change M (F.e a) = _
    induction a using Fin.lastCases with
    | last => exact hMz
    | cast a => exact hMe a

end GlobalTheory.DegAsm.FrameMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.FibProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem spH_B (x y : S.V) : (spH S).B x y = S.hT y x := rfl

theorem frF_e (F : FlagG S r T) (hT : T ≠ 0) (a : Fin (r + 1)) : (frF F hT).e a = F.fvec a := rfl

theorem frF_Xa (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (frF F hT).Xa k = F.Xa k := by

  have h : (fun b : Fin r => (frF F hT).e b.castSucc) = F.e := by
    funext b
    simp [frF_e, FlagG.fvec]
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, h, FlagG.Xa]

theorem frF_X (F : FlagG S r T) (hT : T ≠ 0) : (frF F hT).X = F.X := by
  rw [Formalism.HermitianLatticeCounting.S6.FlagD.X, frF_Xa, FlagG.Xa, FlagG.X]
  congr 1
  ext x
  simp

end Gen

section Bridge
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem isom_of_B {n : S.V ≃ₗ[E] S.V} (h : ∀ x y, (spH S).B (n x) (n y) = (spH S).B x y) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  intro x y
  have h1 := h y x
  rw [spH_B, spH_B] at h1
  exact h1

theorem gmap_eq_smul (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap n Λ = n • Λ := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem nlam_of_inN (F : FlagG S r T) (hT : T ≠ 0) {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (h : (frF F hT).InN (n : S.V →ₗ[E] S.V)) (hΛ : n • Λ = Λ) : n ∈ NLam Λ (⟨F, F.z⟩ : LFlag S r T) := by
  obtain ⟨hB, -, he, hperp⟩ := h

  have hfe : ∀ b : Fin r, (frF F hT).e b.castSucc = F.e b := fun b => by
    simp [frF_e, FlagG.fvec]
  refine ⟨⟨isom_of_B hB, (gmap_eq_smul n Λ).trans hΛ⟩, ?_, ?_⟩
  ·
    intro j x hx
    have hle : F.Xa (j + 1) ≤ (F.Xa j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
      rw [FlagG.Xa, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val < j + 1 := hb
      have h3 := he b
      rw [hfe, frF_Xa] at h3
      have hmono : F.Xa b.val ≤ F.Xa j :=
        Submodule.span_mono (Set.image_mono fun i (hi : i.val < b.val) => show i.val < j by omega)
      exact hmono h3
    simpa using hle hx
  ·
    intro y hy
    have hy' : ∀ x ∈ F.X, S.hT x y = 0 := by
      intro x hx
      have := (Submodule.mem_iInf _).mp hy x
      simpa using (Submodule.mem_iInf _).mp this hx
    have h4 := hperp y (fun a => by
      rw [hfe]
      have h5 := (spH S).herm y (F.e a)
      rw [spH_B, hy' _ (Submodule.subset_span (Set.mem_range_self a)), star_zero] at h5
      exact h5.symm)
    rw [frF_X] at h4
    exact h4

end Bridge

def mapD {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F : Formalism.HermitianLatticeCounting.S6.FlagD H r) (φ : V ≃ₗ[K] V) (hφ : ∀ x y, H.B (φ x) (φ y) = H.B x y) : Formalism.HermitianLatticeCounting.S6.FlagD H r where
  e a := φ (F.e a)
  T := F.T
  indep := F.indep.map' (φ : V →ₗ[K] V) (LinearEquiv.ker φ)
  iso a b := by rw [hφ]; exact F.iso a b
  zperp a := by rw [hφ]; exact F.zperp a
  zz := by rw [hφ]; exact F.zz
  hT := F.hT

section Obj
variable {D : D7} {X : HidaSetting D}

theorem Ft_e {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (a : Fin (D.R.rS + 1)) :
    (Ft t).e a = t.lin ((F0 X u).e a) := by
  have h : t.rep.1.2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  change (frq X t.rep).fl.fvec a = t.rep.1.2 ((X.Fu u).fvec a)
  simp only [frq, mapLF, h, dite_true]
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

theorem Ft_Xa {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (k : ℕ) :
    (Ft t).Xa k = ((F0 X u).Xa k).map (t.lin : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  simp only [Formalism.HermitianLatticeCounting.S6.FlagD.Xa, Submodule.map_span, Set.image_image, Ft_e, LinearEquiv.coe_coe]

end Obj

theorem mem_line {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {A : Submodule (𝓞 K) K} {v : V} {t : K} (ht : t ∈ A) :
    t • v ∈ GlobalTheory.DegCnt.line A v := by
  exact Submodule.mem_map.mpr ⟨t, ht, by simp⟩

section Main
variable {D : D7} {X : HidaSetting D}

theorem line_e_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (a : Fin D.R.rS) :
    GlobalTheory.DegCnt.line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
    (le_iSup (fun b => GlobalTheory.DegCnt.line (N.aa b) (N.F.e b.castSucc)) a)))

theorem line_z_le (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) : GlobalTheory.DegCnt.line 1 N.F.z ≤ N.P0 := by
  unfold GlobalTheory.DegCnt.NF.P0
  exact le_sup_of_le_left le_sup_right

theorem stab_of_fix (u : D.what₂.Word) {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ c, a ((F0 X u).e c) = (F0 X u).e c) : a ∈ stabF D (X.Fu u) := by
  have he : ∀ b, a ((X.Fu u).e b) = (X.Fu u).e b := fun b => by
    have h : a ((X.Fu u).fvec b.castSucc) = (X.Fu u).fvec b.castSucc := hfix b.castSucc
    simpa [FlagG.fvec] using h
  have hz : a (X.Fu u).z = (X.Fu u).z := by
    have h : a ((X.Fu u).fvec (Fin.last _)) = (X.Fu u).fvec (Fin.last _) := hfix (Fin.last _)
    simpa [FlagG.fvec] using h
  refine ⟨hi, fun j => ?_, hz⟩
  rw [FlagG.Xa, Submodule.map_span, Set.image_image]
  simp [he]

theorem gmap_one' (L : Submodule (𝓞 D.host.E) (VS D).V) : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
  rw [gmap_eq_smul, one_smul]

end Main

theorem fibC : FibC := by
  intro D large₂ X Y u hStd t₁ t₂ hlam hEq
  obtain ⟨n₀, hnN, hnΛ, hnG⟩ := hEq

  have hi₁ : t₁.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₁.rep.2.2.1
  have hi₂ : t₂.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₂.rep.2.2.1
  have hin : n₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := isom_of_B hnN.1
  have hg₁ : t₁.lin • t₁.lam' = t₂.lam := by
    rw [← gmap_eq_smul, ← hlam]
    exact t₁.rep.2.2.2.1
  have hg₂ : t₂.lin • t₂.lam' = t₂.lam := by
    rw [← gmap_eq_smul]
    exact t₂.rep.2.2.2.1
  have hnΛ' : n₀ • t₂.lam = t₂.lam := hlam ▸ hnΛ

  obtain ⟨g, hg⟩ : ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, g = t₂.lin⁻¹ * n₀ * t₁.lin := ⟨_, rfl⟩
  have hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hg ▸ mul_mem (mul_mem (inv_mem hi₂) hin) hi₁
  have hgB : ∀ x y, (HV D).B (g x) (g y) = (HV D).B x y := fun x y => by
    rw [spH_B, spH_B]
    exact hgi y x
  have hgl : g • t₁.lam' = t₂.lam' := by
    rw [hg, mul_smul, mul_smul, hg₁, hnΛ', ← hg₂, inv_smul_smul]
  have hgmem : ∀ x ∈ t₁.lam', g x ∈ t₂.lam' := fun x hx => by
    have h := Submodule.smul_mem_pointwise_smul x g t₁.lam' hx
    rw [hgl] at h
    exact h

  let G : Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := mapD (F0 X u) g hgB
  have hSG : GlobalTheory.DegAsm.SameGr (F0 X u) G := by
    intro a
    have h := hnG a
    rw [Ft_e, Ft_e, Ft_Xa, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply] at h
    show g ((F0 X u).e a) - (F0 X u).e a ∈ (F0 X u).Xa a.val
    rw [hg]
    exact h

  obtain ⟨N₁, hF₁, -, -, -, hd₁, -, hRef₁, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₁.lam' (Or.inl t₁.mem')
  obtain ⟨N₂, hF₂, -, -, -, hd₂, hTm₂, hRef₂, -⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hStd t₂.lam' (Or.inl t₂.mem')
  have hP₁ : N₁.P0 ≤ t₁.lam' :=
    (show N₁.P0 ≤ N₁.Ref (GlobalTheory.HermLat.latL N₁.F N₁.F' t₁.lam') from le_sup_left).trans hRef₁.le
  have hP₂ : N₂.P0 ≤ t₂.lam' :=
    (show N₂.P0 ≤ N₂.Ref (GlobalTheory.HermLat.latL N₂.F N₂.F' t₂.lam') from le_sup_left).trans hRef₂.le
  have haa : ∀ a, N₂.aa a = N₁.aa a := fun a => by
    simp only [GlobalTheory.DegCnt.NF.aa, hd₁, hd₂]
  have he₁ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₁.lam' := by
    intro a s hs
    have h := hP₁ (line_e_le N₁ a (mem_line (v := N₁.F.e a.castSucc) ((haa a) ▸ hs)))
    rwa [hF₁] at h
  have he₂ : ∀ a : Fin D.R.rS, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    have h := hP₂ (line_e_le N₂ a (mem_line (v := N₂.F.e a.castSucc) hs))
    rwa [hF₂] at h
  have hone : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hz₁ : (F0 X u).z ∈ t₁.lam' := by
    have h := hP₁ (line_z_le N₁ (mem_line (v := N₁.F.z) hone))
    rwa [one_smul, hF₁] at h
  have hz₂ : (F0 X u).z ∈ t₂.lam' := by
    have h := hP₂ (line_z_le N₂ (mem_line (v := N₂.F.z) hone))
    rwa [one_smul, hF₂] at h
  have hU₂ : GlobalTheory.HermLat.IsUnimod (HV D) t₂.lam' := hTm₂.1.1
  have hFr₂ : GlobalTheory.HermLat.IsFrame (F0 X u) t₂.lam' N₂.aa := hF₂ ▸ hTm₂.1.2.1
  have hint : ∀ a, ∀ s ∈ N₂.aa a, s • (F0 X u).e a.castSucc ∈ t₂.lam' ∧ s • G.e a.castSucc ∈ t₂.lam' := by
    intro a s hs
    refine ⟨he₂ a s hs, ?_⟩
    have h := hgmem _ (he₁ a s hs)
    rw [map_smul] at h
    exact h
  have hGz : G.z ∈ t₂.lam' := hgmem _ hz₁

  have hK := (GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hStd).1
  obtain ⟨m, hmN, hmΛ, hmE⟩ := GlobalTheory.DegAsm.FrameMove.main D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) G N₂.aa
    t₂.lam' hU₂ hFr₂ hSG rfl hint hz₂ hGz

  have hai : g⁻¹ * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hgi) (isom_of_B hmN.1)
  have hafix : ∀ b, (g⁻¹ * m) ((F0 X u).e b) = (F0 X u).e b := fun b => by
    show g.symm (m ((F0 X u).e b)) = (F0 X u).e b
    rw [hmE b]
    exact g.symm_apply_apply _
  have hamap : (g⁻¹ * m) • t₂.lam' = t₁.lam' := by
    rw [mul_smul, hmΛ, ← hgl, inv_smul_smul]

  have hrow := (Y.rowsOK u).2 t₁.lam' ((Y.rowsOK u).1 _ t₁.mem')
  have hl : t₂.lam' = t₁.lam' :=
    hrow.unique ⟨t₂.mem', g⁻¹ * m, stab_of_fix u hai hafix, (gmap_eq_smul _ _).trans hamap⟩
      ⟨t₁.mem', 1, stab_of_fix u (one_mem _) (fun _ => rfl), gmap_one' _⟩
  refine ⟨hl.symm, n₀, g⁻¹ * m, nlam_of_inN (X.Fu u) (tu_ne D u) hnN hnΛ, hai, ?_, hafix, m⁻¹, ?_, ?_⟩
  · rw [gmap_eq_smul]
    rw [hl] at hamap
    exact hamap
  · have hmΛ' : m • t₁.lam' = t₁.lam' := by
      rw [← hl]
      exact hmΛ
    exact GlobalTheory.LoopC.FrEqv.symm_mem_NLam (nlam_of_inN (X.Fu u) (tu_ne D u) hmN hmΛ')
  · rw [hg]
    group

end GlobalTheory.TypeAsm.FibProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof : GlobalTheory.TypeAsm.FibC := by
  first | exact @GlobalTheory.TypeAsm.FibProof.fibC | exact GlobalTheory.TypeAsm.FibProof.fibC | (intros; apply GlobalTheory.TypeAsm.FibProof.fibC <;> assumption)
end
