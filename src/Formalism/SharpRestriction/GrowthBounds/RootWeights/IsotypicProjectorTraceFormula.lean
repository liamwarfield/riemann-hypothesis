module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionRangeTrivial

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.SchurInvariantProjectionTrace
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantInjectiveOfCyclic
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.EquivariantKillsCyclicOfZero
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def weightHeightRootWeights (nu : Fin n → ℤ) : ℤ := ∑ c : Fin n, ((c : ℕ) : ℤ) * nu c

theorem weight_height_root_weights_add_root (nu : Fin n → ℤ) (a b : Fin n) :
    weightHeightRootWeights (nu + rootW a b) = weightHeightRootWeights nu + (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  unfold weightHeightRootWeights rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem lowering_monomial_raises_height {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) {mu : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSp E mu) {u : Module.End K V} (hu : u ∈ loweringWordMonoid E) :
    ∃ nu, u v ∈ weightSp E nu ∧ ((u v = v ∧ nu = mu) ∨ weightHeightRootWeights mu < weightHeightRootWeights nu) := by
  induction hu using Submonoid.closure_induction generalizing mu v with
  | mem x hx =>
    obtain ⟨a, b, hba, rfl⟩ := hx
    refine ⟨mu + rootW a b, hs a b mu v hv, Or.inr ?_⟩
    rw [weight_height_root_weights_add_root]
    have : (b : ℕ) < (a : ℕ) := hba
    omega
  | one => exact ⟨mu, by simpa using hv, Or.inl ⟨by simp, rfl⟩⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨nu2, h2, hc2⟩ := ihy hv
    obtain ⟨nu1, h1, hc1⟩ := ihx h2
    refine ⟨nu1, by simpa [Module.End.mul_apply] using h1, ?_⟩
    rcases hc2 with ⟨e2, rfl⟩ | lt2
    · rcases hc1 with ⟨e1, rfl⟩ | lt1
      · left; exact ⟨by rw [Module.End.mul_apply, e1, e2], rfl⟩
      · right; exact lt1
    · right
      rcases hc1 with ⟨_, rfl⟩ | lt1
      · exact lt2
      · exact lt2.trans lt1

theorem self_mem_cyclicSubmodule (E : GLOps n K V) (v : V) : v ∈ cyclicSubmodule E v := Submodule.subset_span ⟨1, (Umon E).one_mem, by simp⟩

theorem cyclic_highest_weightSpace_line [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (v : V)
    (hv : IsHWV E mu v) (x : V) (hx : x ∈ cyclicSubmodule E v) (hxw : x ∈ weightSp E mu) : ∃ c : K, x = c • v := by
  classical
  have hs : OperatorsShiftWeightsByRoots E := gl_rep_shifts_weights hE

  set Hh : Module.End K V := ∑ c : Fin n, (((c : ℕ) : ℤ) : K) • E c c with hHh
  have hH : ∀ nu (w : V), w ∈ weightSp E nu → Hh w = ((weightHeightRootWeights nu : ℤ) : K) • w := by
    intro nu w hw
    rw [mem_weightSpace_iff_diag_eigen] at hw
    rw [hHh, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hw, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [weightHeightRootWeights]

  have hvY : v ∈ loweringWordSpan E v := Submodule.subset_span ⟨1, (loweringWordMonoid E).one_mem, by simp⟩
  have hcY : cyclicSubmodule E v ≤ loweringWordSpan E v := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    exact lowering_word_span_enveloping_stable hE hv hu v hvY
  set S : Submodule K V := Submodule.span K
    {y | ∃ nu, y ∈ weightSp E nu ∧ weightHeightRootWeights mu < weightHeightRootWeights nu} with hS
  have hYS : loweringWordSpan E v ≤ K ∙ v ⊔ S := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨nu, hnu, hc⟩ := lowering_monomial_raises_height hs hv.2.1 hu
    rcases hc with ⟨he, -⟩ | hlt
    · rw [he]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨nu, hnu, hlt⟩)
  obtain ⟨y, hy, s, hsS, hys⟩ := Submodule.mem_sup.1 (hYS (hcY hx))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  have hsx : s = x - c • v := by rw [← hys]; abel
  have hs1 : s ∈ Hh.eigenspace ((weightHeightRootWeights mu : ℤ) : K) := by
    rw [Module.End.mem_eigenspace_iff, hsx, map_sub, map_smul, hH mu x hxw, hH mu v hv.2.1, smul_sub,
      smul_comm]
  have hs2 : s ∈ ⨆ (l : K) (_ : l ≠ ((weightHeightRootWeights mu : ℤ) : K)), Hh.eigenspace l := by
    refine (Submodule.span_le.2 ?_) hsS
    rintro w ⟨nu, hnu, hlt⟩
    have hne : ((weightHeightRootWeights nu : ℤ) : K) ≠ ((weightHeightRootWeights mu : ℤ) : K) := by
      exact_mod_cast hlt.ne'
    refine Submodule.mem_iSup_of_mem ((weightHeightRootWeights nu : ℤ) : K) (Submodule.mem_iSup_of_mem hne ?_)
    rw [Module.End.mem_eigenspace_iff]
    exact hH nu w hnu
  have h0 : s = 0 :=
    (Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep Hh ((weightHeightRootWeights mu : ℤ) : K))) s hs1 hs2
  rw [← hys, h0, add_zero]

theorem equivariant_kills_cyclic_of_zero (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T) (v : V)
    (h0 : T v = 0) : ∀ x ∈ cyclicSubmodule E v, T x = 0 := by
  intro x hx
  have hle : cyclicSubmodule E v ≤ LinearMap.ker T := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    obtain ⟨u', -, hu'⟩ := equivariant_intertwines_monoid E E' T hT hu
    show T (u v) = 0
    rw [hu' v, h0, map_zero]
  exact hle hx

theorem envelopingMonoid_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) {u : Module.End K V} (hu : u ∈ Umon E) :
    ∃ uL ∈ Umon (restrictRepresentation E L hL), ∀ y : L, ((uL y : L) : V) = u (y : V) := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨restrictRepresentation E L hL a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => rfl⟩
  | one => exact ⟨1, (Umon _).one_mem, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨ux, hux, hx⟩ := ihx
    obtain ⟨uy, huy, hy⟩ := ihy
    refine ⟨ux * uy, (Umon _).mul_mem hux huy, fun z => ?_⟩
    simp only [Module.End.mul_apply, hx, hy]

theorem cyclicSubmodule_restrict_eq_top (E : GLOps n K V) (v : V) (hL : IsSubrepresentation E (cyclicSubmodule E v)) :
    cyclicSubmodule (restrictRepresentation E _ hL) (⟨v, self_mem_cyclicSubmodule E v⟩ : cyclicSubmodule E v) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨x, hx⟩ -
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨uL, huL, hL'⟩ := envelopingMonoid_restrict E _ hL hu
    have heq : (⟨u v, Submodule.subset_span ⟨u, hu, rfl⟩⟩ : cyclicSubmodule E v) = uL ⟨v, self_mem_cyclicSubmodule E v⟩ :=
      Subtype.ext (hL' ⟨v, self_mem_cyclicSubmodule E v⟩).symm
    rw [heq]
    exact Submodule.subset_span ⟨uL, huL, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y z hy hz ihy ihz =>
    have := Submodule.add_mem _ ihy ihz
    exact this
  | smul c y hy ihy =>
    have := Submodule.smul_mem _ c ihy
    exact this

theorem highest_vector_restrict (E : GLOps n K V) (L : Submodule K V) (hL : IsSubrepresentation E L) (mu : Fin n → ℤ) (v : V) (hvL : v ∈ L)
    (hv : IsHWV E mu v) : IsHWV (restrictRepresentation E L hL) mu ⟨v, hvL⟩ := by
  obtain ⟨h0, hw, hl⟩ := hv
  refine ⟨fun h => h0 (congrArg Subtype.val h), ?_, fun a b hab => Subtype.ext (hl a b hab)⟩
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hw ⊢
  intro a
  apply Subtype.ext
  have := hw a
  simpa using this

end

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def prodRepresentation (E : GLOps n K V) (E' : GLOps n K V') : GLOps n K (V × V') := fun a b => (E a b).prodMap (E' a b)

@[simp] theorem prodRepresentation_apply (E : GLOps n K V) (E' : GLOps n K V') (a b : Fin n) (z : V × V') :
    prodRepresentation E E' a b z = (E a b z.1, E' a b z.2) := rfl

theorem prod_mem_weightSpace_iff (E : GLOps n K V) (E' : GLOps n K V') (mu : Fin n → ℤ) (z : V × V') :
    z ∈ weightSp (prodRepresentation E E') mu ↔ z.1 ∈ weightSp E mu ∧ z.2 ∈ weightSp E' mu := by
  obtain ⟨x, y⟩ := z
  simp [weightSp, forall_and]

theorem prodRepresentation_isRep [FiniteDimensional K V] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V')
    (hE : IsGLRep E) (hE' : IsGLRep E') : IsGLRep (prodRepresentation E E') := by
  obtain ⟨hE1, -, hE3⟩ := hE
  obtain ⟨hE1', -, hE3'⟩ := hE'
  refine ⟨fun a b c d => ?_, fun z => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · refine LinearMap.ext fun z => Prod.ext ?_ ?_
    · have h := LinearMap.congr_fun (hE1 a b c d) z.1
      split_ifs at h ⊢ <;> simpa using h
    · have h := LinearMap.congr_fun (hE1' a b c d) z.2
      split_ifs at h ⊢ <;> simpa using h
  · rw [eq_top_iff]
    rintro ⟨x, y⟩ -
    have hx : x ∈ ⨆ mu, weightSp E mu := by rw [hE3]; exact Submodule.mem_top
    have hy : y ∈ ⨆ mu, weightSp E' mu := by rw [hE3']; exact Submodule.mem_top
    have h1 : (⨆ mu, weightSp E mu).map (LinearMap.inl K V V') ≤ ⨆ mu, weightSp (prodRepresentation E E') mu := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun mu => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [prod_mem_weightSpace_iff]
      exact ⟨by simpa using hv, by simp⟩
    have h2 : (⨆ mu, weightSp E' mu).map (LinearMap.inr K V V') ≤ ⨆ mu, weightSp (prodRepresentation E E') mu := by
      rw [Submodule.map_iSup]
      refine iSup_mono fun mu => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [prod_mem_weightSpace_iff]
      exact ⟨by simp, by simpa using hv⟩
    have hxy : ((x, y) : V × V') = LinearMap.inl K V V' x + LinearMap.inr K V V' y := by simp
    rw [hxy]
    exact Submodule.add_mem _ (h1 ⟨x, hx, rfl⟩) (h2 ⟨y, hy, rfl⟩)

theorem equivariant_lifts_monoid (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    {u' : Module.End K V'} (hu : u' ∈ Umon E') : ∃ u ∈ Umon E, ∀ y, T (u y) = u' (T y) := by
  have hu' : u' ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E' ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨E a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => hT a b y⟩
  | one => exact ⟨1, one_mem _, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨u1, hu1, h1⟩ := ihx
    obtain ⟨u2, hu2, h2⟩ := ihy
    exact ⟨u1 * u2, mul_mem hu1 hu2, fun z => (h1 (u2 z)).trans (congrArg x (h2 z))⟩

private theorem exists_Umon_intertwined_of_isEquivariantMap (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V')
    (hT : IsEquivariantMap E E' T) {u : Module.End K V} (hu : u ∈ Umon E) :
    ∃ u' ∈ Umon E', ∀ y, T (u y) = u' (T y) := by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨E' a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun y => hT a b y⟩
  | one => exact ⟨1, one_mem _, fun y => rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨u1, hu1, h1⟩ := ihx
    obtain ⟨u2, hu2, h2⟩ := ihy
    exact ⟨u1 * u2, mul_mem hu1 hu2, fun z => (h1 (y z)).trans (congrArg u1 (h2 z))⟩

theorem equivariant_map_cyclicSubmodule (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T) (v : V) :
    (cyclicSubmodule E v).map T = cyclicSubmodule E' (T v) := by
  unfold cyclicSubmodule
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨u', hu', h⟩ := exists_Umon_intertwined_of_isEquivariantMap E E' T hT hu
    exact ⟨u', hu', h v⟩
  · rintro ⟨u', hu', rfl⟩
    obtain ⟨u, hu, h⟩ := equivariant_lifts_monoid E E' T hT hu'
    exact ⟨u v, ⟨u, hu, rfl⟩, h v⟩

end

theorem equivariant_injective_of_cyclic (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K G V : Type} [Field K] [CharZero K]
    [AddCommGroup G] [Module K G] [FiniteDimensional K G] [AddCommGroup V] [Module K V]
    (EG : GLOps n K G) (hEG : IsGLRep EG) (E : GLOps n K V) (lam : Fin n → ℤ) (g0 : G) (hg0 : IsHWV EG lam g0)
    (hcyc : cyclicSubmodule EG g0 = ⊤) (F : G →ₗ[K] V) (hF : IsEquivariantMap EG E F) (hne : F g0 ≠ 0) :
    LinearMap.ker F = ⊥ := by
  classical
  have hEG0 := hEG
  obtain ⟨hcomm, -, -⟩ := hEG0
  obtain ⟨-, hg0w, hg0r⟩ := hg0
  have wt : ∀ (μ : Fin n → ℤ) (x : G), x ∈ weightSp EG μ ↔ ∀ a, EG a a x = ((μ a : ℤ) : K) • x := by
    intro μ x
    simp [weightSp, sub_eq_zero]
  have hlam := (wt lam g0).mp hg0w
  have comm : ∀ a b c d (y : G), EG c d (EG a b y) =
      EG a b (EG c d y) + ((if d = a then EG c b y else 0) - (if b = c then EG a d y else 0)) := by
    intro a b c d y
    have h' : EG c d (EG a b y) - EG a b (EG c d y) =
        (if d = a then EG c b y else 0) - (if b = c then EG a d y else 0) := by
      have h := LinearMap.congr_fun (hcomm c d a b) y
      split_ifs at h ⊢ <;> simpa using h
    exact sub_eq_iff_eq_add'.mp h'
  obtain ⟨L, hL⟩ : ∃ L : Submonoid (Module.End K G),
      L = Submonoid.closure {x | ∃ a b : Fin n, b < a ∧ x = EG a b} := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Submodule K G, N = Submodule.span K {x | ∃ l ∈ L, x = l g0} := ⟨_, rfl⟩
  have lowL : ∀ a b : Fin n, b < a → EG a b ∈ L := fun a b h => by
    rw [hL]; exact Submonoid.subset_closure ⟨a, b, h, rfl⟩
  have gen_mem : ∀ l ∈ L, l g0 ∈ N := fun l hl => by
    rw [hN]; exact Submodule.subset_span ⟨l, hl, rfl⟩
  have g0N : g0 ∈ N := by simpa using gen_mem 1 L.one_mem
  have low_mem : ∀ a b : Fin n, b < a → N ≤ N.comap (EG a b) := by
    intro a b hab
    refine (le_of_eq hN).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, hl, rfl⟩
    exact gen_mem _ (L.mul_mem (lowL a b hab) hl)
  have all_gen : ∀ l ∈ L, ∀ c d, EG c d (l g0) ∈ N := by
    intro l hl
    rw [hL] at hl
    induction hl using Submonoid.closure_induction_left with
    | one =>
      intro c d
      show EG c d g0 ∈ N
      rcases lt_trichotomy c d with h | h | h
      · rw [hg0r c d h]; exact N.zero_mem
      · rw [h, hlam d]; exact N.smul_mem _ g0N
      · exact gen_mem _ (lowL c d h)
    | mul_left s hs l _ ih =>
      obtain ⟨a, b, hab, rfl⟩ := hs
      intro c d
      show EG c d (EG a b (l g0)) ∈ N
      rw [comm a b c d (l g0)]
      refine N.add_mem (low_mem a b hab (ih c d)) (N.sub_mem ?_ ?_) <;>
        split_ifs <;> first | exact ih _ _ | exact N.zero_mem
  have all_mem : ∀ c d, ∀ x ∈ N, EG c d x ∈ N := by
    intro c d
    have hle : N ≤ N.comap (EG c d) := by
      refine (le_of_eq hN).trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨l, hl, rfl⟩
      exact all_gen l hl c d
    exact fun x hx => hle hx
  have umonS : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) →
      ∀ u ∈ Umon EG, ∀ x ∈ S, u x ∈ S := by
    intro S hS u hu
    have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => EG ab.1 ab.2) := hu
    clear hu
    induction hu' using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      exact fun y hy => hS a b y hy
    | one => exact fun y hy => hy
    | mul x y _ _ ihx ihy => exact fun z hz => ihx _ (ihy z hz)
  have cycle : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) → g0 ∈ S → S = ⊤ := by
    intro S hS hg
    rw [eq_top_iff, ← hcyc]
    unfold cyclicSubmodule
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact umonS S hS u hu g0 hg
  have Ntop : N = ⊤ := cycle N all_mem g0N
  obtain ⟨H, hH⟩ : ∃ H : Module.End K G, H = ∑ c : Fin n, ((c : ℕ) : K) • EG c c := ⟨_, rfl⟩
  have hHapp : ∀ y, H y = ∑ c : Fin n, ((c : ℕ) : K) • EG c c y := by
    intro y
    rw [hH]
    simp
  obtain ⟨h0, hh0⟩ : ∃ h0 : K, h0 = ∑ c : Fin n, ((c : ℕ) : K) * ((lam c : ℤ) : K) := ⟨_, rfl⟩
  have Hg0 : H g0 = h0 • g0 := by
    rw [hHapp, hh0, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hlam c, smul_smul]
  have Hstep : ∀ (a b : Fin n) (y : G) (t : K), H y = t • y →
      H (EG a b y) = (t + (((a : ℕ) : K) - ((b : ℕ) : K))) • EG a b y := by
    intro a b y t hy
    have e1 : ∑ c : Fin n, ((c : ℕ) : K) • EG a b (EG c c y) = EG a b (H y) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hHapp, map_sum]
      simp only [map_smul]
    have e2 : ∑ c : Fin n, ((c : ℕ) : K) • (if c = a then EG c b y else 0) =
        ((a : ℕ) : K) • EG a b y := by
      simp [smul_ite]
    have e3 : ∑ c : Fin n, ((c : ℕ) : K) • (if b = c then EG a c y else 0) =
        ((b : ℕ) : K) • EG a b y := by
      simp [smul_ite]
    rw [hHapp]
    simp only [comm a b, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3,
      hy, map_smul]
    rw [add_smul, sub_smul]
  have alt : ∀ l ∈ L, (∃ r : K, l g0 = r • g0) ∨
      ∃ k : ℕ, 0 < k ∧ H (l g0) = (h0 + (k : K)) • l g0 := by
    intro l hl
    rw [hL] at hl
    induction hl using Submonoid.closure_induction_left with
    | one => exact Or.inl ⟨1, by simp⟩
    | mul_left s hs l _ ih =>
      obtain ⟨a, b, hab, rfl⟩ := hs
      have hab' : (b : ℕ) < (a : ℕ) := hab
      have hcast : ((a : ℕ) : K) - ((b : ℕ) : K) = (((a : ℕ) - (b : ℕ) : ℕ) : K) := by
        rw [Nat.cast_sub hab'.le]
      right
      rcases ih with ⟨r, hr⟩ | ⟨k, hk0, hHk⟩
      · refine ⟨(a : ℕ) - (b : ℕ), by omega, ?_⟩
        show H (EG a b (l g0)) = _ • EG a b (l g0)
        rw [hr, map_smul, map_smul, Hstep a b g0 h0 Hg0, hcast]
        exact smul_comm _ _ _
      · refine ⟨k + ((a : ℕ) - (b : ℕ)), by omega, ?_⟩
        show H (EG a b (l g0)) = _ • EG a b (l g0)
        rw [Hstep a b _ _ hHk, hcast, Nat.cast_add, add_assoc]
  have key : ∀ w : G, H w = h0 • w → ∃ r : K, w = r • g0 := by
    intro w hw
    have hle : N ≤ Submodule.span K {g0} ⊔ ⨆ (μ : K) (_ : μ ≠ h0), Module.End.eigenspace H μ := by
      refine (le_of_eq hN).trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨l, hl, rfl⟩
      rcases alt l hl with ⟨r, hr⟩ | ⟨k, hk, hHk⟩
      · rw [hr]
        exact Submodule.mem_sup_left (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self g0))
      · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (h0 + (k : K))
          (Submodule.mem_iSup_of_mem ?_ ?_))
        · intro h
          have : k = 0 := by simpa using h
          omega
        · exact Module.End.mem_eigenspace_iff.mpr hHk
    have hwN : w ∈ N := by rw [Ntop]; exact Submodule.mem_top
    obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp (hle hwN)
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hz0 : z ∈ Module.End.eigenspace H h0 := by
      rw [Module.End.mem_eigenspace_iff]
      rw [map_add (f := _), map_smul, Hg0, smul_add, smul_comm h0 r g0] at hw
      exact add_left_cancel hw
    have hz' : z = 0 := (Submodule.mem_bot K).mp
      ((Module.End.eigenspaces_iSupIndep H h0).le_bot (Submodule.mem_inf.mpr ⟨hz0, hz⟩))
    exact ⟨r, by rw [hz', add_zero]⟩
  have hWs : ∀ a b, ∀ x ∈ LinearMap.ker F, EG a b x ∈ LinearMap.ker F := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hF a b x, hx, map_zero]
  obtain ⟨W', hC, hW's⟩ := h2 K G n EG hEG (LinearMap.ker F) hWs
  have Hmem : ∀ S : Submodule K G, (∀ a b, ∀ x ∈ S, EG a b x ∈ S) → ∀ x ∈ S, H x ∈ S := by
    intro S hS x hx
    rw [hHapp]
    exact S.sum_mem fun c _ => S.smul_mem _ (hS c c x hx)
  have hg : g0 ∈ LinearMap.ker F ⊔ W' := by rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.mp hg
  have hHw : H w = h0 • w := by
    have e : H w - h0 • w = h0 • w' - H w' := by
      have h := congrArg H hsum
      rw [map_add (f := _), Hg0, ← hsum, smul_add] at h
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have h1 : H w - h0 • w ∈ LinearMap.ker F := sub_mem (Hmem _ hWs w hw) (Submodule.smul_mem _ _ hw)
    have h2' : H w - h0 • w ∈ W' := by
      rw [e]
      exact sub_mem (Submodule.smul_mem _ _ hw') (Hmem _ hW's w' hw')
    exact sub_eq_zero.mp ((Submodule.mem_bot K).mp (hC.disjoint.le_bot (Submodule.mem_inf.mpr ⟨h1, h2'⟩)))
  obtain ⟨r, hr⟩ := key w hHw
  have hr0 : r = 0 := by
    have hFw : F w = 0 := LinearMap.mem_ker.mp hw
    rw [hr, map_smul] at hFw
    exact (smul_eq_zero.mp hFw).resolve_right hne
  have hg0W' : g0 ∈ W' := by
    rw [← hsum, hr, hr0, zero_smul, zero_add]
    exact hw'
  have hbot := hC.inf_eq_bot
  rwa [cycle W' hW's hg0W', inf_top_eq] at hbot

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem exists_equivariant_cyclic_to_hwv (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (lam : Fin n → ℤ)
    (v0 v : V) (hv0 : IsHWV E lam v0) (hv : IsHWV E lam v) (hL : IsSubrepresentation E (cyclicSubmodule E v0)) :
    ∃ φ : cyclicSubmodule E v0 →ₗ[K] V, IsEquivariantMap (restrictRepresentation E _ hL) E φ ∧ φ ⟨v0, self_mem_cyclicSubmodule E v0⟩ = v := by
  have hP := prodRepresentation_isRep E E hE hE
  have hg : IsHWV (prodRepresentation E E) lam (v0, v) := by
    refine ⟨fun h => hv0.1 (congrArg Prod.fst h), (prod_mem_weightSpace_iff E E lam _).2 ⟨hv0.2.1, hv.2.1⟩, fun a b hab => ?_⟩
    rw [prodRepresentation_apply, hv0.2.2 a b hab, hv.2.2 a b hab]; rfl
  have hΓ := cyclicSubmodule_isSubrepresentation (prodRepresentation E E) (v0, v)
  have hEΓ := restrictRepresentation_isRep (prodRepresentation E E) hP _ hΓ
  have hg' := highest_vector_restrict (prodRepresentation E E) _ hΓ lam (v0, v) (self_mem_cyclicSubmodule _ _) hg
  have hcyc := cyclicSubmodule_restrict_eq_top (prodRepresentation E E) (v0, v) hΓ
  let F : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.fst K V V) ∘ₗ (Submodule.subtype _)
  let S2 : cyclicSubmodule (prodRepresentation E E) (v0, v) →ₗ[K] V := (LinearMap.snd K V V) ∘ₗ (Submodule.subtype _)
  have hF : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E F := fun a b x => rfl
  have hS : IsEquivariantMap (restrictRepresentation (prodRepresentation E E) _ hΓ) E S2 := fun a b x => rfl
  have hker := equivariant_injective_of_cyclic D h2 _ hEΓ E lam _ hg' hcyc F hF hv0.1
  have hinj : Function.Injective F := LinearMap.ker_eq_bot.1 hker
  have hrange : LinearMap.range F = cyclicSubmodule E v0 := by
    have := equivariant_map_cyclicSubmodule _ E F hF ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩
    rw [hcyc, Submodule.map_top] at this
    exact this
  have hmem : ∀ z, F z ∈ cyclicSubmodule E v0 := fun z => by rw [← hrange]; exact ⟨z, rfl⟩
  let e : cyclicSubmodule (prodRepresentation E E) (v0, v) ≃ₗ[K] cyclicSubmodule E v0 :=
    LinearEquiv.ofBijective (F.codRestrict _ hmem)
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => by
        have hy : (y : V) ∈ LinearMap.range F := by rw [hrange]; exact y.2
        obtain ⟨z, hz⟩ := hy
        exact ⟨z, Subtype.ext hz⟩⟩
  have he : ∀ z, ((e z : cyclicSubmodule E v0) : V) = F z := fun z => rfl
  refine ⟨S2 ∘ₗ e.symm.toLinearMap, fun a b y => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective y
    have h1 : restrictRepresentation E _ hL a b (e z) = e (restrictRepresentation (prodRepresentation E E) _ hΓ a b z) := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply, e.symm_apply_apply]
    exact hS a b z
  · have h1 : (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) = e ⟨(v0, v), self_mem_cyclicSubmodule _ _⟩ := Subtype.ext rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, e.symm_apply_apply]
    rfl

def trivialRepresentation (n : ℕ) (K : Type) [Field K] : GLOps n K K := fun _ _ => 0

theorem trivialRepresentation_isRep (n : ℕ) (K : Type) [Field K] : IsGLRep (trivialRepresentation n K) := by
  refine ⟨?_, fun x => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩, ?_⟩
  · intro a b c d
    simp only [trivialRepresentation]
    split_ifs <;> simp
  · rw [eq_top_iff]
    intro x _
    exact Submodule.mem_iSup_of_mem 0 ((mem_weightSp_iff_diagonal_apply _ _ _).2 fun a => by simp [trivialRepresentation])

theorem trivialRep_invariant_projection (n : ℕ) (K : Type) [Field K] [CharZero K] : IsInvProj (trivialRepresentation n K) 1 := by
  refine ⟨fun x _ => rfl, fun mu hmu x hx => ?_⟩
  have hle : isoSub (trivialRepresentation n K) mu ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, _, v, hv, _⟩
    exfalso
    obtain ⟨i, hi⟩ : ∃ i, mu i ≠ 0 := by
      by_contra hcon
      exact hmu (funext fun i => by_contra fun h => hcon ⟨i, h⟩)
    have h1 := (mem_weightSp_iff_diagonal_apply _ mu v).1 hv.2.1 i
    simp only [trivialRepresentation, LinearMap.zero_apply] at h1
    rcases smul_eq_zero.1 h1.symm with h | h
    · exact hi (by exact_mod_cast h)
    · exact hv.1 h
  have := hle hx
  rw [Submodule.mem_bot] at this
  rw [this, map_zero]

theorem invariant_projection_equivariant (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V V' : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (E : GLOps n K V) (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E')
    (P : Module.End K (V →ₗ[K] V')) (hP : IsInvProj (homRepresentation E E') P) (g : V →ₗ[K] V') : IsEquivariantMap E E' (P g) := by
  intro a b x
  have h := congrArg (fun f : V →ₗ[K] V' => f x)
    (invariant_projection_kills_operators D h2 n K _ (homRepresentation E E') (homRepresentation_isRep E E' hE hE') P hP g a b)
  simp only [homRepresentation_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.1 h).symm

theorem schur_invariant_projection_trace (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K L : Type} [Field K] [CharZero K]
    [AddCommGroup L] [Module K L] [FiniteDimensional K L] (EL : GLOps n K L) (hEL : IsGLRep EL) (lam : Fin n → ℤ)
    (v0 : L) (hv0 : IsHWV EL lam v0) (hcyc : cyclicSubmodule EL v0 = ⊤)
    (P0 : Module.End K (L →ₗ[K] L)) (hP0 : IsInvProj (homRepresentation EL EL) P0) (g : L →ₗ[K] L) :
    (Module.finrank K L : K) • P0 g = (LinearMap.trace K L g) • (LinearMap.id : L →ₗ[K] L) := by
  have hψ := invariant_projection_equivariant D h2 EL EL hEL hEL P0 hP0 g
  have hw : P0 g v0 ∈ weightSp EL lam := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    rw [← hψ, (mem_weightSp_iff_diagonal_apply EL lam v0).1 hv0.2.1 a, map_smul]
  obtain ⟨c, hc⟩ := cyclic_highest_weightSpace_line EL hEL lam v0 hv0 (P0 g v0) (by rw [hcyc]; trivial) hw
  have hid : P0 g = c • (LinearMap.id : L →ₗ[K] L) := by
    have hT : IsEquivariantMap EL EL (P0 g - c • (LinearMap.id : L →ₗ[K] L)) := by
      intro a b x
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
      rw [hψ]
    have h0 : (P0 g - c • (LinearMap.id : L →ₗ[K] L)) v0 = 0 := by
      simp [hc]
    ext x
    have := equivariant_kills_cyclic_of_zero EL EL _ hT v0 h0 x (by rw [hcyc]; trivial)
    exact sub_eq_zero.1 this
  have htr : IsEquivariantMap (homRepresentation EL EL) (trivialRepresentation n K) (LinearMap.trace K L) := by
    intro a b f
    have : homRepresentation EL EL a b f = EL a b * f - f * EL a b := by
      ext x; simp
    rw [this, map_sub, LinearMap.trace_mul_comm, sub_self]
    rfl
  have h3 := equivariant_commutes_isotypic D h2 n K _ K (homRepresentation EL EL) (trivialRepresentation n K) (homRepresentation_isRep EL EL hEL hEL)
    (trivialRepresentation_isRep n K) (LinearMap.trace K L) htr P0 1 hP0 (trivialRep_invariant_projection n K) g
  rw [Module.End.one_apply, hid, map_smul, LinearMap.trace_id, smul_eq_mul] at h3
  rw [hid, smul_smul, ← h3, mul_comm]

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def smulRightLinear {K L W : Type} [Field K] [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]
    (ξ : L →ₗ[K] K) : W →ₗ[K] (L →ₗ[K] W) where
  toFun := fun m => ξ.smulRight m
  map_add' := fun m m' => by ext x; simp
  map_smul' := fun c m => by
    ext x
    simp only [LinearMap.smulRight_apply, RingHom.id_apply, LinearMap.smul_apply]
    exact smul_comm _ _ _

theorem isotypic_projector_trace_formula (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicProjectorTraceFormula := by
  intro n K W _ _ _ _ _ E hE lam e he v0 hv0 hL P hP ι _ b m
  have hEL := restrictRepresentation_isRep E hE _ hL
  have hv0' := highest_vector_restrict E _ hL lam v0 (self_mem_cyclicSubmodule E v0) hv0
  have hcyc := cyclicSubmodule_restrict_eq_top E v0 hL
  have hPe := fun g => invariant_projection_equivariant D h2 (restrictRepresentation E _ hL) E hEL hE P hP g

  let Θ : W →ₗ[K] W := ∑ i, (LinearMap.applyₗ (b i)) ∘ₗ P ∘ₗ smulRightLinear (b.coord i)
  have hΘ : ∀ m, Θ m = ∑ i, P ((b.coord i).smulRight m) (b i) := by
    intro m
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    rfl
  have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.eqLocus ((Fintype.card ι : K) • Θ) e := by
    refine iSup_le fun mu => ?_
    by_cases hmu : mu = lam
    · subst hmu
      refine Submodule.span_le.2 ?_
      rintro y ⟨u, hu, v, hv, rfl⟩
      have hy : u v ∈ isoSub E mu := Submodule.subset_span ⟨u, hu, v, hv, rfl⟩
      obtain ⟨φ, hφ, hφv⟩ := exists_equivariant_cyclic_to_hwv D h2 E hE mu v0 v hv0 hv hL
      obtain ⟨uL, _, huL⟩ := equivariant_lifts_monoid (restrictRepresentation E _ hL) E φ hφ hu
      have hm : u v = φ (uL ⟨v0, self_mem_cyclicSubmodule E v0⟩) := by rw [huL, hφv]
      obtain ⟨P0, hP0⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEL)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hL)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W φ) := by
        intro a c g
        ext x
        simp only [LinearMap.llcomp_apply, homRepresentation_apply, map_sub]
        rw [hφ]
      change ((Fintype.card ι : K) • Θ) (u v) = e (u v)
      rw [he.1 _ hy, LinearMap.smul_apply, hΘ, hm, Finset.smul_sum]
      set l := uL ⟨v0, self_mem_cyclicSubmodule E v0⟩ with hl
      have hterm : ∀ i, (Fintype.card ι : K) • P ((b.coord i).smulRight (φ l)) (b i) = (b.repr l i) • φ (b i) := by
        intro i
        have h3 : (b.coord i).smulRight (φ l) = LinearMap.llcomp K _ _ W φ ((b.coord i).smulRight l) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEL) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W φ) hT P0 P hP0 hP ((b.coord i).smulRight l)
        have h5 := schur_invariant_projection_trace D h2 _ hEL mu _ hv0' hcyc P0 hP0 ((b.coord i).smulRight l)
        rw [Module.finrank_eq_card_basis b, LinearMap.trace_smulRight] at h5
        rw [h3, ← h4, LinearMap.llcomp_apply, ← map_smul, ← LinearMap.smul_apply, h5]
        simp [Module.Basis.coord_apply]
      rw [Finset.sum_congr rfl fun i _ => hterm i]
      conv_rhs => rw [← b.sum_repr l]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm
    · intro y hy
      have hWm : IsSubrepresentation E (isoSub E mu) := fun a c => isotypic_stable_under_gl_operator E mu a c
      have hEm := restrictRepresentation_isRep E hE _ hWm
      obtain ⟨P1, hP1⟩ := invariant_projection_exists D h2 n K _ _ (homRepresentation_isRep _ _ hEL hEm)
      have hT : IsEquivariantMap (homRepresentation (restrictRepresentation E _ hL) (restrictRepresentation E _ hWm)) (homRepresentation (restrictRepresentation E _ hL) E)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) := by
        intro a c g
        ext x
        simp
      have hzero : ∀ ξ : cyclicSubmodule E v0 →ₗ[K] K, P (ξ.smulRight y) = 0 := by
        intro ξ
        have h3 : ξ.smulRight y = LinearMap.llcomp K _ _ W (isoSub E mu).subtype
            (ξ.smulRight (⟨y, hy⟩ : isoSub E mu)) := by
          ext x; simp
        have h4 := equivariant_commutes_isotypic D h2 n K _ _ _ _ (homRepresentation_isRep _ _ hEL hEm) (homRepresentation_isRep _ _ hEL hE)
          (LinearMap.llcomp K _ _ W (isoSub E mu).subtype) hT P1 P hP1 hP (ξ.smulRight (⟨y, hy⟩ : isoSub E mu))
        have hmem : ∀ x, P (ξ.smulRight y) x ∈ isoSub E mu := by
          intro x
          rw [h3, ← h4]
          simp
        have hv00 : P (ξ.smulRight y) ⟨v0, self_mem_cyclicSubmodule E v0⟩ = 0 := by
          by_contra h0
          have h6 := highest_vector_mem_isotypic E lam _ (equivariant_image_highest_vector _ E _ (hPe _) lam _ hv0' h0)
          exact h0 ((he.1 _ h6).symm.trans (he.2 mu hmu _ (hmem _)))
        ext x
        exact equivariant_kills_cyclic_of_zero _ E _ (hPe _) _ hv00 x (by rw [hcyc]; trivial)
      change ((Fintype.card ι : K) • Θ) y = e y
      rw [he.2 mu hmu y hy, LinearMap.smul_apply, hΘ]
      simp [hzero]
  have hm : m ∈ (⨆ mu, isoSub E mu) := by rw [isotypic_submodules_span_top D h2 n K W E hE]; trivial
  have := hle hm
  change ((Fintype.card ι : K) • Θ) m = e m at this
  rw [LinearMap.smul_apply, hΘ] at this
  exact this

end Formalism.MainNotions.G.GLWeightTheory
