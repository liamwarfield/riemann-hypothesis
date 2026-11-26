module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianHasBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellParabolicNearIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeFlagTransitiveLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfEigOfMemTwKer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasis

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLattice
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.Adapted

section Lemmas

variable {R : Type} [CommRing R] {c : R →+* R} {𝔬 : Subring R}
  {V : Type} [AddCommGroup V] [Module R V] {h : V → V → R}

theorem herm_zero_right (H : IsHerm c h) (x : V) : h x 0 = 0 := by
  have := H.smul_right 0 x 0
  simpa using this

theorem herm_zero_left (H : IsHerm c h) (x : V) : h 0 x = 0 := by
  rw [H.symm x 0, herm_zero_right H, map_zero]

theorem herm_add_left (H : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [H.symm z (x + y), H.add_right, map_add (f := _), ← H.symm z x, ← H.symm z y]

theorem herm_smul_left (H : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [H.symm y (a • x), H.smul_right, map_mul, ← H.symm y x]

def hl (H : IsHerm c h) (w : V) : V →ₗ[R] R where
  toFun := h w
  map_add' := H.add_right w
  map_smul' a y := by simpa using H.smul_right a w y

@[simp] theorem hl_apply (H : IsHerm c h) (w z : V) : hl H w z = h w z := rfl

theorem smul_mem_of {L : Submodule 𝔬 V} {a : R} (ha : a ∈ 𝔬) {v : V} (hv : v ∈ L) : a • v ∈ L :=
  L.smul_mem ⟨a, ha⟩ hv

theorem common_denom (den : ∀ a : R, ∃ s ∈ 𝔬, IsUnit s ∧ s * a ∈ 𝔬) {ι : Type} (S : Finset ι) (a : ι → R) :
    ∃ s ∈ 𝔬, IsUnit s ∧ ∀ i ∈ S, s * a i ∈ 𝔬 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 𝔬.one_mem, isUnit_one, by simp⟩
  | insert i S _ ih =>
    obtain ⟨s, hs, hu, hS⟩ := ih
    obtain ⟨t, ht, hv, hi⟩ := den (a i)
    refine ⟨s * t, 𝔬.mul_mem hs ht, hu.mul hv, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [mul_assoc]; exact 𝔬.mul_mem hs hi
    · rw [mul_right_comm]; exact 𝔬.mul_mem (hS j hj) ht

theorem evenInt_span (H : IsHerm c h) (inv : ∀ a, c (c a) = a) (cm : ∀ a ∈ 𝔬, c a ∈ 𝔬) (G : Set V)
    (h1 : ∀ g ∈ G, ∀ g' ∈ G, h g g' ∈ 𝔬) (h2 : ∀ g ∈ G, ∃ a ∈ 𝔬, h g g = a + c a) :
    IsEvenInt c 𝔬 h (Submodule.span 𝔬 G) := by
  have s1 : ∀ g ∈ G, ∀ z ∈ Submodule.span 𝔬 G, h g z ∈ 𝔬 := by
    intro g hg z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact h1 g hg x hx
    | zero => rw [herm_zero_right H]; exact 𝔬.zero_mem
    | add x y _ _ hx hy => rw [H.add_right]; exact 𝔬.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, H.smul_right]
      exact 𝔬.mul_mem a.2 hx
  have s2 : ∀ z ∈ Submodule.span 𝔬 G, ∀ z' ∈ Submodule.span 𝔬 G, h z z' ∈ 𝔬 := by
    intro z hz z' hz'
    induction hz using Submodule.span_induction with
    | mem x hx => exact s1 x hx z' hz'
    | zero => rw [herm_zero_left H]; exact 𝔬.zero_mem
    | add x y _ _ hx hy => rw [herm_add_left H]; exact 𝔬.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, herm_smul_left H]
      exact 𝔬.mul_mem (cm _ a.2) hx
  refine ⟨s2, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx => exact h2 x hx
  | zero => exact ⟨0, 𝔬.zero_mem, by simp [herm_zero_right H]⟩
  | add x y hx' hy' hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    refine ⟨a + b + h x y, 𝔬.add_mem (𝔬.add_mem ha hb) (s2 x hx' y hy'), ?_⟩
    rw [H.add_right, herm_add_left H, herm_add_left H, ea, eb, H.symm x y, map_add (f := _), map_add (f := _)]
    ring
  | smul a x _ hx =>
    obtain ⟨b, hb, eb⟩ := hx
    refine ⟨c a * a * b, 𝔬.mul_mem (𝔬.mul_mem (cm _ a.2) a.2) hb, ?_⟩
    rw [Subring.smul_def, H.smul_right, herm_smul_left H, eb, map_mul, map_mul, inv]
    ring

theorem exists_maxEven (Hr : IsHermRing c 𝔬) (H : IsHerm c h) (Hp : IsPerfect h) (L₀ : Submodule 𝔬 V)
    (hL : IsLat 𝔬 L₀) (hE : IsEvenInt c 𝔬 h L₀) : ∃ L, L₀ ≤ L ∧ IsMaxEven c 𝔬 h L := by
  haveI := Hr.noeth
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL.1
  have hgL : ∀ i, g i ∈ L₀ := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  let D : Submodule 𝔬 V :=
    { carrier := {z | ∀ i, h (g i) z ∈ 𝔬}
      add_mem' := fun {a b} ha hb i => by
        rw [H.add_right]; exact 𝔬.add_mem (ha i) (hb i)
      zero_mem' := fun i => by rw [herm_zero_right H]; exact 𝔬.zero_mem
      smul_mem' := fun a z hz i => by
        rw [Subring.smul_def, H.smul_right]; exact 𝔬.mul_mem a.2 (hz i) }
  let f : D →ₗ[𝔬] (Fin m → 𝔬) :=
    { toFun := fun z i => ⟨h (g i) z, z.2 i⟩
      map_add' := fun a b => by
        funext i; apply Subtype.ext; exact H.add_right _ _ _
      map_smul' := fun a z => by
        funext i; apply Subtype.ext
        change h (g i) ((a : R) • (z : V)) = (a : R) * h (g i) z
        exact H.smul_right _ _ _ }
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun z hz => ?_
    have h0 : ∀ i, h (g i) z = 0 := fun i => congrArg Subtype.val (congrFun hz i)
    have h1 : ∀ w ∈ L₀, h w z = 0 := by
      intro w hw
      rw [← hg] at hw
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h0 i
      | zero => exact herm_zero_left H _
      | add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]
      | smul a x _ hx => rw [Subring.smul_def, herm_smul_left H, hx, mul_zero]
    have h2 : ∀ w ∈ Submodule.span R (L₀ : Set V), h w z = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => exact herm_zero_left H _
      | add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]
      | smul a x _ hx => rw [herm_smul_left H, hx, mul_zero]
    apply Subtype.ext
    refine Hp.nondeg _ fun w => ?_
    rw [H.symm w, h2 w (by rw [hL.2]; trivial), map_zero]
  haveI : IsNoetherian 𝔬 D := isNoetherian_of_injective f finj
  have hD : ∀ L' : Submodule 𝔬 V, IsEvenInt c 𝔬 h L' → L₀ ≤ L' → L' ≤ D :=
    fun L' hE' hle z hz i => hE'.1 _ (hle (hgL i)) _ hz
  let S : Set (Submodule 𝔬 D) := {N | IsEvenInt c 𝔬 h (N.map D.subtype) ∧ L₀ ≤ N.map D.subtype}
  have hcm : ∀ L' : Submodule 𝔬 V, L' ≤ D → (L'.comap D.subtype).map D.subtype = L' := fun L' hl => by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.2 hl
  have hS : (L₀.comap D.subtype) ∈ S := by
    have := hcm L₀ (hD L₀ hE le_rfl)
    simp only [S, Set.mem_setOf_eq, this]
    exact ⟨hE, le_rfl⟩
  obtain ⟨N, hN, hmin⟩ := (wellFounded_gt (α := Submodule 𝔬 D)).has_min S ⟨_, hS⟩
  refine ⟨N.map D.subtype, hN.2, ⟨?_, ?_⟩, hN.1, fun L' hE' hle => ?_⟩
  · exact (IsNoetherian.noetherian N).map _
  · refine top_le_iff.1 ?_
    rw [← hL.2]
    exact Submodule.span_mono hN.2
  · have hDL : L' ≤ D := hD L' hE' (hN.2.trans hle)
    have hmem : L'.comap D.subtype ∈ S := by
      simp only [S, Set.mem_setOf_eq, hcm L' hDL]
      exact ⟨hE', hN.2.trans hle⟩
    have hNle : N ≤ L'.comap D.subtype := by
      rw [← Submodule.map_le_iff_le_comap]; exact hle
    have : ¬ N < L'.comap D.subtype := hmin _ hmem
    have heq : N = L'.comap D.subtype := by
      by_contra hne
      exact this (lt_of_le_of_ne hNle hne)
    rw [heq, hcm L' hDL]

theorem isAdapted_of {r : ℕ} {x y : Fin r → V} {L : Submodule 𝔬 V} (hE : IsEvenInt c 𝔬 h L)
    (hx : ∀ i, x i ∈ L) (hy : ∀ i, y i ∈ L) : IsAdapted 𝔬 h x y L := by
  intro z
  constructor
  · intro hz
    have ha : ∀ i, h (x i) z ∈ 𝔬 := fun i => hE.1 _ (hx i) _ hz
    have hb : ∀ i, h (y i) z ∈ 𝔬 := fun i => hE.1 _ (hy i) _ hz
    refine ⟨ha, hb, L.sub_mem (L.sub_mem hz ?_) ?_⟩
    · exact L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)
    · exact L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)
  · rintro ⟨ha, hb, hz⟩
    have e : z = (z - ∑ i, h (y i) z • x i - ∑ i, h (x i) z • y i) + ∑ i, h (y i) z • x i
        + ∑ i, h (x i) z • y i := by abel
    rw [e]
    refine L.add_mem (L.add_mem hz ?_) ?_
    · exact L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)
    · exact L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)

end Lemmas

theorem exists_maxEven_adapted : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 →
    ∀ {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    ∀ {r : ℕ} (x y : Fin r → V), IsFrame h x y → ∃ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L ∧ IsAdapted 𝔬 h x y L := by
  intro R _ c 𝔬 Hr V _ _ _ h H Hp r x y F
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := R) (M := V)
  have hyx : ∀ j i, h (y j) (x i) = if i = j then 1 else 0 := by
    intro j i
    rw [H.symm (x i) (y j), F.xy]
    split_ifs <;> simp
  let u : Fin m → V := fun k => e k - ∑ i, h (y i) (e k) • x i - ∑ i, h (x i) (e k) • y i
  have hux : ∀ j k, h (x j) (u k) = 0 := by
    intro j k
    have : hl H (x j) (u k) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.xx, F.xy]
      simp
    exact this
  have huy : ∀ j k, h (y j) (u k) = 0 := by
    intro j k
    have : hl H (y j) (u k) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.yy, hyx]
      simp
    exact this
  obtain ⟨t, ht⟩ := Hr.two.exists_right_inv
  have hct : c t = t := by
    have h2 : (2 : R) * c t = 1 := by
      have := congrArg c ht
      rw [map_mul, map_ofNat c 2, map_one] at this
      exact this
    calc c t = (2 * t) * c t := by rw [ht, one_mul]
      _ = t * (2 * c t) := by ring
      _ = t := by rw [h2, mul_one]
  obtain ⟨s, hs𝔬, hsu, hs⟩ := common_denom Hr.denom
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => h (u p.1) (u p.2) * t)
  have two𝔬 : (2 : R) ∈ 𝔬 := by
    have : (2 : R) = 1 + 1 := by norm_num
    rw [this]; exact 𝔬.add_mem 𝔬.one_mem 𝔬.one_mem
  let w : Fin m → V := fun k => s • u k
  have hxw : ∀ i k, h (x i) (w k) = 0 := fun i k => by
    simp only [w, H.smul_right, hux, mul_zero]
  have hyw : ∀ i k, h (y i) (w k) = 0 := fun i k => by
    simp only [w, H.smul_right, huy, mul_zero]
  have hwx : ∀ k i, h (w k) (x i) = 0 := fun k i => by
    rw [H.symm (x i) (w k), hxw, map_zero]
  have hwy : ∀ k i, h (w k) (y i) = 0 := fun k i => by
    rw [H.symm (y i) (w k), hyw, map_zero]
  have hA : ∀ i j, c s * (s * (h (u i) (u j) * t)) ∈ 𝔬 := fun i j =>
    𝔬.mul_mem (Hr.conj_mem _ hs𝔬) (hs (i, j) (Finset.mem_univ _))
  have hww : ∀ i j, h (w i) (w j) = 2 * (c s * (s * (h (u i) (u j) * t))) := fun i j => by
    simp only [w, H.smul_right, herm_smul_left H]
    linear_combination (-(c s * s * h (u i) (u j))) * ht
  have ite𝔬 : ∀ i j : Fin r, (if i = j then (1 : R) else 0) ∈ 𝔬 := fun i j => by
    split_ifs
    · exact 𝔬.one_mem
    · exact 𝔬.zero_mem
  let G : Set V := Set.range x ∪ Set.range y ∪ Set.range w
  have g1 : ∀ g ∈ G, ∀ g' ∈ G, h g g' ∈ 𝔬 := by
    rintro g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) g' ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · rw [F.xx]; exact 𝔬.zero_mem
    · rw [F.xy]; exact ite𝔬 _ _
    · rw [hxw]; exact 𝔬.zero_mem
    · rw [hyx]; exact ite𝔬 _ _
    · rw [F.yy]; exact 𝔬.zero_mem
    · rw [hyw]; exact 𝔬.zero_mem
    · rw [hwx]; exact 𝔬.zero_mem
    · rw [hwy]; exact 𝔬.zero_mem
    · rw [hww]; exact 𝔬.mul_mem two𝔬 (hA i j)
  have g2 : ∀ g ∈ G, ∃ a ∈ 𝔬, h g g = a + c a := by
    rintro g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨0, 𝔬.zero_mem, by simp [F.xx]⟩
    · exact ⟨0, 𝔬.zero_mem, by simp [F.yy]⟩
    · refine ⟨_, hA i i, ?_⟩
      have hc : c (c s * (s * (h (u i) (u i) * t))) = c s * (s * (h (u i) (u i) * t)) := by
        simp only [map_mul, Hr.invol, hct, ← H.symm]
        ring
      rw [hc, hww]
      ring
  have hE := evenInt_span (𝔬 := 𝔬) H Hr.invol Hr.conj_mem G g1 g2
  have hfin : G.Finite := ((Set.finite_range x).union (Set.finite_range y)).union (Set.finite_range w)
  have hLat : IsLat 𝔬 (Submodule.span 𝔬 G) := by
    refine ⟨Submodule.fg_span hfin, ?_⟩
    set T := Submodule.span R ((Submodule.span 𝔬 G : Submodule 𝔬 V) : Set V) with hT
    have hG : ∀ g ∈ G, g ∈ T := fun g hg => Submodule.subset_span (Submodule.subset_span hg)
    have hu : ∀ k, u k ∈ T := by
      intro k
      obtain ⟨v, rfl⟩ := hsu
      have : u k = (↑v⁻¹ : R) • w k := by
        simp only [w, smul_smul, Units.inv_mul, one_smul]
      rw [this]
      exact T.smul_mem _ (hG _ (Or.inr ⟨k, rfl⟩))
    refine top_le_iff.1 ?_
    rw [← he, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have ek : e k = u k + ∑ i, h (y i) (e k) • x i + ∑ i, h (x i) (e k) • y i := by
      simp only [u]; abel
    change e k ∈ T
    rw [ek]
    refine T.add_mem (T.add_mem (hu k) ?_) ?_
    · exact T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inl ⟨i, rfl⟩)))
    · exact T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inr ⟨i, rfl⟩)))
  obtain ⟨L, hle, hmax⟩ := exists_maxEven Hr H Hp _ hLat hE
  refine ⟨L, hmax, isAdapted_of hmax.2.1 (fun i => hle ?_) (fun i => hle ?_)⟩
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))

end GlobalTheory.CompanionTheory.KFin.Adapted

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLatticeStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_max_even_adapted_lattice : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 → ∀ {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h → ∀ {r : ℕ} (x y : Fin r → V), IsFrame h x y → ∃ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L ∧ IsAdapted 𝔬 h x y L := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted | exact GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted | (intros; apply GlobalTheory.CompanionTheory.KFin.Adapted.exists_maxEven_adapted <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolic
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.LeviPt

section Abstract

variable {K : Type} [CommRing K] (c : K →+* K)

theorem cT_add {m p : Type} (M N : Matrix m p K) : cT c (M + N) = cT c M + cT c N := by
  ext i j; simp [cT]

theorem cT_sub {m p : Type} (M N : Matrix m p K) : cT c (M - N) = cT c M - cT c N := by
  ext i j; simp [cT]

theorem cT_cT (hc : ∀ x, c (c x) = x) {m p : Type} (M : Matrix m p K) : cT c (cT c M) = M := by
  ext i j; simp [cT, hc]

theorem cT_diagonal {m : Type} [DecidableEq m] (d : m → K) :
    cT c (diagonal d) = diagonal (fun i => c (d i)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cT]
  · simp [cT, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem levi_core (hc : ∀ x, c (c x) = x) {n r : ℕ} {Jh : Matrix (Fin n) (Fin n) K}
    {Xa Ya : Matrix (Fin n) (Fin r) K} {Xd Yd : Matrix (Fin r) (Fin n) K}
    (hJ : cT c Jh = Jh) (hXd : Xd = cT c Xa * Jh) (hYd : Yd = cT c Ya * Jh)
    (hxx : Xd * Xa = 0) (hyy : Yd * Ya = 0) (hxy : Xd * Ya = 1)
    (g : GL (Fin n) K) (hg : cT c (g : Matrix (Fin n) (Fin n) K) * Jh * (g : Matrix (Fin n) (Fin n) K) = Jh)
    (B : Matrix (Fin r) (Fin r) K) (hBt : B.BlockTriangular id)
    (hB : (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * B)
    (L : Matrix (Fin n) (Fin n) K)
    (hL : L = Xa * diagonal (fun i => (Yd * (g : Matrix (Fin n) (Fin n) K) * Xa) i i) * Yd
      + Ya * diagonal (fun i => (Xd * (g : Matrix (Fin n) (Fin n) K) * Ya) i i) * Xd
      + (1 - Xa * Yd - Ya * Xd) * (g : Matrix (Fin n) (Fin n) K) * (1 - Xa * Yd - Ya * Xd)) :
    ∃ u : GL (Fin n) K, (u : Matrix (Fin n) (Fin n) K) = L ∧ cT c L * Jh * L = Jh ∧
      (∃ d, L * Xa = Xa * diagonal d) ∧ (∃ d', L * Ya = Ya * diagonal d') ∧
      (∃ B' : Matrix (Fin r) (Fin r) K, B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧
        ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * B') ∧
      ∀ z : Fin n → K, Xd *ᵥ z = 0 → ∃ a : Fin r → K,
        (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ z = Xa *ᵥ a := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) K, M = g := ⟨_, rfl⟩
  obtain ⟨Mi, hMi⟩ : ∃ Mi : Matrix (Fin n) (Fin n) K, Mi = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨_, rfl⟩
  have hMMi : M * Mi = 1 := by rw [hM, hMi]; exact Units.mul_inv g
  have hMiM : Mi * M = 1 := by rw [hM, hMi]; exact Units.inv_mul g
  rw [← hM] at hg hB hL
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) K, P = 1 - Xa * Yd - Ya * Xd := ⟨_, rfl⟩
  rw [← hP] at hL
  have hyx : Yd * Xa = 1 := by
    have h := congrArg (cT c) hxy
    rw [Formalism.UG.cT_mul, hXd, Formalism.UG.cT_mul, hJ, cT_cT c hc, Formalism.UG.cT_one] at h
    rw [hYd, Matrix.mul_assoc]; exact h
  have hcXd : cT c Xd = Jh * Xa := by rw [hXd, Formalism.UG.cT_mul, hJ, cT_cT c hc]
  have hcYd : cT c Yd = Jh * Ya := by rw [hYd, Formalism.UG.cT_mul, hJ, cT_cT c hc]
  have exx : ∀ {k : Type} (N : Matrix (Fin r) k K), Xd * (Xa * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hxx, Matrix.zero_mul]
  have eyy : ∀ {k : Type} (N : Matrix (Fin r) k K), Yd * (Ya * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hyy, Matrix.zero_mul]
  have exy : ∀ {k : Type} (N : Matrix (Fin r) k K), Xd * (Ya * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]
  have eyx : ∀ {k : Type} (N : Matrix (Fin r) k K), Yd * (Xa * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul]
  have hPXa : P * Xa = 0 := by
    rw [hP]; simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, hxx, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have hPYa : P * Ya = 0 := by
    rw [hP]; simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyy, hxy, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have hXdP : Xd * P = 0 := by
    rw [hP]; simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hxx, hxy, Matrix.zero_mul,
      Matrix.one_mul, sub_self, sub_zero]
  have hYdP : Yd * P = 0 := by
    rw [hP]; simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hyy, hyx, Matrix.zero_mul,
      Matrix.one_mul, sub_self, sub_zero]
  have hPP : P * P = P := by
    have h : P * P = P * (1 - Xa * Yd - Ya * Xd) := by rw [← hP]
    rw [h, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPXa, ← Matrix.mul_assoc, hPYa,
      Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have ePP : ∀ {k : Type} (N : Matrix (Fin n) k K), P * (P * N) = P * N := fun N => by
    rw [← Matrix.mul_assoc, hPP]
  have ePx : ∀ {k : Type} (N : Matrix (Fin r) k K), P * (Xa * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hPXa, Matrix.zero_mul]
  have ePy : ∀ {k : Type} (N : Matrix (Fin r) k K), P * (Ya * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hPYa, Matrix.zero_mul]
  have exP : ∀ {k : Type} (N : Matrix (Fin n) k K), Xd * (P * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hXdP, Matrix.zero_mul]
  have eyP : ∀ {k : Type} (N : Matrix (Fin n) k K), Yd * (P * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hYdP, Matrix.zero_mul]
  have hMJ : cT c M * Jh = Jh * Mi := by
    calc cT c M * Jh = cT c M * Jh * (M * Mi) := by rw [hMMi, Matrix.mul_one]
      _ = (cT c M * Jh * M) * Mi := by simp only [Matrix.mul_assoc]
      _ = Jh * Mi := by rw [hg]
  have hBX : cT c B * Xd = Xd * Mi := by
    rw [hXd, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← hB, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc, hMJ]
  have hBC : cT c B * (Xd * M * Ya) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX, Matrix.mul_assoc Xd Mi M, hMiM, Matrix.mul_one, hxy]
  have hCB : (Xd * M * Ya) * cT c B = 1 := mul_eq_one_comm.mp hBC
  have hBiB : cT c (Xd * M * Ya) * B = 1 := by
    have h := congrArg (cT c) hBC
    rwa [Formalism.UG.cT_mul, cT_cT c hc, Formalism.UG.cT_one] at h
  have hBBi : B * cT c (Xd * M * Ya) = 1 := mul_eq_one_comm.mp hBiB
  have hBit : (cT c (Xd * M * Ya)).BlockTriangular id := by
    haveI : Invertible B := invertibleOfRightInverse B _ hBBi
    have h := Matrix.blockTriangular_inv_of_blockTriangular hBt
    rwa [Matrix.inv_eq_right_inv hBBi] at h
  have hdiag : ∀ i, c ((Xd * M * Ya) i i) * B i i = 1 := by
    intro i
    have h := congrFun (congrFun hBiB i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · rw [Matrix.one_apply_eq] at h; exact h
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [hBit h', zero_mul]
      · rw [hBt h', mul_zero]
    · intro h'; exact absurd (Finset.mem_univ i) h'

  have hYMX : Yd * M * Xa = B := by rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  rw [hYMX] at hL
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) K, D = diagonal (fun i => B i i) := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Matrix (Fin r) (Fin r) K, D' = diagonal (fun i => (Xd * M * Ya) i i) := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ Ds : Matrix (Fin r) (Fin r) K, Ds = diagonal (fun i => c (B i i)) := ⟨_, rfl⟩
  obtain ⟨D's, hD's⟩ : ∃ D's : Matrix (Fin r) (Fin r) K, D's = diagonal (fun i => c ((Xd * M * Ya) i i)) :=
    ⟨_, rfl⟩
  rw [← hD, ← hD'] at hL
  have hcD : cT c D = Ds := by rw [hD, hDs, cT_diagonal]
  have hcD' : cT c D' = D's := by rw [hD', hD's, cT_diagonal]
  have eDsD' : ∀ {k : Type} (N : Matrix (Fin r) k K), Ds * (D' * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hDs, hD', diagonal_mul_diagonal]
    convert Matrix.one_mul N
    rw [← diagonal_one]; congr 1; funext i
    have h := congrArg c (hdiag i)
    rw [map_mul, hc, map_one, mul_comm] at h
    exact h
  have eD'sD : ∀ {k : Type} (N : Matrix (Fin r) k K), D's * (D * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hD's, hD, diagonal_mul_diagonal]
    convert Matrix.one_mul N
    rw [← diagonal_one]; congr 1; funext i
    exact hdiag i
  have hXdMP : Xd * (M * P) = 0 := by
    have h1 : cT c B * (Xd * (M * P)) = 0 := by
      rw [← Matrix.mul_assoc, hBX, Matrix.mul_assoc, ← Matrix.mul_assoc Mi, hMiM, Matrix.one_mul, hXdP]
    calc Xd * (M * P) = (Xd * M * Ya * cT c B) * (Xd * (M * P)) := by rw [hCB, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc _ (cT c B), h1, Matrix.mul_zero]
  have hMiXa : Mi * Xa = Xa * cT c (Xd * M * Ya) := by
    calc Mi * Xa = Mi * Xa * (B * cT c (Xd * M * Ya)) := by rw [hBBi, Matrix.mul_one]
      _ = Mi * (M * Xa) * cT c (Xd * M * Ya) := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = Xa * cT c (Xd * M * Ya) := by rw [← Matrix.mul_assoc Mi, hMiM, Matrix.one_mul]
  have h1 : P * (M * P) = M * P - Xa * (Yd * (M * P)) := by
    rw [show P * (M * P) = (1 - Xa * Yd - Ya * Xd) * (M * P) by rw [← hP], Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_assoc Xa, Matrix.mul_assoc Ya, hXdMP, Matrix.mul_zero, sub_zero]
  have hPMiPMP : P * (Mi * (P * (M * P))) = P := by
    rw [h1, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc Mi M, hMiM, Matrix.one_mul, hPP,
      ← Matrix.mul_assoc Mi Xa, hMiXa, Matrix.mul_assoc Xa, ePx, sub_zero]
  obtain ⟨m', hm'⟩ : ∃ m' : Matrix (Fin n) (Fin n) K, m' = Ya * (Ds * Xd) + Xa * (D's * Yd) + P * (Mi * P) :=
    ⟨_, rfl⟩
  have hm'L : m' * L = 1 := by
    clear * - hm' hL exx eyy exy eyx exP eyP ePx ePy ePP eDsD' eD'sD hPMiPMP hP
    rw [hm', hL]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, exx, eyy, exy, eyx, exP, eyP, ePx, ePy,
      ePP, eDsD', eD'sD, hPMiPMP, Matrix.mul_zero, add_zero, zero_add]
    rw [hP]; abel
  have hLm' : L * m' = 1 := mul_eq_one_comm.mp hm'L
  have hPJ : cT c P * Jh = Jh * P := by
    rw [hP, cT_sub, cT_sub, Formalism.UG.cT_one, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcYd, hcXd]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hXd.symm,
      hYd.symm]
    abel
  have ePJ : ∀ (N : Matrix (Fin n) (Fin n) K), cT c P * (Jh * N) = Jh * (P * N) := fun N => by
    rw [← Matrix.mul_assoc, hPJ, Matrix.mul_assoc]
  have eMJ : ∀ (N : Matrix (Fin n) (Fin n) K), cT c M * (Jh * N) = Jh * (Mi * N) := fun N => by
    rw [← Matrix.mul_assoc, hMJ, Matrix.mul_assoc]
  have hcL : cT c L * Jh = Jh * m' := by
    rw [hL, hm']
    simp only [cT_add, Formalism.UG.cT_mul, hcXd, hcYd, hcD, hcD', Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
      hXd.symm, hYd.symm, hPJ, eMJ, ePJ]
  have hunit : cT c L * Jh * L = Jh := by
    rw [hcL, Matrix.mul_assoc, hm'L, Matrix.mul_one]
  have hLXa : L * Xa = Xa * D := by
    rw [hL]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hyx, hxx, hPXa, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hLYa : L * Ya = Ya * D' := by
    rw [hL]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hyy, hxy, hPYa, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add]
  have em'Xa : ∀ {k : Type} (N : Matrix (Fin r) k K), m' * (Xa * N) = Xa * (D's * N) := fun N => by
    rw [hm']
    simp only [Matrix.add_mul, Matrix.mul_assoc, exx, eyx, ePx, Matrix.mul_zero, add_zero, zero_add]
  have hLP : L * P = P * (M * P) := by
    rw [hL]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYdP, hXdP, hPP, Matrix.mul_zero, zero_add]
  refine ⟨⟨L, m', hLm', hm'L⟩, rfl, hunit, ⟨_, hD ▸ hLXa⟩, ⟨_, hD' ▸ hLYa⟩, ?_, ?_⟩
  · refine ⟨D's * B, ?_, ?_, ?_⟩
    · intro i j h
      rw [hD's, diagonal_mul, hBt h, mul_zero]
    · intro i
      rw [hD's, diagonal_mul]
      exact hdiag i
    · change m' * (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * (D's * B)
      rw [← hM, Matrix.mul_assoc, hB, em'Xa]
  · intro z hz
    refine ⟨(D's * B * Yd + D's * (Yd * (M * P)) - Yd) *ᵥ z, ?_⟩
    change (m' * (g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ z = _
    rw [← hM]
    have hz' : z = (Xa * Yd + P) *ᵥ z := by
      rw [show Xa * Yd + P = 1 - Ya * Xd by rw [hP]; abel, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]
    have h2 : m' * (M * P) = Xa * (D's * (Yd * (M * P))) + P := by
      conv_lhs => rw [show M * P = Xa * (Yd * (M * P)) + P * (M * P) by rw [h1]; abel]
      rw [Matrix.mul_add, em'Xa, ← hLP, ← Matrix.mul_assoc m' L P, hm'L, Matrix.one_mul]
    have key : (m' * M - 1) * (Xa * Yd + P) = Xa * (D's * B * Yd + D's * (Yd * (M * P)) - Yd) := by
      calc (m' * M - 1) * (Xa * Yd + P) = m' * (M * Xa) * Yd + m' * (M * P) - Xa * Yd - P := by
            simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]; abel
        _ = Xa * (D's * B) * Yd + (Xa * (D's * (Yd * (M * P))) + P) - Xa * Yd - P := by rw [hB, em'Xa, h2]
        _ = Xa * (D's * B * Yd + D's * (Yd * (M * P)) - Yd) := by
            simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]; abel
    conv_lhs => rw [hz']
    rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]

end Abstract

section Place

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hτ⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [hτ, hτ, star_star]

theorem sigR_invol {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : A ⊗[F] E) : sigR A σ (sigR A σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) (e : E) : sigR A σ (inclR A e) = inclR A (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) {a b : ℕ} (N : Matrix (Fin a) (Fin b) E) :
    cT (sigR A σ) (N.map (inclR (F := F) A)) = (cT (σ : E →+* E) N).map (inclR (F := F) A) := by
  ext i j; simp [cT, sigR_inclR]

theorem exists_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW A _ _ _ p B hBt hB
  have hc := sigR_invol A (sigma_invol hCM)
  have hJh : cT (sigR A σ) (J.map (inclR (F := F) A)) = J.map (inclR (F := F) A) := by
    rw [cT_map_inclR]; congr 1; ext i j; exact hJ.1 i j
  have hmap0 : ((0 : Matrix (Fin r) (Fin r) E)).map (inclR (F := F) A) = 0 := by simp
  have hmap1 : ((1 : Matrix (Fin r) (Fin r) E)).map (inclR (F := F) A) = 1 := by simp
  have hg : cT (sigR A σ) ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) *
      J.map (inclR (F := F) A) * ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) =
      J.map (inclR (F := F) A) := by
    have h : matHom A σ J p ∈ HR A σ J := (show ↥(HR A σ J) from p).2
    exact h
  have hXd : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) =
      cT (sigR A σ) (X.map (inclR (F := F) A)) * J.map (inclR (F := F) A) := by
    rw [Matrix.map_mul, cT_map_inclR]
  have hYd : (cT (σ : E →+* E) Y * J).map (inclR (F := F) A) =
      cT (sigR A σ) (Y.map (inclR (F := F) A)) * J.map (inclR (F := F) A) := by
    rw [Matrix.map_mul, cT_map_inclR]
  have hxx : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) * X.map (inclR (F := F) A) = 0 := by
    rw [← Matrix.map_mul, hW.xx, hmap0]
  have hyy : (cT (σ : E →+* E) Y * J).map (inclR (F := F) A) * Y.map (inclR (F := F) A) = 0 := by
    rw [← Matrix.map_mul, hW.yy, hmap0]
  have hxy : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) * Y.map (inclR (F := F) A) = 1 := by
    rw [← Matrix.map_mul, hW.xy, hmap1]
  obtain ⟨u, hu, hunit, hXa, hYa, hB', hz⟩ := levi_core (sigR A σ) hc hJh hXd hYd hxx hyy hxy
    (matHom A σ J p) hg B hBt hB (leviMat σ J A X Y (matHom A σ J p).1) rfl
  have hmem : u ∈ HR A σ J := by
    show cT (sigR A σ) (u : Matrix (Fin n) (Fin n) (A ⊗[F] E)) * J.map (inclR (F := F) A) *
      (u : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = J.map (inclR (F := F) A)
    rw [hu]; exact hunit
  let m : HA A σ J := (⟨u, hmem⟩ : ↥(HR A σ J))
  have hmu : matHom A σ J m = u := rfl
  have e : ((matHom A σ J (m⁻¹ * p) : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) =
      ((u⁻¹ : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) *
        ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) := by
    rw [map_mul, map_inv, Units.val_mul, hmu]
  refine ⟨m, by rw [hmu]; exact hu, by rw [hmu, hu]; exact hXa, by rw [hmu, hu]; exact hYa, ?_, ?_⟩
  · obtain ⟨B', h1, h2, h3⟩ := hB'
    exact ⟨B', h1, h2, by rw [e]; exact h3⟩
  · intro z hz0
    obtain ⟨a, ha⟩ := hz z hz0
    exact ⟨a, by rw [e]; exact ha⟩

end Place

end GlobalTheory.CompanionTheory.KFin.LeviPt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_mem_minimal_parabolic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | exact GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | (intros; apply GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicLocal
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extH tensNU tensNU_tmul)

namespace GlobalTheory.CompanionTheory.KFin

section Step

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
  [CommRing R'] [Algebra F R'] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b)

theorem tensNU_mul_inclR (u : R ⊗[F] E) (e : E) :
    tensNU j hj u * inclR (F := F) R' e = tensNU j hj (u * inclR (F := F) R e) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]
  | tmul a e' => simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem map_tensNU_mul_inclR {a b c : Type} [Fintype b] (A : Matrix a b (R ⊗[F] E)) (X : Matrix b c E) :
    A.map (tensNU j hj) * X.map (inclR (F := F) R') = (A * X.map (inclR (F := F) R)).map (tensNU j hj) := by
  ext r s
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, tensNU_mul_inclR, map_sum]

theorem inclR_mul_map_tensNU {a b c : Type} [Fintype b] (X : Matrix a b E) (A : Matrix b c (R ⊗[F] E)) :
    X.map (inclR (F := F) R') * A.map (tensNU j hj) = (X.map (inclR (F := F) R) * A).map (tensNU j hj) := by
  ext r s
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, mul_comm (inclR (F := F) R' _), mul_comm (inclR (F := F) R _),
    tensNU_mul_inclR, map_sum]

theorem mat_extH_eq_add (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J) :
    (HA.mat R' σ J (extH σ J j hj g)).1 = 1 + ((HA.mat R σ J g).1 - 1).map (tensNU j hj) := by
  ext r s
  rw [GlobalTheory.AutFunCompare.mat_extH]
  by_cases h : r = s
  · subst h
    simp [map_sub]
    ring
  · simp [Matrix.one_apply, h]

theorem extH_stab (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : HA R σ J)
    (X : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (hB : B.BlockTriangular id)
    (h : (HA.mat R σ J g).1 * X.map (inclR (F := F) R) = X.map (inclR (F := F) R) * B) :
    ∃ B' : Matrix (Fin r) (Fin r) (R' ⊗[F] E), B'.BlockTriangular id ∧
      (HA.mat R' σ J (extH σ J j hj g)).1 * X.map (inclR (F := F) R') = X.map (inclR (F := F) R') * B' := by
  refine ⟨1 + (B - 1).map (tensNU j hj), ?_, ?_⟩
  · intro a b hab
    have hne : a ≠ b := fun e => by subst e; exact lt_irrefl _ hab
    have h0 : B a b = 0 := hB hab
    simp [Matrix.one_apply, hne, h0]
  · rw [mat_extH_eq_add, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, map_tensNU_mul_inclR,
      inclR_mul_map_tensNU, Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]

end Step

theorem emb_mem_minPar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E))
    (hB : B.BlockTriangular id)
    (h : (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B) :
    emb σ J v p ∈ minPar σ J X := by
  obtain ⟨B₁, hB₁, h₁⟩ := extH_stab (singleFin v) (singleFin_mul v) σ J p X B hB h
  obtain ⟨B₂, hB₂, h₂⟩ := extH_stab (R' := AF F) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl) σ J _ X B₁ hB₁ h₁
  exact ⟨B₂, hB₂, h₂⟩

end GlobalTheory.CompanionTheory.KFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicLocalStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_mem_minimal_parabolic_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (v : HeightOneSpectrum (𝓞 F)) (p : GLoc σ J v) (B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E)), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → emb σ J v p ∈ minPar σ J X := by
  first | exact @GlobalTheory.CompanionTheory.KFin.emb_mem_minPar | exact GlobalTheory.CompanionTheory.KFin.emb_mem_minPar | (intros; apply GlobalTheory.CompanionTheory.KFin.emb_mem_minPar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompact
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

open GlobalTheory.CompanionTheory.KFin Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem matHom_mapH_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 =
      (matHom A σ J g).1.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  ext i j
  exact GlobalTheory.AutFunCompare.mat_mapH _ _ _ _ _ _

theorem map_adMat_kfin {A A' : Type} [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (X : Matrix (Fin n) (Fin r) E) :
    (X.map (inclR (F := F) A)).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = X.map (inclR (F := F) A') := by
  ext i j
  simp [inclR]

theorem flag_map_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E))
    (h : (matHom A σ J g).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 * X.map (inclR (F := F) A') =
      X.map (inclR (F := F) A') * B.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin r) (A ⊗[F] E) =>
    M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) h
  rw [Matrix.map_mul, Matrix.map_mul, map_adMat_kfin] at this
  rw [matHom_mapH_kfin]
  exact this

theorem exists_compact_iwasawa_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ finPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW
  let L₀ := stdLattice E n
  haveI : Submodule.IsFullLattice E L₀ := isLattice_stdLattice
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hCM.2.2.2, hCM.2.2.2, star_star])
  have hae : ∀ᶠ v in cofinite,
      IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v) := by
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j),
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J⁻¹ i j),
      eventually_one_tmul_mem_intLoc (F := F) (2⁻¹ : E),
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (X a i),
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (Y a i)]
      with v h1 h2 h3 h4 h5
    exact AE.isMaxEven_isAdapted_std hσ hJ h1 h2 h3 (colV v X) (colV v Y) h4 h5
  have hT : ∀ v, FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) := fun v => GlobalTheory.T.flag_transitive_of_base _ _ (GlobalTheory.T.local_hermitian_ring hCM v) (GlobalTheory.T.local_hermitian_has_base hCM v)
  have hex : ∀ v, ∃ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E),
      IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ ∧
      (IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v) → Λ = latLoc F L₀ v) := by
    intro v
    by_cases hg : IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v)
    · exact ⟨_, hg.1, hg.2, fun _ => rfl⟩
    · obtain ⟨L, h1, h2⟩ := GlobalTheory.T.exists_max_even_adapted_lattice _ (intLoc F E v) (GlobalTheory.T.local_hermitian_ring hCM v) (hR (Fv F v) σ J) (GlobalTheory.T.local_form_hermitian_perfect hCM hJ v).1
        (GlobalTheory.T.local_form_hermitian_perfect hCM hJ v).2 (colV v X) (colV v Y) (GlobalTheory.T.local_witt_frame hCM hJ hW v)
      exact ⟨L, h1, h2, fun h => absurd h hg⟩
  choose Λ hΛ1 hΛ2 hΛ3 using hex
  have hev : ∀ᶠ v in cofinite, Λ v = latLoc F L₀ v := hae.mono fun v h => hΛ3 v h
  have hstab : ∀ v, Λ v = latLoc F L₀ v → (stabLat σ J (Λ v) : Subgroup (GLoc σ J v)) = stabLoc σ J L₀ v := by
    intro v e
    rw [e]
    rfl
  let K : Subgroup (GAd σ J) := finPts σ J ⊓ ⨅ v, (stabLat σ J (Λ v)).comap (proj σ J v)
  have memK : ∀ g, g ∈ K ↔ g ∈ finPts σ J ∧ ∀ v, proj σ J v g ∈ stabLat σ J (Λ v) := fun g => by
    simp [K, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨K, inf_le_left, ?_, ?_, ?_⟩
  ·
    obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Λ v = latLoc F L₀ v :=
      ⟨(eventually_cofinite.1 hev).toFinset, fun v hv => by simpa using hv⟩
    have hc := (isRestrGroup_GFin σ J L₀).isCompact_cyl S (fun _ => Set.univ)
      (fun v => (stabLat σ J (Λ v) : Set (GLoc σ J v))) (fun e => e.elim)
      (fun v _ => GlobalTheory.T.lattice_stabilizer_compact hCM hJ v (Λ v) (hΛ1 v).1)
    convert hc.image (continuous_ofFin σ J) using 1
    ext g
    rw [SetLike.mem_coe, memK]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ : g ∈ (ofFin σ J).range := by rwa [range_ofFin]
      refine ⟨y, ⟨fun e => e.elim, fun v _ => ?_, fun v hv => ?_⟩, rfl⟩
      · simpa using h2 v
      · rw [← hstab v (hS v hv)]
        simpa using h2 v
    · rintro ⟨y, ⟨-, h1, h2⟩, rfl⟩
      refine ⟨mem_finPts.2 (by simp), fun v => ?_⟩
      rw [proj_ofFin]
      by_cases hv : v ∈ S
      · exact h1 v hv
      · rw [hstab v (hS v hv)]
        exact h2 v hv
  ·
    intro g hg
    have hfin : {v | proj σ J v g ∉ stabLat σ J (Λ v)}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [hev, eventually_proj_mem_stabLoc σ J L₀ g] with v e hv
      rw [hstab v e]
      exact hv
    let S : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
    choose pl kl hkl hgl Bl hBl hpl using fun v => GlobalTheory.T.max_even_lattice_flag_transitive_local (X := X) hCM hJ hW v (hT v) (Λ v) (hΛ1 v) (proj σ J v g)
    let x : ∀ v : S, GLoc σ J v := fun v => pl v
    have hp1 : embAt σ J S x ∈ minPar σ J X := by
      have : embAt σ J S x ∈ minParSub X hCM hJ hW := by
        refine Subgroup.noncommProd_mem _ (f := fun v : S => emb σ J v (x v))
          (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => ?_
        exact GlobalTheory.T.block_triangular_mem_minimal_parabolic_local (Y := Y) v.1 _ (Bl v.1) (hBl v.1) (hpl v.1)
      exact this
    have hp2 := mem_atPts.1 (embAt_mem σ J S x)
    refine ⟨embAt σ J S x, hp1, hp2.1, (embAt σ J S x)⁻¹ * g, (memK _).2 ⟨mul_mem (inv_mem hp2.1) hg, fun v => ?_⟩, by simp⟩
    rw [map_mul, map_inv]
    by_cases hv : v ∈ S
    · have : proj σ J v (embAt σ J S x) = pl v := proj_embAt σ J S x ⟨v, hv⟩
      rw [this, hgl v, inv_mul_cancel_left]
      exact hkl v
    · rw [hp2.2 v hv, inv_one, one_mul]
      by_contra hc
      exact hv (hfin.mem_toFinset.2 hc)
  ·
    rintro p ⟨B, hB, hpB⟩ hpK
    obtain ⟨hpf, hpv⟩ := (memK p).1 hpK
    obtain ⟨m, hm, ⟨d, hd⟩, ⟨d', hd'⟩, ⟨B', hB', hB1, hu⟩, hz⟩ := GlobalTheory.T.block_triangular_mem_minimal_parabolic hCM hJ hW (AF F) p B hB hpB
    have hmf : m ∈ finPts σ J := by
      refine mem_finPts.2 (Subtype.ext (Units.ext ?_))
      have e1 : (matHom _ σ J (projInf σ J m)).1 = 1 := by
        refine (matHom_mapH_kfin (fstA F) m).trans ?_
        rw [hm, ← GlobalTheory.T.levi_matrix_map_base_change]
        have e2 : (matHom _ σ J p).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
          rw [← matHom_mapH_kfin]
          have := mem_finPts.1 hpf
          change (matHom _ σ J (projInf σ J p)).1 = 1
          rw [this, map_one]
          rfl
        rw [e2]
        exact GlobalTheory.T.levi_matrix_one hCM hJ hW _
      exact e1
    have hmK : m ∈ K := by
      refine (memK m).2 ⟨hmf, fun v => ?_⟩
      refine GlobalTheory.T.max_even_lattice_adapted_basis hCM hJ hW v (Λ v) (hΛ1 v) (hΛ2 v) (proj σ J v p) (proj σ J v m) (hpv v) _
        (hB.map _) (flag_map_kfin (evFin F v) p B hpB) ?_
      refine (matHom_mapH_kfin (evFin F v) m).trans ?_
      rw [hm, ← GlobalTheory.T.levi_matrix_map_base_change, ← matHom_mapH_kfin]
      rfl
    refine ⟨m, ⟨d, d', hd, ?_⟩, hmK, m⁻¹ * p, ⟨B', hB', hB1, hu, fun z hz' => ?_⟩, mul_mem (inv_mem hmK) hpK, by simp⟩
    · exact hd'
    · refine hz _ ?_
      funext i
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) (cT (σ : E →+* E) X * J) z i).symm.trans ?_
      rw [hz']
      simp

end GlobalTheory.CompanionTheory.KFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompactStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_iwasawa_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ finPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  first | exact @GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good | exact GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good | (intros; apply GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good <;> assumption)
end
