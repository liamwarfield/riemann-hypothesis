module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.HeightsOfFormMix
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimClosureGenericPt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VertEq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombination
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombination
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MixZ

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a)
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem multicone_of_isUnder {U : (MP ℤ m n).Opens} {c : ∀ k, Bk n k} {y : CxPts (mpStr ℤ m n) σ₀}
    {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder y z) (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (U ⊓ mchart c)) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun k =>
  ⟨c k, ((hz k (c k)).1).1 (CxPts.ptsIn_mono (inf_le_right.trans (mchart_le c k)) hy)⟩

theorem isHermRep_congr {M : HermLB (mpStr ℤ m n)} {A B : HermLine (Bk n)} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z)
    (hM : IsHermRep M A) : IsHermRep M B := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨u, h₁, ?_, ?_⟩
  · rw [← ha]
    exact h₂
  · intro i c y z hz hy
    rw [← hh z (multicone_of_isUnder hz hy), ← ha]
    exact h₃ i c y z hz hy

theorem isHermRep_zp {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hM : IsHermRep M A) (e : ℤ) :
    ∃ B : HermLine (Bk n), IsHermRep (zp M e) B ∧ B.a = e • A.a ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = A.h z ^ e := by
  refine ⟨(powLine A e.toNat).tensor (powLine A (-e).toNat).inv,
    isHermRep_tens _ _ _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)
      (isHermRep_dual _ _ _ _ (PowRep.isHermRep_pow _ _ _ _ _ hM)), ?_, ?_⟩
  · funext k
    have e₁ : ((e.toNat : ℤ) - ((-e).toNat : ℤ)) = e := by omega
    simp only [HermLine.tensor, HermLine.inv, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, powLine_a, smul_eq_mul]
    linear_combination (A.a k) * e₁
  · intro z hz
    have hp := (A.pos z hz).ne'
    simp only [HermLine.tensor, HermLine.inv, PowRep.h_powLine]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp]
    congr 1
    omega

theorem isHermRep_foldr {κ : Type} (M : κ → HermLB (mpStr ℤ m n)) (A : κ → HermLine (Bk n))
    (hM : ∀ o, IsHermRep (M o) (A o)) (a : κ → ℤ) (l : List κ) :
    ∃ B : HermLine (Bk n), IsHermRep (l.foldr (fun i N => (zp (M i) (a i)).tens N) (HermLB.triv (mpStr ℤ m n))) B ∧
      B.a = (l.map fun o => a o • (A o).a).sum ∧
      ∀ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → B.h z = (l.map fun o => (A o).h z ^ a o).prod := by
  induction l with
  | nil =>
    exact ⟨_, isHermRep_triv m n, by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine], fun z _ => by simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]⟩
  | cons o l ih =>
    obtain ⟨B, hB, ha, hh⟩ := ih
    obtain ⟨C, hC, ca, ch⟩ := isHermRep_zp (hM o) (a o)
    refine ⟨C.tensor B, isHermRep_tens _ _ _ _ _ _ hC hB, ?_, fun z hz => ?_⟩
    · simp only [HermLine.tensor, List.map_cons, List.sum_cons, ca, ha]
    · simp only [HermLine.tensor, List.map_cons, List.prod_cons, ch z hz, hh z hz]

theorem readComb : ReadComb := by
  intro m n κ _ M A hM a
  obtain ⟨B, hB, ha, hh⟩ := isHermRep_foldr M A hM a (Finset.univ : Finset κ).toList
  refine isHermRep_congr ?_ (fun z hz => ?_) hB
  · rw [ha, Finset.sum_map_toList]
    rfl
  · rw [hh z hz, Finset.prod_map_toList]
    exact (if_pos hz).symm

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadCombinationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_read_combination : GlobalTheory.CompanionTheory.MixZ.ReadComb := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.readComb | exact GlobalTheory.CompanionTheory.MixZ.readComb | (intros; apply GlobalTheory.CompanionTheory.MixZ.readComb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentity
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.ArInt

namespace GlobalTheory.CompanionTheory.MixZ.PolarProof

theorem multilinear_eq_zero {V : Type} [AddCommGroup V] {N : ℕ}
    (M : (Fin N → V) →ₘₗ[ℤ] ℝ)
    (hs : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), M (a ∘ σ) = M a)
    (hd : ∀ x : V, M (fun _ => x) = 0) (a : Fin N → V) : M a = 0 := by
  classical
  have hsurj : ∀ f : Fin N → Fin N, Function.Surjective f → M (a ∘ f) = M a := fun f hf =>
    hs a (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩)
  have expand : ∀ T : Finset (Fin N), M (fun _ => ∑ i, if i ∈ T then 0 else a i) =
      ∑ f : Fin N → Fin N, if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0 := by
    intro T
    set_option synthInstance.maxHeartbeats 100000 in
      rw [M.map_sum (fun _ i => if i ∈ T then 0 else a i)]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with h
    · congr 1
      funext j
      have : f j ∉ T := fun hj => Finset.mem_compl.1 (h hj) (Finset.mem_image_of_mem f (Finset.mem_univ j))
      simp [this]
    · obtain ⟨t, ht, hc⟩ := Finset.not_subset.1 h
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.notMem_compl.1 hc)
      exact M.map_coord_zero j (if_pos ht)
  have hinner : ∀ f : Fin N → Fin N, ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
      (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
      if Function.Surjective f then M a else 0 := by
    intro f
    have h1 : ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
        (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
        (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) * M (a ∘ f) := by
      rw [Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ)]
      have h2 : Finset.univ.filter (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ) =
          ((Finset.univ.image f)ᶜ).powerset := by
        ext T; simp
      rw [h2, Finset.sum_eq_zero (s := Finset.univ.filter _) (fun T hT => by
        rw [if_neg (Finset.mem_filter.1 hT).2, mul_zero]), add_zero]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [if_pos (Finset.mem_powerset.1 hT)]
    have h3 : (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) =
        if (Finset.univ.image f)ᶜ = ∅ then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → ℝ)
        (Finset.sum_powerset_neg_one_pow_card (x := (Finset.univ.image f)ᶜ))
      push_cast at this
      exact this
    have h4 : (Finset.univ.image f)ᶜ = ∅ ↔ Function.Surjective f := by
      rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
      simp [Function.Surjective]
    rw [h1, h3]
    by_cases h : Function.Surjective f
    · rw [if_pos (h4.2 h), if_pos h, one_mul, hsurj f h]
    · rw [if_neg (fun e => h (h4.1 e)), if_neg h, zero_mul]
  have htot : ∑ f : Fin N → Fin N, (if Function.Surjective f then M a else 0) = 0 := by
    simp only [← hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun T _ => ?_
    rw [← Finset.mul_sum, ← expand, hd, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at htot
  rcases mul_eq_zero.1 htot with h | h
  · have hc : (Finset.univ.filter fun f : Fin N → Fin N => Function.Surjective f).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨id, by simp [Function.surjective_id]⟩
    exact absurd (by exact_mod_cast h) hc
  · exact h

theorem eq_of_diag {V : Type} [AddCommGroup V] {N : ℕ} (S T : (Fin N → V) → ℝ)
    (hS : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), S (a ∘ σ) = S a)
    (hT : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), T (a ∘ σ) = T a)
    (aS : ∀ (a : Fin N → V) (j : Fin N) (b c : V), S (Function.update a j (b + c)) =
      S (Function.update a j b) + S (Function.update a j c))
    (aT : ∀ (a : Fin N → V) (j : Fin N) (b c : V), T (Function.update a j (b + c)) =
      T (Function.update a j b) + T (Function.update a j c))
    (hd : ∀ x : V, S (fun _ => x) = T (fun _ => x)) (a : Fin N → V) : S a = T a := by
  have aG : ∀ (a : Fin N → V) (j : Fin N) (b c : V),
      (S - T) (Function.update a j (b + c)) =
        (S - T) (Function.update a j b) + (S - T) (Function.update a j c) := by
    intro a j b c
    simp only [Pi.sub_apply, aS, aT]
    ring
  let M : (Fin N → V) →ₘₗ[ℤ] ℝ :=
    { toFun := S - T
      map_update_add' := by
        intro inst m j b c
        rw [Subsingleton.elim inst (fun a b => instDecidableEqFin N a b)]
        exact aG m j b c
      map_update_smul' := by
        intro inst m j c x
        obtain rfl : inst = (fun a b => instDecidableEqFin N a b) := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun y => (S - T) (Function.update m j y)) (aG m j)) c x }
  have h := multilinear_eq_zero M
    (fun a σ => by
      change (S - T) (a ∘ σ) = (S - T) a
      simp only [Pi.sub_apply, hS, hT])
    (fun x => by
      change (S - T) (fun _ => x) = 0
      simp only [Pi.sub_apply, hd, sub_self]) a
  have h' : (S - T) a = 0 := h
  exact sub_eq_zero.1 h'

section Line

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : HermLine ι} (h₁ : A.a = B.a) (h₂ : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem combLine_add {κ : Type} [Fintype κ] (A : κ → HermLine ι) (a b : κ → ℤ) :
    combLine A (a + b) = (combLine A a).tensor (combLine A b) := by
  refine hermLine_ext ?_ ?_
  · simp only [combLine, HermLine.tensor, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · funext z
    simp only [combLine, HermLine.tensor]
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · rw [if_pos hz, if_pos hz, if_pos hz, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun o _ => zpow_add₀ ((A o).pos z hz).ne' _ _
    · rw [if_neg hz, if_neg hz, if_neg hz, mul_zero]

theorem combLine_elim_zero {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι) (n : κ → ℤ) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 0 n) = combLine A n := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    simp [combLine, Fintype.prod_option]

theorem combLine_elim_one {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι)
    (c₀ : ∀ z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A₀.h z = 0) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 1 fun _ => 0) = A₀ := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · simp only [combLine]
      rw [if_pos hz]
      simp [Fintype.prod_option]
    · simp only [combLine]
      rw [if_neg hz, c₀ z hz]

end Line

section Lin

variable {κ : Type} [Fintype κ]

theorem lin_add (a b : κ → ℤ) : lin (fun o => ((a + b) o : ℝ)) = lin (fun o => (a o : ℝ)) + lin (fun o => (b o : ℝ)) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem lin_elim_zero (n : κ → ℤ) :
    lin (fun o : Option κ => (((o.elim 0 n : ℤ)) : ℝ)) = rename some (lin fun i => (n i : ℝ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, Fintype.sum_option, map_sum, rename_X]

theorem lin_elim_one :
    lin (fun o : Option κ => (((o.elim 1 fun _ => 0 : ℤ)) : ℝ)) = MvPolynomial.X none := by
  simp [lin, Fintype.sum_option]

end Lin

theorem polar : Polar := by
  classical
  intro K _ ι _ F D κ _ A₀ A s₀ sA c₀ cA hsym hadd Φ hΦ n
  let A' : Option κ → HermLine ι := fun o => o.elim A₀ A
  have sA' : ∀ o, IsSmoothHerm (A' o) := by
    rintro (_ | j)
    exacts [s₀, sA j]
  have sC : ∀ a, IsSmoothHerm (combLine A' a) := isSmoothHerm_combLine sA'
  let l : (Option κ → ℤ) → MvPolynomial (Option κ) ℝ := fun a => lin fun o => (a o : ℝ)
  let S : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => Φ (∏ j, l (a j))
  let T : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => F (D + 1) fun j => combLine A' (a j)
  have hST : ∀ a, S a = T a := by
    refine eq_of_diag S T ?_ ?_ ?_ ?_ ?_
    · intro a σ
      change Φ (∏ j, l (a (σ j))) = Φ (∏ j, l (a j))
      rw [Equiv.prod_comp σ fun j => l (a j)]
    · intro a σ
      exact hsym (fun j => combLine A' (a j)) σ fun j => sC _
    · intro a j b c
      change Φ (∏ i, l (Function.update a j (b + c) i)) =
        Φ (∏ i, l (Function.update a j b i)) + Φ (∏ i, l (Function.update a j c i))
      have e : ∀ x : Option κ → ℤ, ∏ i, l (Function.update a j x i) =
          l x * ∏ i ∈ Finset.univ \ {j}, l (a i) := by
        intro x
        have := Finset.prod_update_of_mem (Finset.mem_univ j) (fun i => l (a i)) (l x)
        rw [← this]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, ← map_add (f := _), ← add_mul]
      congr 2
      exact lin_add b c
    · intro a j b c
      have e : ∀ x : Option κ → ℤ, T (Function.update a j x) =
          F (D + 1) (Function.update (fun i => combLine A' (a i)) j (combLine A' x)) := by
        intro x
        change F (D + 1) (fun i => combLine A' (Function.update a j x i)) = _
        congr 1
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, combLine_add]
      exact hadd _ j _ _ (fun _ => sC _) (sC _) (sC _)
    · intro x
      change Φ (∏ _j : Fin (D + 1), l x) = F (D + 1) fun _ => combLine A' x
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact hΦ x
  have key := hST (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0)
  have eS : S (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) := by
    change Φ _ = _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h₁ := lin_elim_zero n
    have h₂ := lin_elim_one (κ := κ)
    simp only [l]
    rw [h₁, h₂, mul_comm]
  have eT : T (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      F (D + 1) (Fin.snoc (fun _ : Fin D => combLine A n) A₀) := by
    change F (D + 1) _ = _
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact combLine_elim_one A₀ A c₀
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact combLine_elim_zero A₀ A n
  rw [← eS, key, eT]

end GlobalTheory.CompanionTheory.MixZ.PolarProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPolarizationIdentityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_polarization_identity : GlobalTheory.CompanionTheory.MixZ.Polar := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PolarProof.polar | exact GlobalTheory.CompanionTheory.MixZ.PolarProof.polar | (intros; apply GlobalTheory.CompanionTheory.MixZ.PolarProof.polar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermOfCntEq
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Polarisation

noncomputable def cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (f j) 1

open Classical in
theorem cnt_apply {ι : Type} {m : ℕ} (f : Fin m → ι) (i : ι) :
    cnt f i = Fintype.card {j // f j = i} := by
  simp [cnt, Finsupp.finsetSum_apply, Finsupp.single_apply, Fintype.card_subtype]

theorem degree_cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : (cnt f).degree = m := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cnt, map_sum]

theorem exists_perm_of_cnt_eq {ι : Type} {m : ℕ} {f g : Fin m → ι} (h : cnt f = cnt g) :
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  classical
  have hc : ∀ i, Nonempty ({j // g j = i} ≃ {j // f j = i}) := fun i => by
    refine Fintype.card_eq.1 ?_
    rw [← cnt_apply, ← cnt_apply, h]
  let e : ∀ i, {j // g j = i} ≃ {j // f j = i} := fun i => (hc i).some
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext j
  exact (Equiv.ofFiberEquiv_map e j).symm

theorem prod_X_eq {ι : Type} {m : ℕ} (f : Fin m → ι) (a : Fin m → ℝ) :
    ∏ j, (C (a j) * X (f j) : MvPolynomial ι ℝ) = monomial (cnt f) (∏ j, a j) := by
  classical
  have key : ∀ s : Finset (Fin m), ∏ j ∈ s, (C (a j) * X (f j) : MvPolynomial ι ℝ)
      = monomial (∑ j ∈ s, Finsupp.single (f j) 1) (∏ j ∈ s, a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx, ih, X,
        C_mul_monomial, monomial_mul]
      simp
  exact key Finset.univ

theorem lin_pow {ι : Type} [Fintype ι] (n : ι → ℝ) (m : ℕ) :
    GlobalTheory.ArInt.lin n ^ m = ∑ f : Fin m → ι, monomial (cnt f) (∏ j, n (f j)) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset ι))
    (fun _ i => (C (n i) * X i : MvPolynomial ι ℝ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at h
  rw [GlobalTheory.ArInt.lin, h]
  exact Finset.sum_congr rfl fun f _ => prod_X_eq f (fun j => n (f j))


open Classical in
noncomputable def coef {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) : ℝ :=
  if h : ∃ f : Fin m → ι, cnt f = k then F h.choose else 0

theorem coef_cnt {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ)
    (hF : ∀ (f : Fin m → ι) (σ : Equiv.Perm (Fin m)), F (f ∘ σ) = F f) (f : Fin m → ι) :
    coef F (cnt f) = F f := by
  have h : ∃ g : Fin m → ι, cnt g = cnt f := ⟨f, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_cnt_eq h.choose_spec.symm
  rw [coef, dite_eq_left h, hσ, hF]

theorem coef_of_degree_ne {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) {k : ι →₀ ℕ}
    (hk : k.degree ≠ m) : coef F k = 0 := by
  refine dif_neg ?_
  rintro ⟨f, rfl⟩
  exact hk (degree_cnt f)

noncomputable def form {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials ι ℝ).constr ℝ (coef F)

theorem form_monomial {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) (a : ℝ) :
    form F (monomial k a) = a * coef F k := by
  have h1 : (monomial k a : MvPolynomial ι ℝ) = a • basisMonomials ι ℝ k := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h1, map_smul, form, Module.Basis.constr_basis, smul_eq_mul]

theorem exists_form (ι : Type) [Fintype ι] (D : ℕ) (F : (Fin (D + 1) → ι) → ℝ)
    (hF : ∀ (f : Fin (D + 1) → ι) (σ : Equiv.Perm (Fin (D + 1))), F (f ∘ σ) = F f) :
    ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ,
      (∀ n : ι → ℝ, Φ (GlobalTheory.ArInt.lin n ^ (D + 1)) = ∑ f : Fin (D + 1) → ι, (∏ j, n (f j)) * F f) ∧
      ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0 := by
  refine ⟨form F, fun n => ?_, fun P d hd hP => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [lin_pow, map_sum]
      exact Finset.sum_congr rfl fun f _ => by rw [form_monomial, coef_cnt F hF]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [P.as_sum, map_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hdeg : k.degree = d := by
        have := hP (mem_support_iff.1 hk)
        rw [Finsupp.degree_eq_weight_one]; exact this
      rw [form_monomial, coef_of_degree_ne F (by rw [hdeg]; exact hd), mul_zero]

end GlobalTheory.CompanionTheory.Polarisation
end

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.CycleHeightFormulas.CombLineSingle
section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.CycleHeightFormulas.TopSelfTower
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArithmeticHeightTower.TowerCopy

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.VdmRec GlobalTheory.ProjVar

theorem topSelf_eq_finrank_mul {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (M : LB X) (d : ℕ) : topSelfIntersection k M d = (Module.finrank k K : ℤ) * topSelfIntersection K M d := by
  have hχ (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
    have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
      refine ⟨fun a b x => ?_⟩
      change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
        cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
      rw [Algebra.smul_def, map_mul, map_mul, hk]
      rfl
    have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
      rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
      push_cast
      ring
    rw [chi_def, chi_def]
    simp_rw [e]
    exact (mul_finsum _ _).symm
  rw [topSelf_def, topSelf_def, interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hχ]
  ring

end GlobalTheory.ArithmeticHeightTower.TowerCopy
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine isSmoothHerm_powLine isSmoothHerm_constLine)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ

namespace GlobalTheory.ArithmeticHeightTower.FormZc

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def dimOf (x : MP ℤ m n) : ℕ := by
  classical
  exact if h : ∃ d : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d then h.choose else 0

theorem dimOf_eq {x : MP ℤ m n} {d : ℕ} (h : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d) :
    dimOf x = d := by
  have hx : ∃ d : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d := ⟨d, h⟩
  have e := hx.choose_spec.symm.trans h
  have e' : hx.choose = d := by exact_mod_cast e
  rw [dimOf, dite_eq_left hx, e']

def htFn (II : IntersectionSystem) (A : HermLine (Bk n)) (x : MP ℤ m n) : ℝ :=
  cycVal II A (dimOf x) (ptIdeal x)

theorem htFn_eq (II : IntersectionSystem) (A : HermLine (Bk n)) {x : MP ℤ m n} {d : ℕ}
    (h : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = d) :
    htFn II A x = cycVal II A d (ptIdeal x) := by
  rw [htFn, dimOf_eq h]

theorem last_powLine (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) {W : Ideal (Pol n)} {e : ℕ}
    (hW : Geo.IsArithVar W (e + 1)) {A : HermLine (Bk n)} (hA : IsSmoothHerm A) (r : ℕ) :
    II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) (powLine A r)) =
      r * II (Fin (m + 1)) (Bk n) W (e + 1) (fun _ => A) := by
  have hadd : ∀ B C : HermLine (Bk n), IsSmoothHerm B → IsSmoothHerm C →
      II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) (B.tensor C)) =
      II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) B) +
        II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) C) := by
    intro B C hB hC
    have h := hII.2.1 _ _ W (e + 1) (fun _ => A) (Fin.last e) B C hW (fun _ => hA) hB hC
    have e₁ : ∀ E : HermLine (Bk n), Function.update (fun _ : Fin (e + 1) => A) (Fin.last e) E =
        Fin.snoc (fun _ : Fin e => A) E := by
      intro E
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Function.update_of_ne (Fin.castSucc_lt_last j).ne]
    simpa only [e₁] using h
  have hs : (Fin.snoc (fun _ : Fin e => A) A : Fin (e + 1) → HermLine (Bk n)) = fun _ => A := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  have s₁ : IsSmoothHerm (constLine (ι := Bk n) 1 one_pos) := isSmoothHerm_constLine 1 one_pos
  have h0 : II (Fin (m + 1)) (Bk n) W (e + 1) (Fin.snoc (fun _ : Fin e => A) (constLine 1 one_pos)) = 0 := by
    have h := hadd _ _ s₁ s₁
    have e₁ : (constLine (ι := Bk n) 1 one_pos).tensor (constLine 1 one_pos) = constLine 1 one_pos :=
      PolarProof.hermLine_ext (by simp [HermLine.tensor, constLine]) (by
        funext z
        simp [HermLine.tensor, constLine])
    rw [e₁] at h
    linarith
  induction r with
  | zero => simpa [powLine] using h0
  | succ r ih =>
    rw [powLine, hadd _ _ (isSmoothHerm_powLine hA r) hA, ih, hs]
    push_cast
    ring

theorem vertical_eq (h₃ : PtDict) (hV : VertEq) (II : IntersectionSystem) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (d : ℕ) (hd : topologicalKrullDim Z = d) :
    cycVal II A d (ptIdeal (i (genericPoint Z))) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  obtain ⟨-, hp₃, -, hp₅⟩ := h₃ m n Z i d hd
  have hnh : ¬ IsHorizontal (ptIdeal (i (genericPoint Z))) := by
    intro hh
    haveI hc : CharZero Γ(Z, ⊤) := hp₃.1 hh
    obtain ⟨p, hp⟩ := CharP.exists κ
    haveI := hp
    have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite κ p
    have h0 : (p : Γ(Z, ⊤)) = 0 := by
      rw [← map_natCast (algebraMap κ Γ(Z, ⊤)) p, CharP.cast_eq_zero, map_zero]
    exact hp0 (Nat.cast_eq_zero.1 h0)
  obtain ⟨hpr, hz⟩ := hp₅ hnh
  rw [cycVal, if_neg hnh]
  generalize charOf (ptIdeal (i (genericPoint Z))) = l at hpr hz ⊢
  haveI : Fact l.Prime := ⟨hpr⟩
  haveI : CharP Γ(Z, ⊤) l := charP_of_cast hpr hz
  haveI : CharP κ l := (RingHom.charP_iff (algebraMap κ Γ(Z, ⊤)) (algebraMap κ Γ(Z, ⊤)).injective l).2 inferInstance
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ZMod.algebra _ l
  have e₀ := GlobalTheory.ArithmeticHeightTower.TowerCopy.topSelf_eq_finrank_mul (X := Z) (ZMod l) κ
    (fun a => RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod l) Γ(Z, ⊤))
      ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ))) a) (N.B.pull i) d
  have e₁ := hV m n N A hN (MP ℤ m n) (𝟙 _) Z i l d hd
  have pullIso : LBIso (N.B.pull i) ((N.B.pull (𝟙 _)).pull i) := by
    refine LBIso.chartPull (chartPullPull N.B i) (chartPullPull (N.B.pull (𝟙 _)) i) ?_
    exact iso_of_chart (LB.isLB_pull N.isLB _) (chartPullUnpull N.B _ rfl)
  have e₂ : topSelfIntersection (ZMod l) (N.B.pull i) d = topSelfIntersection (ZMod l) ((N.B.pull (𝟙 _)).pull i) d :=
    topSelf_congr (ZMod l) (N.restr i).isLB ((N.pull (𝟙 _) (Category.id_comp _)).restr i).isLB pullIso d
  have e₃ : (𝟙 (MP ℤ m n) : _ ⟶ _) (i (genericPoint Z)) = i (genericPoint Z) := by simp
  rw [e₃] at e₁
  haveI : Fintype κ := Fintype.ofFinite κ
  have e₄ : Nat.card κ = l ^ Module.finrank (ZMod l) κ := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l) (V := κ), ZMod.card]
  rw [← e₁, ← e₂, e₀, e₄]
  push_cast
  rw [Real.log_pow]
  ring

theorem rec_pow (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (h₈ : ArchIntegrableOn) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (e : ℕ) (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1)) (mm : ℕ)
    (r : ((N.restr i).pow mm).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((N.restr i).pow mm).B r) :
    (N.restr i).ArchIntegrable ((N.restr i).pow mm) e hr ∧
    mm * cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, ((((N.restr i).pow mm).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.restr i).archInt ((N.restr i).pow mm) e hr := by
  have hRep := GlobalTheory.CompanionTheory.MPDict.PowRep.isHermRep_pow m n N A mm hN
  have sB := isSmoothHerm_powLine hA mm
  have iso : ((N.restr i).pow mm).Isometric ((N.pow mm).restr i) :=
    HermLB.icls_eq_iff.1 (by simp [HermLB.icls_pow, HermLB.icls_pull, map_nsmul])
  obtain ⟨r', hr', e₁, e₂⟩ := iso.exists_isRatSec hr
  have hI := h₈ m n N (N.pow mm) Z i e hZ r' hr'
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n (N.pow mm) (powLine A mm) hRep Z i r' hr'
  have hcyc := h₆ m n (N.pow mm) (powLine A mm) hRep Z i e hZ r' hr' f g hfg hrat (cycVal II A e)
  have hint := h₇ m n N (N.pow mm) A (powLine A mm) hN hRep Z i e hZ hA sB r' hr' f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ e (fun _ => A) (powLine A mm) f g hP (fun _ => hA) sB hfg
  have hpw := last_powLine II hII hP hA mm
  refine ⟨?_, ?_⟩
  · unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at hI ⊢
    rw [e₁] at hI
    exact fun σ => Weight.ChernIntegrableOn.congr (hI σ) (isOpen_offSupp _).measurableSet (e₂ σ)
  · have e₃ : (N.restr i).archInt ((N.restr i).pow mm) e hr = (N.restr i).archInt ((N.pow mm).restr i) e hr' := by
      simp only [HermLB.archInt, e₁]
      exact finsum_congr fun σ => (Weight.chernInt_congr (isOpen_offSupp _).measurableSet (e₂ σ)).symm
    have e₄ : ((N.restr i).pow mm).div hr = ((N.pow mm).restr i).div hr' := e₁.symm
    rw [cycVal, if_pos hP.2.2.1, ← hpw, hrr, e₃, hint, e₄, hcyc]
    rfl

theorem exists_height (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq)
    (h₈ : ArchIntegrableOn) (hV : VertEq) (hPt : PtLen) (hC : CurveInt) (hR : RatRStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (hN : IsHermRep N A)
    (hA : IsSmoothHerm A) : N.IsArithHeight (htFn II A) := by
  refine { vertical := ?_, point := ?_, recursion := ?_ }
  · intro Z i _ _ κ _ _ _ d hd
    rw [htFn_eq II A ((dim_of_generic i).trans hd)]
    exact vertical_eq h₃ hV II N A hN Z i κ d hd
  · intro Z i _ _ _ hc hd r hr
    have hd' : topologicalKrullDim Z = ((0 + 1 : ℕ) : _) := by simpa using hd
    have hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) 0 := (mp_var m n).of_isClosedImmersion i hc hd'
    obtain ⟨-, hp₃, hp₄, -⟩ := h₃ m n Z i 1 hd'
    rw [htFn_eq II A ((dim_of_generic i).trans hd'),
      curve_eq h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z i hZ (hp₄ (hp₃.2 hc)) r hr]
    rfl
  · intro Z i _ _ _ hc e he hd mm r hr
    have hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e := (mp_var m n).of_isClosedImmersion i hc hd
    obtain ⟨-, hp₃, hp₄, -⟩ := h₃ m n Z i (e + 1) hd
    obtain ⟨h₁, h₂⟩ := rec_pow h₅ h₆ h₇ h₈ hR II hII N A hN hA Z i e hZ (hp₄ (hp₃.2 hc)) mm r hr
    refine ⟨h₁, ?_⟩
    rw [htFn_eq II A ((dim_of_generic i).trans hd), h₂]
    refine congrArg (· - _) (finsum_congr fun z => ?_)
    by_cases hz : (((N.restr i).pow mm).div hr).mult z = 0
    · simp [hz]
    · rw [htFn_eq II A ((dim_closure_image i z).trans
        (h₄ Z _ e hZ z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)))]

section Expand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type} [Fintype κ]

theorem combLine_single [DecidableEq κ] (A : κ → HermLine ι)
    (cA : ∀ j z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (A j).h z = 0) (o : κ) : combLine A (Pi.single o 1) = A o := by
  refine PolarProof.hermLine_ext ?_ ?_
  · simp [combLine, Pi.single_apply, ite_smul]
  · funext z
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · simp only [combLine]
      rw [if_pos hz, Finset.prod_eq_single o]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
    · simp only [combLine]
      rw [if_neg hz, cA o z hz]

theorem expand_comb (A : κ → HermLine ι) (sA : ∀ o, IsSmoothHerm (A o))
    (cA : ∀ j z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (A j).h z = 0) (e : ℕ) (F : (Fin e → HermLine ι) → ℝ)
    (hF : ∀ (L : Fin e → HermLine ι) (j : Fin e) (B C : HermLine ι), (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
      IsSmoothHerm C → F (Function.update L j (B.tensor C)) = F (Function.update L j B) + F (Function.update L j C))
    (a : κ → ℤ) :
    F (fun _ => combLine A a) = ∑ f : Fin e → κ, (∏ j, (a (f j) : ℝ)) * F (A ∘ f) := by
  classical
  have sC : ∀ b, IsSmoothHerm (combLine A b) := isSmoothHerm_combLine sA
  have up : ∀ (x : Fin e → κ → ℤ) (j : Fin e) (b : κ → ℤ),
      (fun i => combLine A (Function.update x j b i)) = Function.update (fun i => combLine A (x i)) j (combLine A b) := by
    intro x j b
    funext i
    by_cases h : i = j
    · subst h
      simp
    · simp [Function.update_of_ne h]
  have aG : ∀ (x : Fin e → κ → ℤ) (j : Fin e) (b c : κ → ℤ),
      F (fun i => combLine A (Function.update x j (b + c) i)) =
        F (fun i => combLine A (Function.update x j b i)) + F (fun i => combLine A (Function.update x j c i)) := by
    intro x j b c
    simp only [up, PolarProof.combLine_add]
    exact hF _ j _ _ (fun _ => sC _) (sC _) (sC _)
  let M : (Π _ : Fin e, κ → ℤ) →ₘₗ[ℤ] ℝ :=
    { toFun := fun x => F fun i => combLine A (x i)
      map_update_add' := by
        intro inst x j b c
        rw [Subsingleton.elim inst (fun a b => instDecidableEqFin e a b)]
        exact aG x j b c
      map_update_smul' := by
        intro inst x j c b
        obtain rfl : inst = (fun a b => instDecidableEqFin e a b) := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun y => F fun i => combLine A (Function.update x j y i)) (aG x j)) c b }
  have ha : a = ∑ o, a o • (Pi.single o 1 : κ → ℤ) := by
    funext o
    simp [Finset.sum_apply, Pi.single_apply]
  have h₁ : M (fun _ => a) = F (fun _ => combLine A a) := rfl
  rw [← h₁]
  have h₂ : M (fun _ => a) = M (fun _ => ∑ o, a o • (Pi.single o 1 : κ → ℤ)) := by rw [← ha]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h₂, M.map_sum (fun _ o => a o • (Pi.single o 1 : κ → ℤ))]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [M.map_smul_univ (fun j => a (f j)) (fun j => (Pi.single (f j) 1 : κ → ℤ))]
  simp only [RingHom.id_apply]
  have h₃ : M (fun j => (Pi.single (f j) 1 : κ → ℤ)) = F (A ∘ f) := by
    change F (fun i => combLine A (Pi.single (f i) 1)) = F (A ∘ f)
    congr 1
    funext i
    exact combLine_single A cA (f i)
  rw [h₃, zsmul_eq_mul]
  push_cast
  rfl

end Expand

end GlobalTheory.ArithmeticHeightTower.FormZc
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine isSmoothHerm_powLine isSmoothHerm_constLine)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ

namespace GlobalTheory.ArithmeticHeightTower.FormZc


open ReciprocityTheory.ChartRestriction.G.Geo.ResK (ResKStatement) in
theorem formZ_direct :
    Geo.ArithIntersectionSystemStatement → ResKStatement → GlobalTheory.ArithmeticHeightTower.FormZ := by
  rintro ⟨II, hII⟩ hK m n X _ i _ D hX ι _ M tM
  have h₈ := GlobalTheory.T.archimedean_integrable_on hK
  have h₇ := GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable h₈
  have hR := GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK hK
  have h₃ := GlobalTheory.CompanionTheory.MixZ.ptDict
  choose A sA RA cA using fun j => GlobalTheory.CompanionTheory.MixZ.existsRead m n (M j) (tM j)
  have hc := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := h₃ m n X i (D + 1) hX.dim_eq
  have hhor : IsHorizontal (ptIdeal (i (genericPoint X))) := hp₃.2 hc
  have hP := hp₄ hhor
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.CompanionTheory.Polarisation.exists_form ι D
    (fun f => II (Fin (m + 1)) (Bk n) (ptIdeal (i (genericPoint X))) (D + 1) (A ∘ f))
    (fun f s => (hII.1 _ _).1 _ _ (A ∘ f) s hP fun _ => sA _)
  refine ⟨Φ, fun a => ?_, h0⟩
  have Rc := GlobalTheory.CompanionTheory.MixZ.readComb m n ι M A RA a
  have sC := isSmoothHerm_combLine sA a
  have H := exists_height h₃ codimOne_holds GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational h₇ h₈ GlobalTheory.CompanionTheory.MixZ.Vert.vertEq GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen curveInt hR II hII
    (comb M a) (combLine A a) Rc sC
  refine ⟨_, (isometric_comb_pull M a i rfl).symm.isArithHeight hX (H.restrict (mp_var m n) i rfl), ?_⟩
  rw [htFn_eq II _ ((dim_of_generic i).trans hX.dim_eq), cycVal, if_pos hhor, hΦ]
  refine (expand_comb A sA cA (D + 1) (II (Fin (m + 1)) (Bk n) (ptIdeal (i (genericPoint X))) (D + 1))
    (fun L j B C hL hB hC => hII.2.1 _ _ _ _ L j B C hP hL hB hC) a)

end GlobalTheory.ArithmeticHeightTower.FormZc

namespace GlobalTheory.CompanionTheory.MixZ

theorem mixZ_direct :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.ArithmeticHeightTower.MixZ := by
  rintro ⟨II, hII⟩ hK
  have hR := GlobalTheory.T.rationality_of_resolution_statement hK
  have hI := GlobalTheory.T.archimedean_integrable_on hK
  have hE := GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable hI
  exact mixZ_of GlobalTheory.T.mixed_cycle_read_exists GlobalTheory.T.mixed_cycle_read_combination GlobalTheory.T.mixed_cycle_point_dictionary GlobalTheory.T.mixed_cycle_codimension_one GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational hE hI GlobalTheory.T.mixed_polarization_identity hR II hII
    (GlobalTheory.T.height_eq_of_full_intersection_system GlobalTheory.T.mixed_cycle_point_dictionary GlobalTheory.T.mixed_cycle_codimension_one GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational hE GlobalTheory.CompanionTheory.MixZ.Vert.vertEq GlobalTheory.T.mixed_point_length_formula GlobalTheory.T.mixed_curve_intersection_formula hR II hII)

end GlobalTheory.CompanionTheory.MixZ

namespace GlobalTheory.CompanionTheory.MPDict
open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem height_eq_direct : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (II : Geo.IntersectionSystem), Geo.IsFullIntersectionSystem II → ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → ∀ h : MP ℤ m n → ℝ, M.IsArithHeight h → ∀ (x : MP ℤ m n) (d : ℕ), Geo.IsArithVar (ptIdeal x) d → h x = II (Fin (m + 1)) (Bk n) (ptIdeal x) d (fun _ => A) := by
  intro hK II hII m n M A hA h H x d hd
  have hI := GlobalTheory.T.archimedean_integrable_on hK
  have hE := GlobalTheory.CompanionTheory.MixZ.archIntEq_of_integrable hI
  have hH : GlobalTheory.CompanionTheory.MixZ.HeightEq II := GlobalTheory.T.height_eq_of_full_intersection_system GlobalTheory.T.mixed_cycle_point_dictionary GlobalTheory.T.mixed_cycle_codimension_one GlobalTheory.T.mixed_cycle_rational_exists GlobalTheory.T.mixed_cycle_of_rational hE GlobalTheory.CompanionTheory.MixZ.Vert.vertEq
    GlobalTheory.T.mixed_point_length_formula GlobalTheory.T.mixed_curve_intersection_formula (GlobalTheory.T.rationality_of_resolution_statement hK) II hII
  have hX := isArithVar_mpStr m n
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  haveI : IsNoetherian Z := hX.isNoetherian_sub i
  have e := hH m n M A hA (GlobalTheory.T.hermitian_line_bundle_smooth m n M A hA) Z i _ (H.restrict hX i rfl) (genericPoint Z) d
    ((GlobalTheory.CompanionTheory.MixZ.dim_closure_generic Z).trans (dim_of_isArithVar GlobalTheory.T.mixed_cycle_point_dictionary i hd))
  refine e.trans ?_
  rw [GlobalTheory.CompanionTheory.MixZ.cycVal]
  exact if_pos hd.2.2.1

theorem projQ_direct (hAIS : Geo.ArithIntersectionSystemStatement)
    (hK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) : ProjQ := by
  obtain ⟨II, hII⟩ := hAIS
  intro n' m n Y _ j' _ e hvar hdim hdeg M hM h h' hh hh'
  let j : Y ⟶ MP ℤ (m + 1) (consN n' n) := j'
  haveI : IsClosedImmersion j := ‹IsClosedImmersion j'›
  obtain ⟨A, hA⟩ := GlobalTheory.CompanionTheory.MPDict.HermRep.exists_isHermRep m n M hM
  have hA' := GlobalTheory.CompanionTheory.MPDict.isHermRep_pull n' m n M A hA
  have hS := GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep m n M A hA
  haveI hc : CharZero ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) := charZero_genericPt hvar
  haveI hc' : CharZero ((MP ℤ m n).residueField (qpSnd n' m n (j (genericPoint Y)))) := charZero_image _ _ _ _
  have hP' : Geo.IsArithVar (ptIdeal (j (genericPoint Y))) (e + 1) :=
    GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal (m + 1) (consN n' n) _ _ hc (dim_closure_genericPt hvar)
  have hP : Geo.IsArithVar (ptIdeal (qpSnd n' m n (j (genericPoint Y)))) (e + 1) := GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal m n _ _ hc' hdim
  have e₁ := height_eq_direct hK II hII (m + 1) (consN n' n) _ _ hA' h' hh' _ _ hP'
  have e₂ := height_eq_direct hK II hII m n M A hA h hh _ _ hP
  have hi := GlobalTheory.CompanionTheory.MPDict.ProjImage.imageZ_ptIdeal n' m n (j (genericPoint Y))
  have pf := hII.2.2.1 (Fin (m + 1)) (Bk n) (Fin (m + 2)) (Bk (consN n' n)) Fin.succ (sv n' n)
    ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) (ptCoord (j (genericPoint Y))) (e + 1)
    (fun _ => A) (fun _ => pullLine n' A) (isBlockMap_sv n' n) hP' (by
      change Geo.IsArithVar (imageZ (sv n' n) (ptIdeal (j (genericPoint Y)))) (e + 1)
      rw [hi]; exact hP) (fun _ => hS)
    (fun _ => isPullHerm_pullLine n' A)
  have hd := GlobalTheory.CompanionTheory.MPDict.FnDeg.relfinrank_blockFnField_sv n' m n (j (genericPoint Y))
  have hd' : (IntermediateField.relfinrank (blockFnField (ptCoord (j (genericPoint Y)) ∘ sv n' n)) (blockFnField (ptCoord (j (genericPoint Y)))) : ℝ) = ((qpSnd n' m n).residueDegree (j (genericPoint Y)) : ℝ) := by
    exact_mod_cast hd
  rw [hd'] at pf
  change II _ _ (ptIdeal (j (genericPoint Y))) _ _ = _ * II _ _ (imageZ (sv n' n) (ptIdeal (j (genericPoint Y)))) _ _ at pf
  rw [hi] at pf
  refine e₁.trans (pf.trans ?_)
  exact congrArg (fun t => (((qpSnd n' m n).residueDegree (j (genericPoint Y)) : ℕ) : ℝ) * t) e₂.symm

end GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights

theorem arCalc_direct (hP : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong) (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) : GlobalTheory.Published.ArCalc :=
  have H := GlobalTheory.T.arith_intersection_system_of_poincare_lelong hP hR
  have P := GlobalTheory.ArithmeticHeightTower.Read1.bridge3 (GlobalTheory.ArithmeticHeightTower.FormZc.formZ_direct H hR) (GlobalTheory.CompanionTheory.MixZ.mixZ_direct H hR)
    (GlobalTheory.CompanionTheory.MPDict.projQ_direct H hR)
  GlobalTheory.T.arithIntersectionCalculus_of_form_mixed_projection P.1 P.2.1 P.2.2

theorem cycleHeights_direct (hP : GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) : GlobalTheory.Published.CycleHeights :=
  GlobalTheory.Published.cycleHeights_of_arCalc (arCalc_direct hP hR)

end GlobalTheory.ArithmeticHeightTower.ArakelovDirectHeights
