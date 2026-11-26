module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStarOdd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.TensorPrimeModuli.SBStarOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrimitiveDiscriminants.IsPrimCmap
noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

namespace LargePrimeDiscriminant

theorem isCyc_cmap (hC : SChain) {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Chn G (m + 1)} (hz : IsCyc z) : IsCyc (cmap f (m + 1) z) := by
  unfold IsCyc at hz ⊢
  rw [hC.2.1 G H f m z, hz, map_zero]

end LargePrimeDiscriminant

end PositivityTheory.KB

end
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

namespace PrimeModuloFree

open LargePrimeDiscriminant

def zc (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n m : ℕ} (z : Chn (GL (Fin n) R) m) :
    ∀ t : ℕ, Chn (GL (Fin (lev l n t)) R) m
  | 0 => z
  | t + 1 => cmap (psi R l (lev l n t)) m (zc R hl z t) -
      ((l : ℝ) ^ (t + 2)) • cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m (zc R hl z t)

theorem le_lev {l : ℕ} (hl : 0 < l) (n : ℕ) : ∀ t, n ≤ lev l n t
  | 0 => le_rfl
  | t + 1 => (le_lev hl n t).trans (Nat.le_mul_of_pos_left _ hl)

theorem isCyc_zc (hC : SChain) (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n k : ℕ}
    {z : Chn (GL (Fin n) R) (k + 1)} (hz : IsCyc z) : ∀ t, IsCyc (zc R hl z t)
  | 0 => hz
  | t + 1 => by
    have h := isCyc_zc hC R hl hz t
    have h1 : bd _ k (cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t)) = 0 := isCyc_cmap hC _ h
    have h2 : bd _ k (cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) (k + 1)
      (zc R hl z t)) = 0 := isCyc_cmap hC _ h
    change bd (GL (Fin (l * lev l n t)) R) k (cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t) -
      ((l : ℝ) ^ (t + 2)) • cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) (k + 1)
        (zc R hl z t)) = 0
    rw [map_sub, map_smul, h1, h2, smul_zero, sub_zero]

theorem wsys_zc (hC : SChain) {R : Type} [CommRing R] {k j : ℕ} {a : ∀ n : ℕ, Chn (GL (Fin n) R) (k + 1) →ₗ[ℝ] ℝ}
    (ha : WSys R k j a) {l : ℕ} (hl : 0 < l) {n : ℕ} {z : Chn (GL (Fin n) R) (k + 1)} (hz : IsCyc z) :
    ∀ t, a (lev l n t) (zc R hl z t) = (∏ i ∈ Finset.range t, ((l : ℝ) ^ j - (l : ℝ) ^ (i + 2))) * a n z
  | 0 => by
    simp only [Finset.range_zero, Finset.prod_empty, one_mul]
    rfl
  | t + 1 => by
    have hc := isCyc_zc hC R hl hz t
    have ih := wsys_zc hC ha hl hz t
    rw [Finset.prod_range_succ]
    change a (l * lev l n t) (cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t) -
      ((l : ℝ) ^ (t + 2)) • cmap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) (k + 1)
        (zc R hl z t)) = _
    rw [map_sub, map_smul, ha.2.2 l (lev l n t) _ hl hc, ha.2.1 _ _ _ _ hc, ih]
    simp only [smul_eq_mul]
    ring

theorem th_zc {k : ℕ} (θ : ∀ (G : Type) [Group G], LinearMap.ker (bd G k) →ₗ[ℝ] ℝ ⊗[ℤ] grpH G (k + 1))
    (hθn : ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (z : LinearMap.ker (bd G k)) (z' : LinearMap.ker (bd H k)),
      z'.1 = cmap f (k + 1) z.1 → θ H z' = LinearMap.baseChange ℝ (grpHMap f (k + 1)).hom (θ G z))
    (hC : SChain) (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n : ℕ} (z : Chn (GL (Fin n) R) (k + 1))
    (hz : IsCyc z) (x : grpH (GL (Fin n) R) (k + 1)) (hx : θ _ ⟨z, hz⟩ = (1 : ℝ) ⊗ₜ x) :
    ∀ t, θ _ ⟨zc R hl z t, isCyc_zc hC R hl hz t⟩ = (1 : ℝ) ⊗ₜ zSeq R hl x t
  | 0 => hx
  | t + 1 => by
    have ih := th_zc θ hθn hC R hl z hz x hx t
    have hc := isCyc_zc hC R hl hz t
    have hs : lev l n t ≤ l * lev l n t := Nat.le_mul_of_pos_left (lev l n t) hl
    change θ (GL (Fin (l * lev l n t)) R) ⟨zc R hl z (t + 1), isCyc_zc hC R hl hz (t + 1)⟩ =
      (1 : ℝ) ⊗ₜ[ℤ] (zSeq R hl x (t + 1) : grpH (GL (Fin (l * lev l n t)) R) (k + 1))
    have e : (⟨zc R hl z (t + 1), isCyc_zc hC R hl hz (t + 1)⟩ : LinearMap.ker (bd (GL (Fin (l * lev l n t)) R) k)) =
        ⟨cmap (psi R l (lev l n t)) (k + 1) (zc R hl z t), isCyc_cmap hC _ hc⟩ -
          ((l : ℝ) ^ (t + 2)) • ⟨cmap (stab R (lev l n t) (l * lev l n t) hs) (k + 1) (zc R hl z t),
            isCyc_cmap hC _ hc⟩ := rfl
    rw [e, map_sub, map_smul, hθn _ _ (psi R l (lev l n t)) ⟨_, hc⟩ _ rfl,
      hθn _ _ (stab R (lev l n t) (l * lev l n t) hs) ⟨_, hc⟩ _ rfl, ih,
      LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    change _ = (1 : ℝ) ⊗ₜ ((grpHMap (psi R l (lev l n t)) (k + 1)).hom (zSeq R hl x t) -
      l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) hs) (k + 1)).hom (zSeq R hl x t))
    rw [TensorProduct.tmul_sub]
    congr 1
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact (map_nsmul (TensorProduct.mk ℤ ℝ _ 1) _ _).symm

end PrimeModuloFree

end PositivityTheory.KB

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddSpanRank.RankSpanLe
open scoped TensorProduct

namespace PositivityTheory.KB.TwOdd

theorem rank_span_le {A : Type} [AddCommGroup A] [inst : Module ℤ A] (S : Set A) {ι C : Type} [Fintype ι] [AddCommGroup C]
    [Module ℝ C] (θ : C →ₗ[ℝ] ℝ ⊗[ℤ] A) (T : C →ₗ[ℝ] (ι → ℝ)) (h0 : ∀ z, T z = 0 → θ z = 0)
    (hS : ∀ s ∈ S, ∃ z, θ z = (1 : ℝ) ⊗ₜ s) :
    Module.rank ℤ (Submodule.span ℤ S) ≤ Fintype.card ι := by
  classical
  obtain rfl : inst = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  have hker : LinearMap.ker T ≤ LinearMap.ker θ := fun z hz => h0 z hz
  have hrank : Module.rank ℝ (LinearMap.range θ) ≤ Fintype.card ι := by
    have e1 : LinearMap.range ((LinearMap.ker T).liftQ θ hker) = LinearMap.range θ :=
      Submodule.range_liftQ _ _ _
    calc Module.rank ℝ (LinearMap.range θ)
        = Module.rank ℝ (LinearMap.range ((LinearMap.ker T).liftQ θ hker)) := by rw [e1]
      _ ≤ Module.rank ℝ (C ⧸ LinearMap.ker T) := rank_range_le _
      _ = Module.rank ℝ (LinearMap.range T) := T.quotKerEquivRange.rank_eq
      _ ≤ Module.rank ℝ (ι → ℝ) := Submodule.rank_le _
      _ = Fintype.card ι := by simp
  have hmem : ∀ x ∈ Submodule.span ℤ S, (1 : ℝ) ⊗ₜ[ℤ] x ∈ LinearMap.range θ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨z, hz⟩ := hS s hs
      exact ⟨z, hz⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
    | smul n x _ hx =>
      rw [TensorProduct.tmul_smul]
      exact zsmul_mem hx n
  apply rank_le
  intro s hs
  have hA : LinearIndependent ℤ (fun i : s => ((i : Submodule.span ℤ S) : A)) :=
    hs.map' (Submodule.span ℤ S).subtype (Submodule.ker_subtype _)
  have hR := Module.Flat.linearIndependent_one_tmul (S := ℝ) hA
  let w : s → LinearMap.range θ := fun i =>
    ⟨(1 : ℝ) ⊗ₜ[ℤ] ((i : Submodule.span ℤ S) : A), hmem _ (i : Submodule.span ℤ S).2⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp (LinearMap.range θ).subtype hR
  have h2 := hw.cardinal_le_rank.trans hrank
  simpa using h2

end PositivityTheory.KB.TwOdd
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

open PrimeModuloFree LargePrimeDiscriminant in
theorem sBStarOdd_of : SBStarOdd := by
  intro hC hSep hBr hStab hSurj hWt L _ _ hTC k hk hkr l hl n hn
  haveI : IsTotallyComplex L := hTC
  obtain ⟨θ, hθs, hθ0, hθn⟩ := hBr k
  obtain ⟨τ, hτW, hτ⟩ := hWt L k hk
  have hcard : Fintype.card (InfinitePlace L) = nrComplexPlaces L := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hM : 2 * (k + 1) + 4 ≤ lev l n k := le_trans hn (PrimeModuloFree.le_lev hl n k)
  let C : Submodule ℝ (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker :=
    Submodule.span ℝ {y | ∃ z0 : Chn (GL (Fin n) (𝓞 L)) (k + 1), IsCyc z0 ∧
      (y : Chn (GL (Fin (lev l n k)) (𝓞 L)) (k + 1)) = PrimeModuloFree.zc (𝓞 L) hl z0 k}
  calc _ ≤ ((Fintype.card (InfinitePlace L) : ℕ) : Cardinal) :=
        TwOdd.rank_span_le _ ((θ (GL (Fin (lev l n k)) (𝓞 L))).comp C.subtype)
          ((LinearMap.pi fun w : InfinitePlace L => τ w (lev l n k)).comp
            ((bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker.subtype.comp C.subtype)) ?_ ?_
    _ = _ := by rw [hcard]
  · intro z hT
    have hTw : ∀ w, τ w (lev l n k) (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1 = 0 :=
      fun w => congrFun hT w
    show (θ _) (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker) = 0
    refine (hθ0 _ _).2 ?_
    by_contra hnb
    have hcyc : IsCyc (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1 :=
      LinearMap.mem_ker.mp (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).2
    obtain ⟨N, hMN, hN⟩ := hSurj L hTC k hkr (lev l n k)
    have hz'c := LargePrimeDiscriminant.isCyc_cmap hC (stab (𝓞 L) (lev l n k) N hMN) hcyc
    have hz'nb : ¬ IsBd (cmap (stab (𝓞 L) (lev l n k) N hMN) (k + 1)
        (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1) :=
      fun h => hnb ((hStab (𝓞 L) k (lev l n k) N hMN hM).1 _ hcyc h)
    obtain ⟨c, hcI, hcd, hcne⟩ := hSep _ k _ hz'c hz'nb
    obtain ⟨ω, hωI, hω⟩ := hN c hcI hcd
    obtain ⟨cc, a, ha, hdec⟩ := hτ N ω hωI
    have hazero : ∀ j ∈ Finset.Icc 2 (k + 1), ∀ y ∈ C,
        a j (lev l n k) (y : Chn (GL (Fin (lev l n k)) (𝓞 L)) (k + 1)) = 0 := by
      intro j hj y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z0, hz0, hx⟩ := hx
        rw [hx, PrimeModuloFree.wsys_zc (R := 𝓞 L) hC (ha j hj) hl hz0 k]
        apply mul_eq_zero_of_left
        rw [Finset.mem_Icc] at hj
        apply Finset.prod_eq_zero (i := j - 2)
        · rw [Finset.mem_range]; omega
        · rw [Nat.sub_add_cancel hj.1, sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul r x _ hx => simp [hx]
    apply hcne
    rw [hω _ hz'c, hdec _ hz'c]
    have h1 : ∀ w, τ w N (cmap (stab (𝓞 L) (lev l n k) N hMN) (k + 1)
        (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1) = 0 := by
      intro w
      rw [(hτW w).2.1 _ _ hMN _ hcyc]
      exact hTw w
    have h2 : ∀ j ∈ Finset.Icc 2 (k + 1), a j N (cmap (stab (𝓞 L) (lev l n k) N hMN) (k + 1)
        (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1) = 0 := by
      intro j hj
      rw [(ha j hj).2.1 _ _ hMN _ hcyc]
      exact hazero j hj _ z.2
    rw [Finset.sum_eq_zero (fun w _ => by rw [h1 w, mul_zero]), Finset.sum_eq_zero h2, add_zero]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨z0, hz0⟩ := hθs (GL (Fin n) (𝓞 L)) (1 ⊗ₜ x)
    refine ⟨⟨⟨PrimeModuloFree.zc (𝓞 L) hl z0.1 k,
      PrimeModuloFree.isCyc_zc hC (𝓞 L) hl (LinearMap.mem_ker.mp z0.2) k⟩,
      Submodule.subset_span ⟨z0.1, LinearMap.mem_ker.mp z0.2, rfl⟩⟩, ?_⟩
    exact PrimeModuloFree.th_zc θ hθn hC (𝓞 L) hl z0.1 (LinearMap.mem_ker.mp z0.2) x hz0 k

end PositivityTheory.KB

end
