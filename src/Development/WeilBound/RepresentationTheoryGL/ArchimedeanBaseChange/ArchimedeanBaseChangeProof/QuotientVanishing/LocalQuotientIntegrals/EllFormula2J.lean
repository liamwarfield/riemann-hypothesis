module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanishOfSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMemUniRad
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AevalTranspose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogSizeNonneg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnormOfRealToRealLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCornerGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddOfSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceFiniteAdeleRingCmField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteTopologyProdMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuotNormaliserIndicator

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjCentMul
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.ChiGamGlobal

theorem twConj_cent_mul {G : Type} [Group G] (θ : Monoid.End G) {t δ : G} (x : G) (ht : twConj θ t δ = δ) :
    twConj θ (t * x) δ = twConj θ x δ := by
  have h : t⁻¹ * δ * θ t = δ := ht
  calc twConj θ (t * x) δ = x⁻¹ * (t⁻¹ * δ * θ t) * θ x := by
        simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    _ = twConj θ x δ := by rw [h]; rfl

theorem logSize_nonneg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (g : GA E n) :
    0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

theorem chiGam_of (hI : OnlyIsotropic) (hP : PosY) (hC : ChainSum) : ChiGam := by
  classical
  intro E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hI E n
  obtain ⟨C₂, h₂⟩ := hP E n
  refine ⟨max C₁ C₂, fun d m Wof a hiso huniq h0 hmeet hle hreg hdeg τ x hτ t ht => ?_⟩
  have hs : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by
    have := logSize_nonneg (twConj (thetaA E n) x (ratGL E n d))
    linarith
  have b₁ := (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hs).trans hτ
  have b₂ := (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hs).trans hτ
  have hconj : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) :=
    twConj_cent_mul _ x ht
  have hind := (hC m).1 _ (a t) (h₂ d m Wof hiso huniq h0 hmeet hle hreg τ x b₂)
  have hiff : t * x ∈ cutSet E n τ ↔
      ∀ e, sdot e (a t) ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e) := by
    rw [h₁ τ (t * x) d (by rw [hconj]; exact b₁)]
    constructor
    · intro h e
      have := h (Wof e) (hiso e).1 (hiso e).2
      rw [hdeg t ht x e] at this
      linarith
    · intro h W hW₁ hW₂
      obtain ⟨e, rfl, _⟩ := huniq W ⟨hW₁, hW₂⟩
      have := h e
      rw [hdeg t ht x e]
      linarith
  rw [hind]
  by_cases hx : t * x ∈ cutSet E n τ
  · have ha : a t ∈ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      hiff.1 hx
    rw [Set.indicator_of_mem ha, chiT, Set.indicator_of_mem hx]
    simp
  · have ha : a t ∉ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      fun h => hx (hiff.2 h)
    rw [Set.indicator_of_notMem ha, chiT, Set.indicator_of_notMem hx]
    simp

end GlobalTheory.CompanionTheory.ChiGamGlobal

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImgEqOfInvariant
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalIntertwining
theorem UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine :
    ∀ {K : Type} [inst : Field K] {M N : Type} [inst_1 : AddCommGroup M]
    [inst_2 : _root_.Module K M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module K N] (φ : M →ₗ[K] N)
    (f : Module.End K M) (f' : Module.End K N),
    (∀ (x : M), (φ : M → N) ((f : M → M) x) = (f' : N → N) ((φ : M → N) x)) →
      ∀ (p : Polynomial K) (x : M),
        (φ : M → N) (((Polynomial.aeval f : Polynomial K → Module.End K M) p : M → M) x) =
          ((Polynomial.aeval f' : Polynomial K → Module.End K N) p : N → N) ((φ : M → N) x) := by
  intro K _ M N _ _ _ _ φ f f' h p
  have hpow : ∀ (n : ℕ) (x : M), φ ((f ^ n) x) = (f' ^ n) (φ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    intro x
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

open Polynomial Matrix PositivityTheory.Rg.BcB

noncomputable section

namespace GlobalTheory.CompanionTheory.PairParam

section Comb

variable {A : Type} [Finite A]

theorem exists_signs (ι : A → A) (hι : ∀ a, ι (ι a) = a) :
    ∃ (m : ℕ) (T : (Fin m → SignType) → Set A), (∀ e, ∀ a ∈ T e, ι a ∉ T e) ∧
      (∀ I : Set A, (∀ a ∈ I, ι a ∉ I) → ∃! e, T e = I) ∧ T 0 = ∅ ∧
      (∀ e e', T (sMeet e e') = T e ∩ T e') ∧ (∀ e e', SLe e e' → T e ⊆ T e') := by
  classical
  obtain ⟨k, ⟨q⟩⟩ := Finite.exists_equiv_fin A
  letI : Fintype A := Fintype.ofEquiv _ q.symm
  letI : LinearOrder A := LinearOrder.lift' q q.injective
  let R : Finset A := Finset.univ.filter fun a => a < ι a
  let r : Fin R.card → A := fun j => (R.equivFin.symm j : A)
  have hr : ∀ j, r j < ι (r j) := fun j => (Finset.mem_filter.1 (R.equivFin.symm j).2).2
  have hinj : Function.Injective r := fun i j h => R.equivFin.symm.injective (Subtype.ext h)
  have hsurj : ∀ a, a < ι a → ∃ j, r j = a := fun a ha =>
    ⟨R.equivFin ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩, by simp [r]⟩
  have hne : ∀ i j, r i ≠ ι (r j) := fun i j h => by
    have h1 : ι (r i) = r j := by rw [h, hι]
    have h2 := hr i
    have h3 := hr j
    rw [h1] at h2
    rw [← h] at h3
    exact lt_asymm h2 h3
  let T : (Fin R.card → SignType) → Set A := fun e =>
    {a | ∃ j, (a = r j ∧ e j = 1) ∨ (a = ι (r j) ∧ e j = -1)}
  have hpos : ∀ e j, r j ∈ T e ↔ e j = 1 := fun e j => by
    constructor
    · rintro ⟨i, ⟨h, hi⟩ | ⟨h, _⟩⟩
      · rwa [hinj h]
      · exact absurd h (hne _ _)
    · exact fun h => ⟨j, Or.inl ⟨rfl, h⟩⟩
  have hneg : ∀ e j, ι (r j) ∈ T e ↔ e j = -1 := fun e j => by
    constructor
    · rintro ⟨i, ⟨h, _⟩ | ⟨h, hi⟩⟩
      · exact absurd h.symm (hne _ _)
      · have : r j = r i := by simpa [hι] using congrArg ι h
        rwa [hinj this]
    · exact fun h => ⟨j, Or.inr ⟨rfl, h⟩⟩
  have hext : ∀ e e', T e = T e' → e = e' := fun e e' h => by
    funext j
    have h1 := hpos e j
    have h2 := hneg e j
    rw [h] at h1 h2
    rw [hpos e' j] at h1
    rw [hneg e' j] at h2
    cases he : e j <;> cases he' : e' j <;> simp_all
  refine ⟨R.card, T, ?_, ?_, ?_, ?_, ?_⟩
  · rintro e a ⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ hc
    · have := (hneg e j).1 hc
      rw [h] at this
      exact absurd this (by decide)
    · rw [hι] at hc
      have := (hpos e j).1 hc
      rw [h] at this
      exact absurd this (by decide)
  · intro I hI
    let e : Fin R.card → SignType := fun j => if r j ∈ I then 1 else if ι (r j) ∈ I then -1 else 0
    have he : T e = I := by
      ext a
      constructor
      · rintro ⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
        · by_contra hc
          simp only [e, hc, if_false] at h
          split_ifs at h <;> exact absurd h (by decide)
        · by_contra hc
          simp only [e, hc, if_false] at h
          split_ifs at h <;> exact absurd h (by decide)
      · intro ha
        have hna := hI a ha
        rcases lt_trichotomy a (ι a) with h | h | h
        · obtain ⟨j, rfl⟩ := hsurj a h
          exact ⟨j, Or.inl ⟨rfl, by simp [e, ha]⟩⟩
        · rw [← h] at hna
          exact absurd ha hna
        · obtain ⟨j, hj⟩ := hsurj (ι a) (by rwa [hι])
          refine ⟨j, Or.inr ⟨by rw [hj, hι], ?_⟩⟩
          have h2 : ι (r j) ∈ I := by rwa [hj, hι]
          have h3 : r j ∉ I := by rwa [hj]
          simp [e, h2, h3]
    exact ⟨e, he, fun e' h => hext _ _ (h.trans he.symm)⟩
  · ext a
    simp [T]
  · intro e e'
    ext a
    constructor
    · rintro ⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
      · have h1 : e j = e' j ∧ e j = 1 := by
          by_cases hc : e j = e' j
          · simpa [sMeet, hc] using h
          · simp [sMeet, hc] at h
        exact ⟨(hpos _ _).2 h1.2, (hpos _ _).2 (h1.1 ▸ h1.2)⟩
      · have h1 : e j = e' j ∧ e j = -1 := by
          by_cases hc : e j = e' j
          · simpa [sMeet, hc] using h
          · simp [sMeet, hc] at h
        exact ⟨(hneg _ _).2 h1.2, (hneg _ _).2 (h1.1 ▸ h1.2)⟩
    · rintro ⟨⟨j, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩, h2⟩
      · have h3 := (hpos _ _).1 h2
        exact ⟨j, Or.inl ⟨rfl, by simp [sMeet, h, h3]⟩⟩
      · have h3 := (hneg _ _).1 h2
        exact ⟨j, Or.inr ⟨rfl, by simp [sMeet, h, h3]⟩⟩
  · intro e e' h a
    rintro ⟨j, ⟨rfl, h1⟩ | ⟨rfl, h1⟩⟩
    · exact ⟨j, Or.inl ⟨rfl, by rw [h j (by rw [h1]; decide), h1]⟩⟩
    · exact ⟨j, Or.inr ⟨rfl, by rw [h j (by rw [h1]; decide), h1]⟩⟩

end Comb

theorem exists_invol {A : Type} (c : Set A → Set A) (hanti : Antitone c) (hinv : ∀ I, c (c I) = I) :
    ∃ ι : A → A, (∀ a, ι (ι a) = a) ∧ ∀ I, c I = (ι '' I)ᶜ := by
  classical

  let cd : Set A ≃o (Set A)ᵒᵈ :=
    { toFun := fun I => OrderDual.toDual (c I)
      invFun := fun I => c (OrderDual.ofDual I)
      left_inv := hinv
      right_inv := fun I => by simp [hinv]
      map_rel_iff' := by
        intro I J
        constructor
        · intro h
          have := hanti (show c J ≤ c I from h)
          rwa [hinv, hinv] at this
        · intro h
          exact hanti h }
  have hcompl : ∀ I, c Iᶜ = (c I)ᶜ := fun I => by
    have h := cd.isCompl (isCompl_compl (x := I))
    have h2 : IsCompl (c I) (c Iᶜ) := h.ofDual
    exact h2.compl_eq.symm
  let ψ : Set A ≃o Set A :=
    { toFun := fun I => (c I)ᶜ
      invFun := fun I => (c I)ᶜ
      left_inv := fun I => by simp [← hcompl, hinv]
      right_inv := fun I => by simp [← hcompl, hinv]
      map_rel_iff' := by
        intro I J
        constructor
        · intro h
          have h1 : c J ≤ c I := compl_le_compl_iff_le.1 h
          have := hanti h1
          rwa [hinv, hinv] at this
        · intro h
          exact compl_le_compl (hanti h) }
  have hatom : ∀ a, ∃ b, ψ {a} = {b} := fun a =>
    Set.isAtom_iff.1 ((ψ.isAtom_iff _).2 (Set.isAtom_singleton a))
  choose ι hι using hatom
  have hψψ : ∀ I, ψ (ψ I) = I := fun I => ψ.left_inv I
  have hsub : ∀ I, ∀ a ∈ I, ι a ∈ ψ I := fun I a ha => by
    have h1 : ψ {a} ≤ ψ I := ψ.monotone (Set.singleton_subset_iff.2 ha)
    rw [hι] at h1
    exact h1 rfl
  have hιι : ∀ a, ι (ι a) = a := fun a => by
    have h1 := hψψ {a}
    rw [hι, hι] at h1
    exact Set.singleton_injective h1
  refine ⟨ι, hιι, fun I => ?_⟩
  have h2 : ψ I = ι '' I := by
    ext b
    constructor
    · intro hb
      have := hsub _ _ hb
      rw [hψψ] at this
      exact ⟨_, this, hιι b⟩
    · rintro ⟨a, ha, rfl⟩
      exact hsub _ _ ha
  rw [← h2]
  exact (compl_compl _).symm

section Lin

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_intertwine {M N : Type} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (φ : M →ₗ[K] N)
    (f : Module.End K M) (f' : Module.End K N) (h : ∀ x, φ (f x) = f' (φ x)) (p : K[X]) (x : M) :
    φ (aeval f p x) = aeval f' p (φ x) :=
  _root_.UpperTheory.Reformulated.B.AevalIntertwining.aeval_intertwine φ f f' h p x

theorem aeval_restrict_coe (f : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) (p : K[X]) (w : W) :
    ((aeval (f.restrict hW : Module.End K W) p) w : V) = aeval f p (w : V) :=
  (aeval_intertwine W.subtype (f.restrict hW) f (fun _ => rfl) p w)

theorem aeval_mem (f : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) (p : K[X]) {w : V} (hw : w ∈ W) :
    aeval f p w ∈ W := by
  have := aeval_restrict_coe f W hW p ⟨w, hw⟩
  rw [← show _ = aeval f p w from this]
  exact Subtype.property _

theorem aeval_mapQ (f : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) (p : K[X]) (v : V) :
    aeval (W.mapQ W f (fun x hx => hW x hx) : Module.End K (V ⧸ W)) p (W.mkQ v) = W.mkQ (aeval f p v) :=
  (aeval_intertwine W.mkQ f (W.mapQ W f (fun x hx => hW x hx)) (fun _ => rfl) p v).symm

theorem invariant_eq_ker [FiniteDimensional K V] (f : Module.End K V) (hs : Squarefree f.charpoly) (W : Submodule K V)
    (hW : ∀ x ∈ W, f x ∈ W) : ∃ a b : K[X], a * b = f.charpoly ∧ W = LinearMap.ker (aeval f a) := by
  have hab := GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W f hW
  set a := LinearMap.charpoly (f.restrict hW) with ha
  set b := LinearMap.charpoly (W.mapQ W f (fun x hx => hW x hx)) with hb
  refine ⟨a, b, hab.symm, le_antisymm ?_ ?_⟩
  · intro w hw
    have h1 := aeval_restrict_coe f W hW a ⟨w, hw⟩
    rw [ha, LinearMap.aeval_self_charpoly] at h1
    rw [LinearMap.mem_ker, ← show _ = aeval f _ w from h1]
    rfl
  · intro v hv
    rw [hab] at hs
    have hco : IsCoprime a b := (squarefree_mul_iff.1 hs).1.isCoprime
    obtain ⟨u, w, huw⟩ := hco
    have hbv : aeval f b v ∈ W := by
      have h1 := aeval_mapQ f W hW b v
      rw [hb, LinearMap.aeval_self_charpoly] at h1
      exact (Submodule.Quotient.mk_eq_zero W).1 h1.symm
    have h2 : v = aeval f w (aeval f b v) := by
      have h3 := congrArg (fun p => aeval f p v) huw
      simp only [map_add (f := _), map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at h3
      rw [LinearMap.mem_ker.1 hv, map_zero, zero_add] at h3
      exact h3.symm
    rw [h2]
    exact aeval_mem f W hW w hbv

theorem ker_le_of_dvd (f : Module.End K V) {P p : K[X]} (h : P ∣ p) :
    LinearMap.ker (aeval f P) ≤ LinearMap.ker (aeval f p) := by
  obtain ⟨c, rfl⟩ := h
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [mul_comm, map_mul, Module.End.mul_apply, hx, map_zero]

theorem exists_atoms [FiniteDimensional K V] (f : Module.End K V) (hs : Squarefree f.charpoly) :
    ∃ (A : Type) (_ : Finite A) (L : A → Submodule K V), iSupIndep L ∧ (∀ i, L i ≠ ⊥) ∧
      (∀ i, ∀ x ∈ L i, f x ∈ L i) ∧
      ∀ W : Submodule K V, (∀ x ∈ W, f x ∈ W) → ∃ I : Set A, W = ⨆ i ∈ I, L i := by
  classical
  have hm : f.charpoly.Monic := LinearMap.charpoly_monic f
  let F := (UniqueFactorizationMonoid.normalizedFactors f.charpoly).toFinset
  let Lk : K[X] → Submodule K V := fun P => LinearMap.ker (aeval f P)
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hm.ne_zero).1 hs
  have hprod : ∏ P ∈ F, P = f.charpoly := by
    have h1 : F.val = UniqueFactorizationMonoid.normalizedFactors f.charpoly := by
      simp only [F, Multiset.toFinset_val, hnd.dedup]
    rw [Finset.prod, h1, Multiset.map_id', UniqueFactorizationMonoid.prod_normalizedFactors_eq hm.ne_zero,
      hm.normalize_eq_self]
  have hirr : ∀ P ∈ F, Irreducible P := fun P hP =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor P (Multiset.mem_toFinset.1 hP)
  have hnorm : ∀ P ∈ F, normalize P = P := fun P hP =>
    UniqueFactorizationMonoid.normalize_normalized_factor P (Multiset.mem_toFinset.1 hP)
  have hcop : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → IsCoprime P Q := fun P hP Q hQ hne => by
    refine ((hirr P hP).coprime_iff_not_dvd).2 fun hd => hne ?_
    exact dvd_antisymm_of_normalize_eq (hnorm P hP) (hnorm Q hQ) hd ((hirr P hP).dvd_symm (hirr Q hQ) hd)
  have hker : ∀ s : Finset K[X], s ⊆ F → LinearMap.ker (aeval f (∏ P ∈ s, P)) = ⨆ P ∈ s, Lk P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty, map_one, Finset.notMem_empty, iSup_false, iSup_bot]
      exact LinearMap.ker_id
    | insert a s ha ih =>
      intro hsF
      have hs' : s ⊆ F := (Finset.subset_insert a s).trans hsF
      have haF : a ∈ F := hsF (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih hs', Finset.iSup_insert]
      exact IsCoprime.prod_right fun b hb => hcop a haF b (hs' hb) fun h => ha (h ▸ hb)
  have htop : ⨆ P ∈ F, Lk P = ⊤ := by
    rw [← hker F subset_rfl, hprod, LinearMap.aeval_self_charpoly, LinearMap.ker_zero]
  let A := {P : K[X] // P ∈ F ∧ Lk P ≠ ⊥}
  haveI : Finite A := Finite.of_injective (fun a : A => (⟨a.1, a.2.1⟩ : F))
    (fun a b h => Subtype.ext (congrArg (fun z : {x // x ∈ F} => z.1) h))
  let L : A → Submodule K V := fun a => Lk a.1
  refine ⟨A, inferInstance, L, ?_, fun a => a.2.2, fun a x hx => ?_, fun W hW => ?_⟩
  · intro a
    have hle : ⨆ j, ⨆ (_ : j ≠ a), L j ≤ LinearMap.ker (aeval f (∏ P ∈ F.erase a.1, P)) := by
      rw [hker _ (Finset.erase_subset _ _)]
      refine iSup₂_le fun j hj => ?_
      exact le_iSup₂_of_le j.1 (Finset.mem_erase.2 ⟨fun h => hj (Subtype.ext h), j.2.1⟩) le_rfl
    refine Disjoint.mono_right hle (disjoint_ker_aeval_of_isCoprime f ?_)
    exact IsCoprime.prod_right fun Q hQ =>
      hcop _ a.2.1 _ (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ).symm
  · have h1 : aeval f a.1 (f x) = f (aeval f a.1 x) := (aeval_intertwine f f f (fun _ => rfl) a.1 x).symm
    have h2 : aeval f a.1 x = 0 := hx
    show aeval f a.1 (f x) = 0
    rw [h1, h2, map_zero]
  · obtain ⟨p, q, hpq, hWe⟩ := invariant_eq_ker f hs W hW
    refine ⟨{a | a.1 ∣ p}, ?_⟩
    have h1 : ⨆ i ∈ {a : A | a.1 ∣ p}, L i ≤ W := by
      rw [hWe]
      exact iSup₂_le fun i hi => ker_le_of_dvd f hi
    have h2 : (⊤ : Submodule K V) ≤ (⨆ i ∈ {a : A | a.1 ∣ p}, L i) ⊔ ⨆ P ∈ F.filter (fun P => ¬ P ∣ p), Lk P := by
      rw [← htop]
      refine iSup₂_le fun P hP => ?_
      by_cases hd : P ∣ p
      · by_cases hb : Lk P = ⊥
        · rw [hb]; exact bot_le
        · exact le_sup_of_le_left (le_iSup₂_of_le (⟨P, hP, hb⟩ : A) hd le_rfl)
      · exact le_sup_of_le_right (le_iSup₂_of_le P (Finset.mem_filter.2 ⟨hP, hd⟩) le_rfl)
    have h3 : ⨆ P ∈ F.filter (fun P => ¬ P ∣ p), Lk P ≤ LinearMap.ker (aeval f q) := by
      refine iSup₂_le fun P hP => ?_
      obtain ⟨hPF, hPp⟩ := Finset.mem_filter.1 hP
      have hd : P ∣ p * q := by
        rw [hpq, ← hprod]
        exact Finset.dvd_prod_of_mem _ hPF
      exact ker_le_of_dvd f (((hirr P hPF).prime.dvd_or_dvd hd).resolve_left hPp)
    have hco : IsCoprime p q := by
      rw [← hpq] at hs
      exact (squarefree_mul_iff.1 hs).1.isCoprime
    have hdis := disjoint_ker_aeval_of_isCoprime f hco
    refine le_antisymm (fun x hx => ?_) h1
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h2 (Submodule.mem_top (x := x)))
    have hyW := h1 hy
    have hzW : z ∈ W := by simpa using W.sub_mem hx hyW
    have hz0 : z = 0 := by
      rw [hWe] at hzW
      exact (Submodule.disjoint_def.1 hdis) z hzW (h3 hz)
    rw [hz0, add_zero]
    exact hy

end Lin

section Main

open PositivityTheory.Rg.BcB.D4

theorem perp_anti {K : Type} [Field K] {n : ℕ} (σ : K →+* K) {W W' : Submodule K (Fin n → K)} (h : W ≤ W') :
    perp σ W' ≤ perp σ W := fun _ hy x hx => hy x (h hx)

theorem perpD_anti {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (d : GL (Fin n) K) {W W' : Submodule K (Fin n → K)}
    (h : W ≤ W') : perpD σ d W' ≤ perpD σ d W :=
  Submodule.map_mono (perp_anti σ h)

theorem img_eq_of_invariant {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K))
    (h : ∀ x ∈ W, Matrix.toLin' g.val x ∈ W) : img g W = W := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro a b hab
    have h1 := congrArg (fun z => (g⁻¹ : GL (Fin n) K).val *ᵥ z) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

theorem pairParam : PairParam := by
  intro E _ _ _ n d hd
  let f : Module.End E (Fin n → E) := Matrix.toLin' (nrm d).val
  have hcp : LinearMap.charpoly f = (nrm d).val.charpoly := by
    simp [f, Matrix.charpoly_toLin']
  have hs : Squarefree (LinearMap.charpoly f) := by
    rw [hcp]
    exact Polynomial.Separable.squarefree hd
  obtain ⟨A, hA, L, hind, hne, hinv, hall⟩ := exists_atoms f hs
  let S : Set A → Submodule E (Fin n → E) := fun I => ⨆ i ∈ I, L i
  have hSinv : ∀ I, ∀ x ∈ S I, f x ∈ S I := by
    intro I x hx
    have h1 : S I ≤ (S I).comap f := by
      refine iSup₂_le fun i hi x hx => ?_
      exact (le_iSup₂_of_le (f := fun i (_ : i ∈ I) => L i) i hi le_rfl : L i ≤ S I) (hinv i x hx)
    exact h1 hx
  have hSle : ∀ I J, S I ≤ S J ↔ I ⊆ J := by
    intro I J
    constructor
    · intro h a ha
      by_contra hc
      have h1 : L a ≤ S I := le_iSup₂_of_le (f := fun i (_ : i ∈ I) => L i) a ha le_rfl
      have h2 : S J ≤ ⨆ j, ⨆ (_ : j ≠ a), L j :=
        iSup₂_le fun j hj => le_iSup₂_of_le (f := fun j (_ : j ≠ a) => L j) j (fun e => hc (e ▸ hj)) le_rfl
      exact hne a ((hind a).eq_bot_of_le (h1.trans (h.trans h2)))
    · intro h
      exact biSup_mono h
  have hSinj : ∀ I J, S I = S J → I = J := fun I J h =>
    Set.Subset.antisymm ((hSle _ _).1 h.le) ((hSle _ _).1 h.ge)
  have hstab : ∀ I, img (nrm d) (S I) = S I := fun I => img_eq_of_invariant _ _ (hSinv I)
  have hexists : ∀ W, img (nrm d) W = W → ∃ I, W = S I := by
    intro W hW
    refine hall W fun x hx => ?_
    rw [← hW]
    exact ⟨x, hx, rfl⟩
  have hφφ : ∀ W, perpD (conjE E) d (perpD (conjE E) d W) = img (nrm d) W := fun W =>
    GlobalTheory.CompanionTheory.FlagCent.perpD_perpD (conjE E) (fun a => NumberField.IsCMField.complexConj_apply_apply E a) d W
  have hφstab : ∀ W, img (nrm d) W = W → img (nrm d) (perpD (conjE E) d W) = perpD (conjE E) d W := by
    intro W hW
    rw [← hφφ, hφφ W, hW]
  have hcex : ∀ I, ∃ J, perpD (conjE E) d (S I) = S J := fun I => hexists _ (hφstab _ (hstab I))
  choose c hc using hcex
  have hanti : Antitone c := by
    intro I J h
    refine (hSle _ _).1 ?_
    rw [← hc, ← hc]
    exact perpD_anti _ _ ((hSle _ _).2 h)
  have hcc : ∀ I, c (c I) = I := fun I => hSinj _ _ (by rw [← hc, ← hc, hφφ, hstab])
  obtain ⟨ι, hι, hcι⟩ := exists_invol c hanti hcc
  obtain ⟨m, T, hT1, hT2, hT3, hT4, hT5⟩ := exists_signs ι hι
  have hSinf : ∀ I J, S (I ∩ J) = S I ⊓ S J := by
    intro I J
    obtain ⟨Q, hQ⟩ := hall (S I ⊓ S J) fun x hx => ⟨hSinv I x hx.1, hSinv J x hx.2⟩
    have h1 : Q ⊆ I := (hSle _ _).1 (hQ.symm.le.trans inf_le_left)
    have h2 : Q ⊆ J := (hSle _ _).1 (hQ.symm.le.trans inf_le_right)
    have h3 : I ∩ J ⊆ Q := (hSle _ _).1 (by
      have : S (I ∩ J) ≤ S I ⊓ S J :=
        le_inf ((hSle _ _).2 Set.inter_subset_left) ((hSle _ _).2 Set.inter_subset_right)
      exact this.trans hQ.le)
    have h4 : I ∩ J = Q := Set.Subset.antisymm h3 (Set.subset_inter h1 h2)
    rw [h4]
    exact hQ.symm
  refine ⟨m, fun e => S (T e), fun e => ⟨hstab _, ?_⟩, fun W hW => ?_, ?_, fun e e' => ?_, fun e e' h => ?_,
    fun e => ?_⟩
  · rw [hc, hSle, hcι]
    rintro a ha ⟨b, hb, rfl⟩
    exact hT1 _ _ hb ha
  · obtain ⟨I, rfl⟩ := hexists W hW.1
    have h2 := hW.2
    rw [hc, hSle, hcι] at h2
    have h3 : ∀ a ∈ I, ι a ∉ I := fun a ha hb => h2 ha ⟨ι a, hb, hι a⟩
    obtain ⟨e, he, hu⟩ := hT2 I h3
    exact ⟨e, congrArg S he, fun e' h => hu e' (hSinj _ _ h)⟩
  · show S (T 0) = ⊥
    rw [hT3]
    simp [S]
  · show S (T (sMeet e e')) = S (T e) ⊓ S (T e')
    rw [hT4, hSinf]
  · exact (hSle _ _).2 (hT5 e e' h)
  · show perpD (conjE E) d (perpD (conjE E) d (S (T e))) = S (T e)
    rw [hφφ, hstab]

end Main

end GlobalTheory.CompanionTheory.PairParam
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanish
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.IsCompactEntryBall
noncomputable section

open Matrix Polynomial PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.LocP

variable {n : ℕ}

theorem exists_diag (γ : Matrix (Fin n) (Fin n) ℂ) (h : γ.charpoly.Separable) :
    ∃ (P : GL (Fin n) ℂ) (lam : Fin n → ℂ), Function.Injective lam ∧
      γ = P.val * diagonal lam * (P⁻¹).val := by
  classical
  have hnd : γ.charpoly.roots.Nodup := nodup_roots h
  have hcard : γ.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits γ.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ γ.charpoly.roots.toFinset := (Finset.equivFinOfCardEq hcard).symm
  let lam : Fin n → ℂ := fun i => (e i : ℂ)
  have hl : Function.Injective lam := Subtype.val_injective.comp e.injective
  have hroot : ∀ i, γ.charpoly.IsRoot (lam i) := fun i =>
    isRoot_of_mem_roots (Multiset.mem_toFinset.1 (e i).2)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' γ) (lam i) := fun i => by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hroot i
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' γ) lam hl v hv
  let Pm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a i => v i a
  have hPu : IsUnit Pm := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  obtain ⟨P, hP⟩ := hPu
  have hγ : γ * P.val = P.val * diagonal lam := by
    rw [hP]
    ext a i
    have h1 := congrFun (hv i).apply_eq_smul a
    rw [Matrix.toLin'_apply] at h1
    rw [Matrix.mul_diagonal]
    simp only [Pm, Matrix.of_apply]
    rw [mul_comm]
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h1
  refine ⟨P, lam, hl, ?_⟩
  rw [← hγ, Matrix.mul_assoc, ← Units.val_mul]
  simp

theorem aeval_conj_units (y : GL (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ[X]) :
    aeval ((y⁻¹).val * A * y.val) q = (y⁻¹).val * aeval A q * y.val := by
  have hpow : ∀ k : ℕ, ((y⁻¹).val * A * y.val) ^ k = (y⁻¹).val * A ^ k * y.val := fun k => by
    simpa using Units.conj_pow y⁻¹ A k
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    simp only [aeval_monomial, hpow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul]

theorem aeval_diagonal (lam : Fin n → ℂ) (q : ℂ[X]) :
    aeval (diagonal lam) q = diagonal fun j => q.eval (lam j) := by
  have h : diagonal lam = Matrix.diagonalAlgHom ℂ lam := rfl
  rw [h, aeval_algHom_apply]
  have h2 : aeval lam q = fun j => q.eval (lam j) := by
    funext j
    have := aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : Fin n => ℂ) j) lam q
    simpa using this.symm
  rw [h2]
  rfl

theorem isCompact_entryBall (n : ℕ) (B : ℝ) :
    IsCompact {k : GL (Fin n) ℂ | (∀ i j, ‖k.val i j‖ ≤ B) ∧ ∀ i j, ‖(k⁻¹).val i j‖ ≤ B} := by
  set S : Set (Matrix (Fin n) (Fin n) ℂ) := {M | ∀ i j, ‖M i j‖ ≤ B} with hS
  have hSc : IsCompact S := by
    have : S = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) B := by
      ext M
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) ℂ)).isCompact_preimage
    (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))
  exact h

theorem diag_proper (lam : Fin n → ℂ) (hl : Function.Injective lam)
    (C : Set (Matrix (Fin n) (Fin n) ℂ)) (hC : IsCompact C) :
    ∃ K : Set (GL (Fin n) ℂ), IsCompact K ∧ ∀ y : GL (Fin n) ℂ,
      (y⁻¹).val * diagonal lam * y.val ∈ C →
      ∃ (t k : GL (Fin n) ℂ) (s : Fin n → ℂ), k ∈ K ∧ y = t * k ∧ t.val = diagonal s := by
  classical
  let p : Fin n → ℂ[X] := fun i => Lagrange.basis Finset.univ lam i
  have hp : ∀ i j, (p i).eval (lam j) = if j = i then 1 else 0 := by
    intro i j
    split_ifs with h
    · subst h; exact Lagrange.eval_basis_self hl.injOn (Finset.mem_univ _)
    · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)
  let G : Matrix (Fin n) (Fin n) ℂ → Fin n → Fin n → Fin n → ℂ := fun g i a b => aeval g (p i) a b
  have hG : Continuous G := by
    refine continuous_pi fun i => continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_id.matrix_elem a b).comp (Polynomial.continuous_aeval (p i))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨_, isCompact_entryBall n (max B 1), fun y hy => ?_⟩
  have hE : ∀ i a b, ‖(y⁻¹).val a i * y.val i b‖ ≤ B := by
    intro i a b
    have h1 : aeval ((y⁻¹).val * diagonal lam * y.val) (p i) =
        (y⁻¹).val * diagonal (fun j => (p i).eval (lam j)) * y.val := by
      rw [aeval_conj_units, aeval_diagonal]
    have h2 : G ((y⁻¹).val * diagonal lam * y.val) i a b = (y⁻¹).val a i * y.val i b := by
      simp only [G, h1, hp]
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← h2]
    exact ((norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans (norm_le_pi_norm _ i))).trans (hB _ hy)

  have hrow : ∀ i, ∃ j, ∀ j', ‖y.val i j'‖ ≤ ‖y.val i j‖ := fun i => by
    haveI : Nonempty (Fin n) := ⟨i⟩
    exact Finite.exists_max _
  choose c hc using hrow
  have hne : ∀ i, y.val i (c i) ≠ 0 := by
    intro i h0
    have h1 : (y.val * (y⁻¹).val) i i = 1 := by
      rw [← Units.val_mul]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro j _
      have : y.val i j = 0 := by
        have := hc i j
        rw [h0, norm_zero] at this
        exact norm_le_zero_iff.1 this
      rw [this, zero_mul]
  let s : Fin n → ℂ := fun i => y.val i (c i)
  let t : GL (Fin n) ℂ := ⟨diagonal s, diagonal fun i => (s i)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal]; simp [s, hne], by rw [Matrix.diagonal_mul_diagonal]; simp [s, hne]⟩
  refine ⟨t, t⁻¹ * y, s, ⟨?_, ?_⟩, by group, rfl⟩
  · intro i j
    have htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹ := rfl
    have h1 : (t⁻¹ * y).val i j = (s i)⁻¹ * y.val i j := by
      rw [Units.val_mul, htinv, Matrix.diagonal_mul]
    rw [h1, norm_mul, norm_inv]
    refine le_trans ?_ (le_max_right _ _)
    exact (inv_mul_le_one₀ (norm_pos_iff.2 (hne i))).2 (hc i j)
  · intro a i
    have h1 : ((t⁻¹ * y)⁻¹).val a i = (y⁻¹).val a i * y.val i (c i) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
      change ((y⁻¹).val * diagonal s) a i = _
      rw [Matrix.mul_diagonal]
    rw [h1]
    exact (hE i a (c i)).trans (le_max_left _ _)

def phiU (n : ℕ) : GL (Fin n) ℂ :=
  ⟨GlobalTheory.Tw.Phi n ℂ, (GlobalTheory.Tw.Phi n ℂ)ᵀ, GlobalTheory.Tw.Model.Phi_mul_transpose, GlobalTheory.Tw.Model.transpose_mul_Phi⟩

theorem conjT_eq (g : GL (Fin n) ℂ) : (g.val)ᴴ = (thetaR (starRingEnd ℂ) n g⁻¹).val := by
  rw [thetaR_val, inv_inv]
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem theta_val (g : GL (Fin n) ℂ) :
    GlobalTheory.Tw.theta g.val = (phiU n * thetaR (starRingEnd ℂ) n g * (phiU n)⁻¹).val := by
  rw [GlobalTheory.Tw.theta, ← Matrix.coe_units_inv, conjT_eq, inv_inv]
  rfl

theorem theta_phiU : thetaR (starRingEnd ℂ) n (phiU n) = phiU n := by
  apply Units.ext
  rw [thetaR_val]
  change (((GlobalTheory.Tw.Phi n ℂ)ᵀ).map (starRingEnd ℂ))ᵀ = GlobalTheory.Tw.Phi n ℂ
  have h := GlobalTheory.Tw.Model.Phi_conjTranspose (n := n) (R := ℂ)
  have h2 : ((GlobalTheory.Tw.Phi n ℂ)ᵀ).map (starRingEnd ℂ) = (GlobalTheory.Tw.Phi n ℂ)ᵀ := h
  rw [h2, Matrix.transpose_transpose]

theorem phi_sq : ((phiU n)⁻¹ * (phiU n)⁻¹).val = ((-1 : ℂ) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  change (GlobalTheory.Tw.Phi n ℂ)ᵀ * (GlobalTheory.Tw.Phi n ℂ)ᵀ = _
  nth_rewrite 2 [GlobalTheory.Tw.Model.Phi_transpose]
  rw [Matrix.mul_smul, GlobalTheory.Tw.Model.transpose_mul_Phi]

theorem nrm_eq (d : GL (Fin n) ℂ) :
    GlobalTheory.Tw.nrm (d * (phiU n)⁻¹).val = ((-1 : ℂ) ^ (n - 1)) • (d * thetaR (starRingEnd ℂ) n d).val := by
  rw [GlobalTheory.Tw.nrm, theta_val, ← Units.val_mul]
  have : d * (phiU n)⁻¹ * (phiU n * thetaR (starRingEnd ℂ) n (d * (phiU n)⁻¹) * (phiU n)⁻¹) =
      (d * thetaR (starRingEnd ℂ) n d) * ((phiU n)⁻¹ * (phiU n)⁻¹) := by
    simp only [map_mul, map_inv, theta_phiU]
    group
  rw [this, Units.val_mul, phi_sq, Matrix.mul_smul, Matrix.mul_one]

theorem adj_eq (d z : GL (Fin n) ℂ) :
    GlobalTheory.Tw.adj (d * (phiU n)⁻¹).val z.val = (d * (thetaR (starRingEnd ℂ) n z)⁻¹ * d⁻¹).val := by
  have : d * (thetaR (starRingEnd ℂ) n z)⁻¹ * d⁻¹ =
      d * (phiU n)⁻¹ * phiU n * thetaR (starRingEnd ℂ) n z⁻¹ * (phiU n)⁻¹ * (d * (phiU n)⁻¹)⁻¹ := by
    simp only [map_inv]
    group
  rw [this, GlobalTheory.Tw.adj, conjT_eq, ← Matrix.coe_units_inv]
  rfl

theorem norm_proper (d : GL (Fin n) ℂ) (hd : (d * thetaR (starRingEnd ℂ) n d).val.charpoly.Separable)
    (C : Set (GL (Fin n) ℂ)) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin n) ℂ), IsCompact D ∧ ∀ z : GL (Fin n) ℂ,
      z * (d * thetaR (starRingEnd ℂ) n d) = (d * thetaR (starRingEnd ℂ) n d) * z →
      twConj (thetaR (starRingEnd ℂ) n) z d ∈ C →
      ∃ t ∈ twCent (thetaR (starRingEnd ℂ) n) d, ∃ e ∈ D, z = t * e := by
  set δ : GL (Fin n) ℂ := d * (phiU n)⁻¹ with hδ
  have hε : ((-1 : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hReg : GlobalTheory.Tw.Reg δ.val :=
    ⟨δ.isUnit, by rw [nrm_eq]; exact Formalism.RepresentationBoundsCohomology.ringDataObjects.charpoly_smul_sep _ _ hε hd⟩
  have TC := GlobalTheory.Tw.twisted_centraliser n ℂ δ.val hReg
  set C' : Set (GL (Fin n) ℂ) := (fun c : GL (Fin n) ℂ => d * c⁻¹) '' C
  have hC' : IsCompact C' := hC.image (continuous_const.mul continuous_inv)
  obtain ⟨D, hD, hDp⟩ := GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact ℂ (fun x => norm_star x) n δ.val hReg C' hC'
  refine ⟨D, hD, fun z hz hzC => ?_⟩
  have hzv : z.val * GlobalTheory.Tw.nrm δ.val = GlobalTheory.Tw.nrm δ.val * z.val := by
    have h1 : z.val * (d * thetaR (starRingEnd ℂ) n d).val = (d * thetaR (starRingEnd ℂ) n d).val * z.val := by
      rw [← Units.val_mul, hz, Units.val_mul]
    rw [nrm_eq, Matrix.mul_smul, Matrix.smul_mul, h1]
  have hzA : z.val ∈ Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val} := (TC.2.2.2.2.1 z.val).1 hzv
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val}, z.val * x = x * z.val := by
    intro x hx
    have hle : Algebra.adjoin ℂ {GlobalTheory.Tw.nrm δ.val} ≤ Subalgebra.centralizer ℂ {z.val} := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hzv
    exact hle hx z.val (Set.mem_singleton _)
  have hu : (d * (twConj (thetaR (starRingEnd ℂ) n) z d)⁻¹).val = z.val * GlobalTheory.Tw.adj δ.val z.val := by
    rw [hcomm _ (TC.2.2.2.1 _ hzA).1, adj_eq, ← Units.val_mul]
    simp only [twConj]
    congr 1
    group
  obtain ⟨t, htA, ht1, e, he, rfl⟩ := hDp z hzA _ ⟨_, hzC, rfl⟩ hu
  refine ⟨t, ?_, e, he, rfl⟩
  have htc : t.val ∈ GlobalTheory.Tw.cent δ.val := by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩
  have h2 : t * δ = δ * (phiU n * thetaR (starRingEnd ℂ) n t * (phiU n)⁻¹) :=
    Units.ext (by rw [Units.val_mul t δ, Units.val_mul δ, ← theta_val]; exact htc.2)
  change t⁻¹ * d * thetaR (starRingEnd ℂ) n t = d
  have h3 : t * d = d * thetaR (starRingEnd ℂ) n t := by
    have : t * d * (phiU n)⁻¹ = d * thetaR (starRingEnd ℂ) n t * (phiU n)⁻¹ := by
      rw [mul_assoc t, ← hδ, h2, hδ]; group
    exact mul_right_cancel this
  rw [mul_assoc, ← h3]; group

theorem main : PositivityTheory.Rg.BcB.D4.LocProper := by
  intro n d hd C hC
  have hcont : Continuous (thetaR (starRingEnd ℂ) n) := GlobalTheory.CompanionTheory.LocVan.continuous_thC
  have hinv : ∀ g : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g :=
    fun g => GlobalTheory.CompanionTheory.FlagCent.thetaR_thetaR (starRingEnd ℂ) (fun x => Complex.conj_conj x) g
  obtain ⟨P, lam, hl, hP⟩ := exists_diag _ hd

  set C₂ : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun c : GL (Fin n) ℂ => (c * thetaR (starRingEnd ℂ) n c).val) '' C with hC₂
  have hC₂c : IsCompact C₂ := hC.image (Units.continuous_val.comp (continuous_id.mul hcont))
  obtain ⟨K, hK, hKp⟩ := diag_proper lam hl C₂ hC₂c
  set K' : Set (GL (Fin n) ℂ) := (fun k => P * k) '' K with hK'
  have hK'c : IsCompact K' := hK.image (continuous_const.mul continuous_id)
  set C₃ : Set (GL (Fin n) ℂ) :=
    (fun p : GL (Fin n) ℂ × GL (Fin n) ℂ => p.1 * p.2 * (thetaR (starRingEnd ℂ) n p.1)⁻¹) '' (K' ×ˢ C) with hC₃
  have hC₃c : IsCompact C₃ := (hK'c.prod hC).image
    ((continuous_fst.mul continuous_snd).mul (hcont.comp continuous_fst).inv)
  obtain ⟨D, hD, hDp⟩ := norm_proper d hd C₃ hC₃c
  refine ⟨D * K', hD.mul hK'c, ?_⟩
  intro x hx
  have hx' : twConj (thetaR (starRingEnd ℂ) n) x d ∈ C := hx

  have hnorm : ((P⁻¹ * x)⁻¹).val * diagonal lam * (P⁻¹ * x).val ∈ C₂ := by
    refine ⟨_, hx', ?_⟩
    have e : twConj (thetaR (starRingEnd ℂ) n) x d * thetaR (starRingEnd ℂ) n (twConj (thetaR (starRingEnd ℂ) n) x d)
        = x⁻¹ * (d * thetaR (starRingEnd ℂ) n d) * x := by
      simp only [twConj, map_mul, map_inv, hinv]
      group
    show (_ : GL (Fin n) ℂ).val = _
    rw [e, Units.val_mul, Units.val_mul, hP]
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨t, k, s, hk, hy, ht⟩ := hKp _ hnorm
  have hx2 : x = (P * t * P⁻¹) * (P * k) := by
    have : x = P * (t * k) := by rw [← hy]; group
    rw [this]; group
  set z := P * t * P⁻¹ with hz
  have hcomm : z * (d * thetaR (starRingEnd ℂ) n d) = (d * thetaR (starRingEnd ℂ) n d) * z := by
    apply Units.ext
    rw [Units.val_mul z, Units.val_mul _ z, hP, hz]
    simp only [Units.val_mul]
    have hPP : (P⁻¹).val * P.val = 1 := by rw [← Units.val_mul]; simp
    have hdt : t.val * diagonal lam = diagonal lam * t.val := by
      rw [ht, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; ext i; ring
    calc P.val * t.val * (P⁻¹).val * (P.val * diagonal lam * (P⁻¹).val)
        = P.val * t.val * ((P⁻¹).val * P.val) * diagonal lam * (P⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = P.val * (t.val * diagonal lam) * (P⁻¹).val := by rw [hPP]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = P.val * (diagonal lam * t.val) * (P⁻¹).val := by rw [hdt]
      _ = P.val * diagonal lam * ((P⁻¹).val * P.val) * t.val * (P⁻¹).val := by
          rw [hPP]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hzC : twConj (thetaR (starRingEnd ℂ) n) z d ∈ C₃ := by
    refine ⟨(P * k, twConj (thetaR (starRingEnd ℂ) n) x d), ⟨⟨k, hk, rfl⟩, hx'⟩, ?_⟩
    show (P * k) * twConj (thetaR (starRingEnd ℂ) n) x d * (thetaR (starRingEnd ℂ) n (P * k))⁻¹ = _
    rw [hx2]
    simp only [twConj, map_mul, map_inv]
    group
  obtain ⟨u, hu, e, he, hze⟩ := hDp z hcomm hzC
  refine ⟨u, hu, e * (P * k), Set.mul_mem_mul he ⟨k, hk, rfl⟩, ?_⟩
  show u * (e * (P * k)) = x
  rw [hx2, hze, mul_assoc]

end PositivityTheory.Rg.BcB.CV.LocP

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.QuotVanishL
open MeasureTheory

namespace PositivityTheory.Rg.BcB.CV

theorem quotVanishL : GlobalTheory.CompanionTheory.LocVan.QuotVanish := by
  intro n _ _ μ _ d μd _ W₁ W₂ hs _ hW h1 h2 F hF hT hK h0
  letI : MeasurableSpace (nilrad W₁ W₂) := borel _
  haveI : BorelSpace (nilrad W₁ W₂) := ⟨rfl⟩
  haveI : LocallyCompactSpace (nilrad W₁ W₂) := (nilrad W₁ W₂).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine GlobalTheory.CompanionTheory.QuotVan.quotVanish n μ d μd W₁ W₂ hW Measure.addHaar F hs h1 h2 hF hT hK fun q _ => ?_
  simp only [GlobalTheory.CompanionTheory.QuotVan.uOf_eq]
  exact h0 _ q

theorem locVanish : LocVanish := GlobalTheory.CompanionTheory.LocVan.locVanish_of GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag quotVanishL

end PositivityTheory.Rg.BcB.CV
end

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 GlobalTheory.CompanionTheory

theorem classVanish : ClassVanish :=
  classVanish_of_steps QuotNorm.integral_normaliser_eq (QuotProduct.quotProd_of_normEq QuotNorm.integral_normaliser_eq) chainSum
    RatDisc.ratDisc locVanish LocP.main LocFlagPf.locFlag degBdd KerTwFin.kerFin mahler SplitInf.splitAt NonEll.nonEllFlag
    SplitTwo.splitAt2 PairParam.pairParam (TorusCh.torusChar degAdelic)
    (ChiGamGlobal.chiGam_of onlyIsotropic (PosYGlobal.posY_of degSubmod degPairing) chainSum)
    (QuotStageInt.quotStage_of QuotNorm.integral_normaliser_eq) sizeBasic

theorem unfold : Unfold := UnfoldCut.unfold_of_mahler mahler

end PositivityTheory.Rg.BcB.CV
end

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.D4

theorem classVanish2 : ClassVanish2 := classVanish2_of (GlobalTheory.CompanionTheory.SliceFubini.sliceTerm_of mahler) classVanish sizeBasic

theorem ellFormula2J : EllFormula2J := ellFormula2_of (GlobalTheory.CompanionTheory.TwUnfold.unfold2_of mahler) ellTerm classVanish2 sizeBasic

end PositivityTheory.Rg.BcB.CV
