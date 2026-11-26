module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PResClosed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PDenseGen

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycRes
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma finsum_fib {A P : Type*} [Finite A] (f : A → P) (S : Set P) (g : P → ℤ)
    (hg : ∀ z ∈ S, g z = (Nat.card {a // f a = z} : ℤ)) :
    ∑ᶠ z ∈ S, g z = (Nat.card {a // f a ∈ S} : ℤ) := by
  classical
  haveI := Fintype.ofFinite A
  have h1 : ∑ᶠ z ∈ S, g z = ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) :=
    finsum_mem_congr rfl hg
  set s : Finset A := Finset.univ.filter fun a => f a ∈ S with hs
  have h2 : ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) =
      ∑ z ∈ s.image f, (Nat.card {a // f a = z} : ℤ) := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext z
    simp only [Set.mem_inter_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe, hs,
      Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_support, ne_eq]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨?_, h⟩
      have : Nonempty {a // f a = z} := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        exact h (by simp)
      obtain ⟨⟨a, rfl⟩⟩ := this
      exact ⟨a, hz, rfl⟩
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨ha, h⟩
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hs,
    Finset.card_eq_sum_card_image f s, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext a
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.1 hz
    refine ⟨?_, rfl⟩
    rw [← hbz]
    exact (Finset.mem_filter.1 hb).2
  · exact fun h => h.2

private lemma co_eq (q : ℕ) {n : ℕ} (j : Fin (n + 1)) :
    co q j = (crystallineComparison.wEv q j : ℤ) - (crystallineComparison.wOd q j : ℤ) := by
  unfold co crystallineComparison.wEv crystallineComparison.wOd
  by_cases h : Even (j : ℕ)
  · simp [h, h.neg_one_pow]
  · have h' : Odd (j : ℕ) := Nat.not_even_iff_odd.1 h
    simp [h, h'.neg_one_pow]

theorem UpperTheory.Gal.Mod.cycRes :
    WtVal → CycRes := by
  intro hW p q n Y π T w hOne hPt V _ _ _ _ _ hp y hgen φ hφ y₀
  classical
  have hv := fun j => hW p Y (T j) (w j) (hOne j) V hp y
  haveI : ∀ j, Finite ((T j).Sec y) := fun j => (hv j).1
  letI : ∀ j, Fintype ((T j).Sec y) := fun j => Fintype.ofFinite _
  have hA := hPt V hp y hgen φ hφ (fun j => (T j).Sec y) (fun j => id)
    (fun j => Function.bijective_id)
  have hc := congrArg (Multiset.count y₀) hA
  simp only [crystallineComparison.pts, Multiset.count_sum', Multiset.count_nsmul, id] at hc
  have key : ∀ j : Fin (n + 1),
      ∑ᶠ z ∈ {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀}, w j _ z =
      (Multiset.count y₀ (Finset.univ.val.map fun i : (T j).Sec y =>
        (twist φ Y)^[n - j] (resPt V ≫ i.1 ≫ (T j).r)) : ℤ) := by
    intro j
    rw [finsum_fib (fun i : (T j).Sec y => resPt V ≫ i.1)
      {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀} (w j _)
      (fun z hz => (hv j).2 z hz.1)]
    congr 1
    rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val]
    refine congrArg Multiset.card (Multiset.filter_congr fun i _ => ?_)
    have h1 : (resPt V ≫ i.1) ≫ (T j).p = resPt V ≫ y := by
      rw [Category.assoc, i.2]
    simp only [Set.mem_setOf_eq, h1, true_and, Category.assoc]
    exact eq_comm
  simp only [key, co_eq, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact_mod_cast hc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PClopenAt
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma clopen_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClopen (X.basicOpen e : Set X) := by
  have hsum : X.basicOpen e ⊔ X.basicOpen (1 - e) = ⊤ := by
    apply le_antisymm le_top
    have h := X.basicOpen_add_le e (1 - e)
    rwa [add_sub_cancel, Scheme.basicOpen_one] at h
  have hprod : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, Scheme.basicOpen_zero]
  have hc : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro hx hx'
      have hin : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hx'⟩
      rw [hprod] at hin
      simpa using hin
    · intro hx
      have hin : x ∈ X.basicOpen e ⊔ X.basicOpen (1 - e) := by
        rw [hsum]
        trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hin with h | h
      · exact h
      · exact absurd h hx
  refine ⟨?_, (X.basicOpen e).isOpen⟩
  rw [hc]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

private noncomputable def rho {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) : Γ(W, ⊤) →+* κ :=
  (z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom

private lemma mem_basicOpen_iff {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) (e : Γ(W, ⊤)) :
    pt z ∈ W.basicOpen e ↔ rho z e ≠ 0 := by
  have h1 : pt z ∈ W.basicOpen e ↔ IsLocalRing.closedPoint κ ∈ (gp κ).basicOpen (z.appTop e) := by
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  rw [h1, basicOpen_eq_of_affine']
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  change _ ∉ IsLocalRing.maximalIdeal κ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]
  rfl

private lemma rho_inj {κ : Type} [Field κ] {W : Scheme.{0}} [IsAffine W] {z z' : gp κ ⟶ W}
    (h : rho z = rho z') : z = z' := by
  apply ext_of_isAffine
  have : z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom = z'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom :=
    CommRingCat.hom_ext h
  exact (cancel_mono _).mp this

private lemma rho_comp (V : Type) [CommRing V] [IsLocalRing V] {W : Scheme.{0}}
    (g : W ⟶ Spec (CommRingCat.of V)) (z : gp (IsLocalRing.ResidueField V) ⟶ W) (hz : z ≫ g = resPt V) :
    (rho z).comp ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom = IsLocalRing.residue V := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (z ≫ g).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField V))).hom =
      CommRingCat.ofHom (IsLocalRing.residue V) := by
    rw [hz, resPt, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h2 := congrArg CommRingCat.Hom.hom key
  exact h2

theorem UpperTheory.Gal.Mod.clopenAt :
    ResClosed → HensSplit → ClopenAt := by
  intro _ hHS V _ _ _ _ W g _ z₀ hz₀
  haveI : IsAffine W := isAffine_of_isAffineHom g
  set φ : V →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom with hφ
  have hfin : φ.Finite := by
    have h1 := g.finite_appTop
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (fun a => ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom a, by simp⟩)
    exact h1.comp h2
  letI : Algebra V Γ(W, ⊤) := φ.toAlgebra
  haveI : Module.Finite V Γ(W, ⊤) := hfin
  have hc : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      ∀ v : V, rho z (φ v) = IsLocalRing.residue V v := by
    intro z hz v
    exact RingHom.congr_fun (rho_comp V g z hz) v
  have hsurj : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      Function.Surjective (rho z) := by
    intro z hz r
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective r
    exact ⟨φ v, by rw [hc z hz v, hv]⟩
  have hmax : (RingHom.ker (rho z₀)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (hsurj z₀ hz₀)
  obtain ⟨e, he, hem, hoth⟩ := hHS V Γ(W, ⊤) (RingHom.ker (rho z₀)) hmax
  refine ⟨W.basicOpen e, clopen_basicOpen he, ?_⟩
  intro z hz
  rw [SetLike.mem_coe, mem_basicOpen_iff]
  constructor
  · intro hne
    have hk : RingHom.ker (rho z) = RingHom.ker (rho z₀) := by
      by_contra hk
      exact hne (RingHom.mem_ker.mp
        (hoth _ (RingHom.ker_isMaximal_of_surjective _ (hsurj z hz)) hk))
    apply rho_inj
    ext a
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective (rho z₀ a)
    have hmem : a - φ v ∈ RingHom.ker (rho z₀) := by
      rw [RingHom.mem_ker, map_sub, hc z₀ hz₀ v, hv, sub_self]
    rw [← hk, RingHom.mem_ker, map_sub, sub_eq_zero, hc z hz v, hv] at hmem
    exact hmem
  · rintro rfl
    exact fun h => hem (RingHom.mem_ker.mpr h)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHensSplit
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem split_monic (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [IsAlgClosed (FractionRing V)] :
    ∀ (n : ℕ) (F : Polynomial V), F.Monic → F.natDegree = n →
      ∃ s : Multiset V, F = (s.map fun α => Polynomial.X - Polynomial.C α).prod := by
  intro n
  induction n with
  | zero =>
    intro F hF hdeg
    refine ⟨0, ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact Polynomial.eq_one_of_monic_natDegree_zero hF hdeg
  | succ n ih =>
    intro F hF hdeg
    have hm : (F.map (algebraMap V (FractionRing V))).Monic := hF.map _
    have hnd : (F.map (algebraMap V (FractionRing V))).natDegree = n + 1 := by
      rw [hF.natDegree_map, hdeg]
    have hd0 : (F.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
      intro h
      rw [Polynomial.degree_eq_natDegree hm.ne_zero, hnd] at h
      norm_cast at h
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd0
    have hint : IsIntegral V x := ⟨F, hF, by rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx⟩
    obtain ⟨α, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hroot : F.IsRoot α := by
      apply IsFractionRing.injective V (FractionRing V)
      rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hx
      rw [hx, map_zero]
    have hmul : (Polynomial.X - Polynomial.C α) * (F /ₘ (Polynomial.X - Polynomial.C α)) = F :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hGm : (F /ₘ (Polynomial.X - Polynomial.C α)).Monic :=
      Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C α) (by rw [hmul]; exact hF)
    have hGd : (F /ₘ (Polynomial.X - Polynomial.C α)).natDegree = n := by
      rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C α), hdeg,
        Polynomial.natDegree_X_sub_C]
      omega
    obtain ⟨s, hs⟩ := ih _ hGm hGd
    refine ⟨α ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

private theorem coprime_left {R ι : Type} [CommRing R] (s : Multiset ι) (f : ι → R) (x : R)
    (h : ∀ a ∈ s, IsCoprime (f a) x) : IsCoprime (s.map f).prod x := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact isCoprime_one_left
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a t)).mul_left (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

private theorem prod_notMem {R ι : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (s : Multiset ι) (f : ι → R) (h : ∀ a ∈ s, f a ∉ P) : (s.map f).prod ∉ P := by
  induction s using Multiset.induction_on with
  | empty =>
    intro h1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using h1))
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    intro hm
    rcases hP.mem_or_mem hm with h1 | h1
    · exact h a (Multiset.mem_cons_self a t) h1
    · exact ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)) h1

private theorem algebraMap_mem_maximal_of_mem_maximalIdeal (V : Type) [CommRing V] [IsLocalRing V] {A : Type} [CommRing A]
    [Algebra V A] [Algebra.IsIntegral V A] (m' : Ideal A) [m'.IsMaximal] {v : V}
    (hv : v ∈ IsLocalRing.maximalIdeal V) : algebraMap V A v ∈ m' := by
  have hc : (m'.comap (algebraMap V A)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V) m'
  rw [← IsLocalRing.eq_maximalIdeal hc] at hv
  exact hv

private theorem exists_idempotent_approx_at_maximal (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [IsAlgClosed (FractionRing V)] {A : Type} [CommRing A] [Algebra V A] [Algebra.IsIntegral V A]
    (m : Ideal A) [hm : m.IsMaximal] (a : A) :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ m ∧ ∀ m' : Ideal A, m'.IsMaximal → e ∉ m' →
      ∃ β : V, a - algebraMap V A β ∈ m ∧ a - algebraMap V A β ∈ m' := by
  classical
  obtain ⟨F, hF, hFa⟩ := Algebra.IsIntegral.isIntegral (R := V) a
  obtain ⟨s, hs⟩ := split_monic V F.natDegree F hF rfl
  set f : V → A := fun α => a - algebraMap V A α with hf
  have hprod : (s.map f).prod = 0 := by
    have h0 : Polynomial.aeval a F = 0 := by
      rw [Polynomial.aeval_def]
      exact hFa
    rw [hs, map_multiset_prod, Multiset.map_map] at h0
    simpa [f, Function.comp_def] using h0
  set g := ((s.filter (fun α => f α ∈ m)).map f).prod with hg
  set h := ((s.filter (fun α => ¬ f α ∈ m)).map f).prod with hh
  have hgh : g * h = 0 := by
    rw [hg, hh, ← Multiset.prod_add, ← Multiset.map_add (f := _), Multiset.filter_add_not, hprod]
  have hhm : h ∉ m := prod_notMem m _ f (fun α hα => (Multiset.mem_filter.mp hα).2)
  have hgm : g ∈ m := by
    have hz : g * h ∈ m := by
      rw [hgh]
      exact m.zero_mem
    exact (hm.isPrime.mem_or_mem hz).resolve_right hhm
  have hcop : IsCoprime g h := by
    apply IsCoprime.symm
    apply coprime_left
    intro β hβ
    apply IsCoprime.symm
    apply coprime_left
    intro α hα
    have hPα : f α ∈ m := (Multiset.mem_filter.mp hα).2
    have hPβ : f β ∉ m := (Multiset.mem_filter.mp hβ).2
    have hu : IsUnit (α - β) := by
      by_contra hnu
      apply hPβ
      have hmem : algebraMap V A (α - β) ∈ m :=
        algebraMap_mem_maximal_of_mem_maximalIdeal V m ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      have hfe : f β = f α + algebraMap V A (α - β) := by
        simp only [f, map_sub]
        ring
      rw [hfe]
      exact m.add_mem hPα hmem
    obtain ⟨w, hw⟩ := hu
    refine ⟨-algebraMap V A (↑w⁻¹ : V), algebraMap V A (↑w⁻¹ : V), ?_⟩
    have hw1 : algebraMap V A (↑w⁻¹ : V) * algebraMap V A (α - β) = 1 := by
      rw [← map_mul, ← hw, Units.inv_mul, map_one]
    simp only [f, map_sub] at hw1 ⊢
    linear_combination hw1
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨v * h, ?_, ?_, ?_⟩
  · show v * h * (v * h) = v * h
    linear_combination (v * h) * huv - (u * v) * hgh
  · intro he
    apply hm.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    exact m.add_mem (m.mul_mem_left u hgm) he
  · intro m' hm' he
    have hhm' : h ∉ m' := fun hh' => he (m'.mul_mem_left v hh')
    have hex : ∃ α ∈ s, f α ∈ m' := by
      by_contra hne
      push_neg at hne
      have hn := prod_notMem (hP := hm'.isPrime) m' s f hne
      rw [hprod] at hn
      exact hn m'.zero_mem
    obtain ⟨α, hαs, hαm'⟩ := hex
    by_cases hPα : f α ∈ m
    · exact ⟨α, hPα, hαm'⟩
    · exfalso
      apply hhm'
      have hmemf : α ∈ s.filter (fun α => ¬ f α ∈ m) := Multiset.mem_filter.mpr ⟨hαs, hPα⟩
      obtain ⟨c, hc⟩ := Multiset.dvd_prod (Multiset.mem_map_of_mem f hmemf)
      rw [hh, hc]
      exact m'.mul_mem_right c hαm'

theorem UpperTheory.Gal.Mod.hensSplit :
    HensSplit := by
  intro V _ _ _ _ A _ _ _ m hm
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := V) (M := A)
  choose E hEi hEm hEm' using fun t : A => exists_idempotent_approx_at_maximal V m t
  refine ⟨∏ t ∈ T, E t, ?_, ?_, ?_⟩
  · show (∏ t ∈ T, E t) * (∏ t ∈ T, E t) = ∏ t ∈ T, E t
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun t _ => (hEi t).eq)
  · rw [Finset.prod_eq_multiset_prod]
    exact prod_notMem m T.val E (fun t _ => hEm t)
  · intro m' hm' hne
    by_contra hem'
    have hall : ∀ t ∈ T, ∃ β : V, t - algebraMap V A β ∈ m ⊓ m' := by
      intro t ht
      have hEt : E t ∉ m' := by
        intro hE
        apply hem'
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem E ht
        rw [hc]
        exact m'.mul_mem_right c hE
      obtain ⟨β, h1, h2⟩ := hEm' t m' hm' hEt
      exact ⟨β, Ideal.mem_inf.mpr ⟨h1, h2⟩⟩
    have hspan : ∀ x : A, ∃ β : V, x - algebraMap V A β ∈ m ⊓ m' := by
      intro x
      have hx : x ∈ Submodule.span V (T : Set A) := by
        rw [hT]
        trivial
      induction hx using Submodule.span_induction with
      | mem y hy => exact hall y hy
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨β, hβ⟩ := hy
        obtain ⟨γ, hγ⟩ := hz
        refine ⟨β + γ, ?_⟩
        have hyz : y + z - algebraMap V A (β + γ) =
            (y - algebraMap V A β) + (z - algebraMap V A γ) := by
          rw [map_add (f := _)]
          ring
        rw [hyz]
        exact (m ⊓ m').add_mem hβ hγ
      | smul c y _ hy =>
        obtain ⟨β, hβ⟩ := hy
        refine ⟨c * β, ?_⟩
        have hcy : c • y - algebraMap V A (c * β) = algebraMap V A c * (y - algebraMap V A β) := by
          rw [Algebra.smul_def, map_mul]
          ring
        rw [hcy]
        exact (m ⊓ m').mul_mem_left _ hβ
    have hle : m ≤ m' := by
      intro x hx
      obtain ⟨β, hβ⟩ := hspan x
      have hβ1 := (Ideal.mem_inf.mp hβ).1
      have hβ2 := (Ideal.mem_inf.mp hβ).2
      have hβm : algebraMap V A β ∈ m := by
        have hd := m.sub_mem hx hβ1
        simpa using hd
      have hβmax : β ∈ IsLocalRing.maximalIdeal V := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hβm (hu.map _))
      have hs := m'.add_mem hβ2 (algebraMap_mem_maximal_of_mem_maximalIdeal V m' hβmax)
      simpa using hs
    exact hne (hm.eq_of_le hm'.ne_top hle).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSecGen
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.secGen :
    SecGen := by
  intro Z Y g _ V _ _ _ y
  have hP : IsProper g := inferInstance
  have hV : ValuativeCriterion g := by
    rw [IsProper.eq_valuativeCriterion] at hP
    exact hP.1.1.1
  let e : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    show (e ≫ z) ≫ g = e ≫ y
    rw [Category.assoc, show z ≫ g = y from hz]
  · intro z₁ hz₁ z₂ hz₂ h
    have h₁ : z₁ ≫ g = y := hz₁
    have h₂ : z₂ ≫ g = y := hz₂
    have h' : e ≫ z₁ = e ≫ z₂ := h
    let S : ValuativeCommSq g :=
      ⟨V, FractionRing V, e ≫ z₁, y, ⟨by rw [Category.assoc, h₁]⟩⟩
    have hu := ValuativeCriterion.uniqueness hV S
    have := @Subsingleton.elim _ hu
      ⟨z₁, rfl, h₁⟩ ⟨z₂, h'.symm, h₂⟩
    exact congrArg CommSq.LiftStruct.l this
  · intro x hx
    have hx' : x ≫ g = e ≫ y := hx
    let S : ValuativeCommSq g := ⟨V, FractionRing V, x, y, ⟨hx'⟩⟩
    obtain ⟨⟨l⟩⟩ := ValuativeCriterion.existence hV S
    exact ⟨l.l, l.fac_right, l.fac_left⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PNwtOne
noncomputable section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.Mod

private theorem mem_basicOpen_of_ne {p : ℕ} {Y : Scheme.{0}} (Ω : Type) [Field Ω]
    (x : gp Ω ⟶ Y) (hp : (p : Ω) ≠ 0) : pt x ∈ Y.basicOpen (p : Γ(Y, ⊤)) := by
  have hu : IsUnit ((p : ℕ) : Γ(gp Ω, ⊤)) := by
    have h1 : IsUnit ((p : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hp
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    simpa using h2
  have h3 : (gp Ω).basicOpen (x.appTop (p : Γ(Y, ⊤))) = ⊤ := by
    rw [map_natCast]
    exact Scheme.basicOpen_of_isUnit _ hu
  have h4 : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, h3]
    trivial
  exact h4

theorem nwtOne : NwtOne := by
  intro p Y T hL _
  obtain ⟨_, _, _, _, _, _, _, hMB, _, _, hWN, _, hNF, _, _⟩ := all_holds.1
  haveI := T.fin
  have hN : IsNwt T.p (nwt T.p) := hWN T.p hL
  refine ⟨hN.1, ?_⟩
  intro Ω _ _ z hp
  haveI := T.et
  have hD : Dense {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} := by
    have hs : {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} =
        {s | GenPt s} := by
      ext s
      exact genBasic_of.2.1 (Y.basicOpen (p : Γ(Y, ⊤))).ι s
    rw [hs]
    exact genBasic_of.1 _
  have hc := hNF (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤))) T.p
    (Y.basicOpen (p : Γ(Y, ⊤))).ι (isPullback_morphismRestrict T.p _).flip hN hD
  rw [hMB.2.2 (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤)))] at hc
  have hmem : pt (z ≫ T.p) ∈ Y.basicOpen (p : Γ(Y, ⊤)) := mem_basicOpen_of_ne Ω (z ≫ T.p) hp
  have hr : Set.range z ⊆ Set.range (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hq
    exact hmem
  have hz := IsOpenImmersion.lift_fac (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι z hr
  have h5 := congrArg (fun w : Wt _ => w Ω (IsOpenImmersion.lift _ z hr)) hc
  simp only [Wt.comap, hz] at h5
  rw [h5]
  rfl

end UpperTheory.Gal.Mod

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycExt
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma sp_twist {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (u : gp Ω ⟶ Y) :
    sp a ≫ twist φ Y u = twist φ' Y (sp a ≫ u) := by
  have h : sp a ≫ sp φ = sp φ' ≫ sp a := by
    simp only [UpperTheory.Gal.Mod.sp, ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  change sp a ≫ sp φ ≫ u = sp φ' ≫ sp a ≫ u
  rw [← Category.assoc, h, Category.assoc]

private lemma sp_iter {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (m : ℕ) (u : gp Ω ⟶ Y) :
    sp a ≫ (twist φ Y)^[m] u = (twist φ' Y)^[m] (sp a ≫ u) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, sp_twist a φ φ' hc]

private lemma pt_sp {Ω Ω' : Type} [Field Ω] [Field Ω'] {Z : Scheme.{0}} (a : Ω →+* Ω') (z : gp Ω ⟶ Z) :
    pt (sp a ≫ z) = pt z := by
  have h : ∀ c : gp Ω', (sp a ≫ z) c = z (sp a c) := fun c => Scheme.Hom.comp_apply _ _ _
  exact (h _).trans (congrArg (fun t : gp Ω => z t) (Subsingleton.elim (α := PrimeSpectrum Ω) _ _))

private lemma sum_eq (hF : FibExt) (hWt : TranscendenceTraces.WtPt) {p : ℕ} {Y : Scheme.{0}} (T : crystallineComparison.Corr p Y) (w : Wt T.Z)
    (hw : IsWt T.p w) (m : ℕ) {Ω Ω' : Type} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (x y : gp Ω ⟶ Y) :
    ∑ᶠ z ∈ {z : gp Ω ⟶ T.Z | z ≫ T.p = x ∧ (twist φ Y)^[m] (z ≫ T.r) = y}, w Ω z =
      ∑ᶠ z ∈ {z : gp Ω' ⟶ T.Z | z ≫ T.p = sp a ≫ x ∧ (twist φ' Y)^[m] (z ≫ T.r) = sp a ≫ y}, w Ω' z := by
  haveI : IsFinite T.p := T.fin
  obtain ⟨-, hb, hinj⟩ := hF T.p Ω Ω' a x
  refine finsum_mem_eq_of_bijOn (fun z => sp a ≫ z) ⟨?_, ?_, ?_⟩ ?_
  · rintro z ⟨h1, h2⟩
    refine ⟨by simp only [Category.assoc, h1], ?_⟩
    rw [Category.assoc, ← sp_iter a φ φ' hc, h2]
  · intro z hz z' hz' h
    exact hb.injOn (show z ∈ fib T.p x from hz.1) (show z' ∈ fib T.p x from hz'.1) h
  · rintro z' ⟨h1, h2⟩
    obtain ⟨z, hz, rfl⟩ := hb.surjOn (show z' ∈ fib T.p (sp a ≫ x) from h1)
    refine ⟨z, ⟨hz, hinj _ _ ?_⟩, rfl⟩
    rw [sp_iter a φ φ' hc, ← Category.assoc] at *
    simpa [Category.assoc] using h2
  · intro z _
    exact hWt T.p w hw Ω Ω' z (sp a ≫ z) (pt_sp a z).symm

theorem UpperTheory.Gal.Mod.cycExt :
    FibExt → CycExt := by
  intro hF p q n Y T w hw Ω Ω' _ _ _ _ a φ φ' hc x
  have hWt : TranscendenceTraces.WtPt := TranscendenceTraces.all_holds.1.2.2.2.2.1
  have hs := fun (j : Fin (n + 1)) y => sum_eq hF hWt (T j) (w j) (hw j) (n - j) a φ φ' hc x y
  constructor
  · intro h y'
    by_cases hy : ∃ y : gp Ω ⟶ Y, y' = sp a ≫ y
    · obtain ⟨y, rfl⟩ := hy
      have := h y
      simp only [hs] at this
      exact this
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : {z : gp Ω' ⟶ (T j).Z | z ≫ (T j).p = sp a ≫ x ∧ (twist φ' Y)^[n - j] (z ≫ (T j).r) = y'} = ∅ := by
        ext z'
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        haveI : IsFinite (T j).p := (T j).fin
        obtain ⟨z, -, rfl⟩ := (hF (T j).p Ω Ω' a x).2.1.surjOn (show z' ∈ fib (T j).p (sp a ≫ x) from h1)
        refine hy ⟨(twist φ Y)^[n - j] (z ≫ (T j).r), ?_⟩
        rw [sp_iter a φ φ' hc, ← h2, Category.assoc]
      rw [this]
      simp
  · intro h y
    have := h (sp a ≫ y)
    simp only [← hs] at this
    exact this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFibExt
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.Mod

private theorem pt_sp {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') {X : Scheme.{0}} (x : gp Ω ⟶ X) :
    pt (sp a ≫ x) = pt x := by
  rw [pt_comp, pt_eq]

private instance sp_flat {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') : Flat (sp a) := by
  letI := a.toAlgebra
  exact (inferInstance : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω'))))

private instance sp_surj {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') : Surjective (sp a) := by
  refine ⟨fun t => ⟨IsLocalRing.closedPoint Ω', ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum Ω) _ _

private theorem sp_epi {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') : Epi (sp a) :=
  Flat.epi_of_flat_of_surjective _

theorem fibExt : FibExt := by
  intro Z Y g _ Ω Ω' _ _ _ a x
  have hepi := sp_epi a
  have inj : ∀ {T : Scheme.{0}} (y y' : gp Ω ⟶ T), sp a ≫ y = sp a ≫ y' → y = y' :=
    fun y y' h => (cancel_epi (sp a)).1 h
  refine ⟨fibFin_of chart_of g Ω x, ⟨?_, ?_, ?_⟩, fun y y' h => inj y y' h⟩
  · intro z hz
    have hz' : z ≫ g = x := hz
    change (sp a ≫ z) ≫ g = sp a ≫ x
    rw [Category.assoc, hz']
  · intro z _ z' _ h
    exact inj z z' h
  · intro w hw
    have hw' : w ≫ g = sp a ≫ x := hw
    let z2 : gp Ω' ⟶ pullback g x := pullback.lift w (sp a) hw'
    obtain ⟨z0, h0, hpt⟩ := ptLift_of (pullback.snd g x) Ω (𝟙 (gp Ω)) (pt z2)
      (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
    have e : sp a ≫ z0 = z2 := by
      refine ptOne_of chart_of Ω (pullback.snd g x) Ω' (sp a) (sp a ≫ z0) z2 ?_ ?_ ?_
      · rw [Category.assoc, h0, Category.comp_id]
      · exact pullback.lift_snd _ _ _
      · rw [pt_sp, hpt]
    refine ⟨z0 ≫ pullback.fst g x, ?_, ?_⟩
    · change (z0 ≫ pullback.fst g x) ≫ g = x
      rw [Category.assoc, pullback.condition, ← Category.assoc, h0, Category.id_comp]
    · change sp a ≫ z0 ≫ pullback.fst g x = w
      rw [← Category.assoc, e]
      exact pullback.lift_fst _ _ _

end UpperTheory.Gal.Mod
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycAll
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma natCast_eq_zero_of_pt {p : ℕ} {Y : Scheme.{0}} {Ω : Type} [Field Ω] (x : gp Ω ⟶ Y)
    (h : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤))) : (p : Ω) = 0 := by
  by_contra hne
  apply h
  have hu : IsUnit ((ConcreteCategory.hom (Scheme.Hom.app x ⊤)) (p : Γ(Y, ⊤))) := by
    rw [map_natCast]
    have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (p : Ω) = (p : Γ(gp Ω, ⊤)) := map_natCast _ p
    have hu0 := (IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    rw [e] at hu0
    exact hu0
  have hpre := Scheme.preimage_basicOpen x (p : Γ(Y, ⊤))
  rw [Scheme.basicOpen_of_isUnit _ hu] at hpre
  have hm : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [hpre]
    trivial
  exact hm

private lemma sp_closedPoint {K L : Type} [Field K] [Field L] (a : K →+* L) :
    (sp a) (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint K := by
  exact IsLocalRing.comap_closedPoint a

private lemma resPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] :
    (resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint V := by
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

private lemma exists_frob (p f : ℕ) (hp : p.Prime) (F : Type) [Field F] (h : (p : F) = 0) :
    ∃ φ : F →+* F, ∀ a, φ a = a ^ p ^ f := by
  haveI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 h
  haveI : ExpChar F p := ExpChar.prime hp
  exact ⟨iterateFrobenius F p f, fun a => iterateFrobenius_def p f a⟩

theorem UpperTheory.Gal.Mod.cycAll :
    ResClosed → ValLift → CycRes → CycExt → CycAll := by
  intro hRC hVL hCR hCE p f n hp Y π T w hOne hPt hdense hbasic Ω _ _ x hgen
  obtain ⟨η, hη, hsp⟩ := hdense (pt x)
  obtain ⟨V, _, _, _, _, y, Ω', _, _, a, b, hpV, hsq⟩ := hVL p Y Ω x η hsp hη
  haveI := hRC V
  have hx0 : pt x ∉ Y.basicOpen (p : Γ(Y, ⊤)) := fun h => hgen.1 (hbasic _ h)
  have hptA : pt (sp a ≫ x) = pt x := by
    change x (sp a (IsLocalRing.closedPoint Ω')) = _
    rw [sp_closedPoint]
    rfl
  have hptB : pt (sp b ≫ resPt V ≫ y) = y (IsLocalRing.closedPoint V) := by
    change y (resPt V (sp b (IsLocalRing.closedPoint Ω'))) = _
    rw [sp_closedPoint, resPt_closedPoint]
  have hyx : y (IsLocalRing.closedPoint V) = pt x := by
    rw [← hptB, ← hsq, hptA]
  have hpΩ := natCast_eq_zero_of_pt x hx0
  have hpΩ' := natCast_eq_zero_of_pt (sp a ≫ x) (by rw [hptA]; exact hx0)
  have hpR := natCast_eq_zero_of_pt (resPt V ≫ y) (by
    change y (resPt V (IsLocalRing.closedPoint _)) ∉ _
    rw [resPt_closedPoint, hyx]
    exact hx0)
  obtain ⟨φ, hφ⟩ := exists_frob p f hp Ω hpΩ
  obtain ⟨φ', hφ'⟩ := exists_frob p f hp Ω' hpΩ'
  obtain ⟨ψ, hψ⟩ := exists_frob p f hp (IsLocalRing.ResidueField V) hpR
  refine ⟨φ, hφ, ?_⟩
  have hW : ∀ j, IsWt (T j).p (w j) := fun j => (hOne j).1
  have h1 := hCR p (p ^ f) n Y π T w hOne hPt V hpV y (by rw [hyx]; exact hgen) ψ hψ
  have h2 := (hCE p (p ^ f) n Y T w hW _ Ω' b ψ φ'
    (RingHom.ext fun z => by simp [hψ, hφ', map_pow]) (resPt V ≫ y)).mp h1
  rw [← hsq] at h2
  exact (hCE p (p ^ f) n Y T w hW Ω Ω' a φ φ'
    (RingHom.ext fun z => by simp [hφ, hφ', map_pow]) x).mpr h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PValLiftB
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.TranscendenceTraces (gp pt)
open UpperTheory.Gal.crystallineComparison (resPt)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem exists_common_algClosed_embedding {k A B : Type} [Field k] [Field A] [Field B] [Algebra k A]
    [Algebra k B] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (f : A →+* C) (g : B →+* C),
      f.comp (algebraMap k A) = g.comp (algebraMap k B) := by
  haveI : Nontrivial (TensorProduct k A B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k A B
      (algebraMap k B).injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct k A B)
  letI := Ideal.Quotient.field M
  let q : TensorProduct k A B →+* TensorProduct k A B ⧸ M := Ideal.Quotient.mk M
  let iA : A →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeLeft
  let iB : B →ₐ[k] TensorProduct k A B := Algebra.TensorProduct.includeRight
  refine ⟨AlgebraicClosure (TensorProduct k A B ⧸ M), inferInstance, inferInstance,
    (algebraMap _ _).comp (q.comp iA.toRingHom), (algebraMap _ _).comp (q.comp iB.toRingHom), ?_⟩
  ext c
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgHom.commutes, iA, iB]

theorem UpperTheory.Gal.Mod.valLiftB :
    ValLift := by
  intro p Y Ω _ x η hsp hp
  let O := Y.presheaf.stalk (pt x)
  let sx : O ⟶ CommRingCat.of Ω := Scheme.stalkClosedPointTo x
  haveI : IsLocalHom sx.hom := Scheme.isLocalHom_stalkClosedPointTo' x
  have hx : Spec.map sx ≫ Y.fromSpecStalk (pt x) = x :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  let K := AlgebraicClosure (Y.residueField η)
  let f : O →+* K := (algebraMap (Y.residueField η) K).comp
    ((Y.residue η).hom.comp (Y.presheaf.stalkSpecializes hsp).hom)
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let g : O →+* A := f.codRestrict A.toSubring hA
  haveI : IsLocalHom g := hloc
  haveI : IsAlgClosed (FractionRing A) :=
    IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv A K).symm.toRingEquiv
  let φ : IsLocalRing.ResidueField O →+* Ω := IsLocalRing.ResidueField.lift sx.hom
  let ψ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField A :=
    IsLocalRing.ResidueField.map g
  letI : Algebra (IsLocalRing.ResidueField O) Ω := φ.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) := ψ.toAlgebra
  obtain ⟨C, _, _, fa, fb, hab⟩ := exists_common_algClosed_embedding (k := IsLocalRing.ResidueField O) (A := Ω)
    (B := IsLocalRing.ResidueField A)
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom g) ≫ Y.fromSpecStalk (pt x), C, inferInstance, inferInstance,
    fa, fb, ?_, ?_⟩
  · intro h0
    have hu := ((Y.mem_basicOpen (p : Γ(Y, ⊤)) η trivial).mp hp).map (Y.residue η).hom
    simp only [map_natCast] at hu
    have h1 := congrArg A.subtype h0
    simp only [map_natCast, map_zero] at h1
    have h2 : (p : Y.residueField η) = 0 :=
      (algebraMap (Y.residueField η) K).injective (by rw [map_natCast, map_zero]; exact h1)
    exact hu.ne_zero h2
  · conv_lhs => rw [← hx]
    simp only [sp, resPt, ← Spec.map_comp_assoc]
    congr 2
    ext z
    have hz := congrArg (fun h => h (IsLocalRing.residue O z)) hab
    simpa [φ, ψ, RingHom.algebraMap_toAlgebra, IsLocalRing.ResidueField.map_residue] using hz
end

namespace UpperTheory.Gal.Mod

theorem wtVal_holds : WtVal := by
  exact wtVal fibExt secGen (clopenAt resClosed hensSplit)

theorem cycAll_holds : CycAll := by
  exact cycAll resClosed valLiftB (cycRes wtVal_holds) (cycExt fibExt)

theorem esPt_holds : ESPt := esPt cycAll_holds

end UpperTheory.Gal.Mod
