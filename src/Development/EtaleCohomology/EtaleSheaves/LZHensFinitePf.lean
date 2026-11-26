module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf
public import Development.EtaleCohomology.EtaleSheaves.TorEtPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LZHensFinitePf
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LZHensFinitePf

def HensIdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
  (e : B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)), IsIdempotentElem e →
  ∃ f : B, IsIdempotentElem f ∧ Ideal.Quotient.mk _ f = e

theorem hensIdemLift : HensIdemLift := by
  intro A _ _ _ B _ _ _ e he
  exact GlobalTheory.exists_idempotent_lift_of_henselian A (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective he

theorem idem_triv_of_preconnected (R : Type) [CommRing R] [PreconnectedSpace (PrimeSpectrum R)]
    (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    apply he.eq_zero_of_isNilpotent
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact SetLike.coe_injective h
  · right
    have hz : PrimeSpectrum.zeroLocus ({e} : Set R) = ∅ := by
      rw [← compl_compl (PrimeSpectrum.zeroLocus ({e} : Set R)), ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, h,
        Set.compl_univ]
    have h1 : IsNilpotent (1 - e) := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply SetLike.coe_injective
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub, sub_sub_cancel, hz]
      rfl
    exact (sub_eq_zero.mp (he.one_sub.eq_zero_of_isNilpotent h1)).symm

theorem subsingleton_of_idem (R : Type) [CommRing R] [IsArtinianRing R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (PrimeSpectrum R) := by
  have hp : PreconnectedSpace (PrimeSpectrum R) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases h e he with rfl | rfl
    · left; simp
    · right; simp
  exact ⟨fun x y => hp.constant (f := id) continuous_id⟩

theorem LZHensFinite_of_lift (hL : HensIdemLift) : LateralTheory.E.LZProperCut.LZHensFinite := by
  intro A _ _ _ B _ _ _ hB
  have : ConnectedSpace (PrimeSpectrum B) := hB
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  set I := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hI
  have hle : ∀ M : Ideal B, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    have : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  have htriv : ∀ e : B ⧸ I, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := hL A B e he
    rcases idem_triv_of_preconnected B f hf with rfl | rfl
    · left; simp
    · right; simp
  have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsArtinianRing (B ⧸ I) := IsArtinianRing.of_finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I)
  have hsub := subsingleton_of_idem (B ⧸ I) htriv
  have key : ∀ P : Ideal B, P.IsMaximal →
      P = (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) ∧ (P.map (Ideal.Quotient.mk I)).IsPrime := by
    intro P hP
    refine ⟨(Ideal.comap_map_mk (hle P hP)).symm, ?_⟩
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle P hP)
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  refine ⟨M, hM, fun N hN => ?_⟩
  obtain ⟨hN1, hN2⟩ := key N hN
  obtain ⟨hM1, hM2⟩ := key M hM
  have : (⟨_, hN2⟩ : PrimeSpectrum (B ⧸ I)) = ⟨_, hM2⟩ := Subsingleton.elim _ _
  exact hN1.trans ((congrArg (fun P : PrimeSpectrum (B ⧸ I) => P.asIdeal.comap (Ideal.Quotient.mk I)) this).trans hM1.symm)

end LateralTheory.E.LZHensFinitePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocalIntegralClosureRoots
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.LocalIntegralClosureRoots

theorem root_mem (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] (h : GlobalTheory.EtC.AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ x : K, aeval x p = 0 →
      ∃ a : A, algebraMap A K a = x := by
  intro n
  induction n with
  | zero =>
    intro p hn hp x hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hn
    subst h1
    simp at hx
  | succ n ih =>
    intro p hn hp x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdvd : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hdvd]; exact hp)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hdvd, map_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hqd hq x h1

theorem isIntegrallyClosed_of_aic (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x ⟨p, hp, hx⟩
  exact root_mem A (FractionRing A) h _ p rfl hp x (by rw [aeval_def]; exact hx)

theorem LocAIC_of : NormPf.AICPf.LocAIC := by
  intro X _ hcov
  refine ⟨inferInstance, fun V hV hVne => ?_⟩
  have : Nonempty V := hVne.to_subtype
  have hst : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hxU, hU, hA⟩ := hcov x
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have := isIntegrallyClosed_of_aic _ hA
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have hR : IsIntegrallyClosed Γ(X, V) := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P _ hP
    let y : PrimeSpectrum Γ(X, V) := ⟨P, hP.isPrime⟩
    have hy : hV.fromSpec y ∈ V := by
      show hV.fromSpec y ∈ (V : Set X)
      rw [← hV.range_fromSpec]; exact ⟨y, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hV.fromSpec y, hy⟩ : V)
    have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P := hV.isLocalization_stalk' y hy
    have := hst (hV.fromSpec y)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv
  have hK : IsAlgClosed X.functionField := by
    obtain ⟨x⟩ := ‹Nonempty V›
    obtain ⟨U, hxU, hU, hA⟩ := hcov x.1
    have : Nonempty U := ⟨⟨x.1, hxU⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    exact NormPf.FFPf.algClosed_of_aic _ _ hA
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  intro p hp hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap Γ(X, V) X.functionField))
    (by
      rw [degree_map_eq_of_injective (IsFractionRing.injective Γ(X, V) X.functionField),
        degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hd.ne')
  have hint : IsIntegral Γ(X, V) z := ⟨p, hp, by rwa [IsRoot, Polynomial.eval_map] at hz⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, IsFractionRing.injective Γ(X, V) X.functionField ?_⟩
  have hz' : eval z (p.map (algebraMap Γ(X, V) X.functionField)) = 0 := hz
  rw [map_zero, ← hz', Polynomial.eval_map, ← ha, eval₂_at_apply]

end LateralTheory.E.LocalIntegralClosureRoots

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RootPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.RootPf

lemma unit_sec {Z : Scheme.{0}} (q : ℕ) (A : Type) [CommRing A] (p : Z ⟶ Spec (CommRingCat.of A))
    (hq : IsUnit (q : A)) (U : Z.Opens) : IsUnit (q : Γ(Z, U)) := by
  let f : CommRingCat.of A ⟶ Γ(Z, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
  have := hq.map f.hom
  simpa using this

lemma prim_of_aic (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] (hT : AIC T)
    (hq : IsUnit (q : T)) : ∃ a : T, IsPrimitiveRoot a q := by
  have : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  exact ⟨a, (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := a)).1 ha⟩

lemma local_root {Z : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U))
    (q : ℕ) [NeZero q] (hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U))) (ζ : Z.functionField)
    (hζ : IsPrimitiveRoot ζ q) (V : Z.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ s : Γ(Z, V), (Z.germToFunctionField V).hom s = ζ := by
  obtain ⟨a, ha⟩ := prim_of_aic q Γ(Z, V)
    (hZ V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)) (hqU V)
  have hb := ha.map_of_injective (f := (Z.germToFunctionField V).hom) (Z.germToFunctionField_injective V)
  obtain ⟨i, -, hi⟩ := hb.eq_pow_of_pow_eq_one hζ.pow_eq_one
  exact ⟨a ^ i, by rw [map_pow]; exact hi⟩

theorem Root_of : LateralTheory.E.ChartSurjCut.Root := by
  intro q A _ Z p hZ hq
  obtain ⟨hI, hA⟩ := hZ
  have hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U)) := fun U => unit_sec q A p hq U
  obtain ⟨x⟩ := (inferInstance : Nonempty Z)
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨x, trivial⟩⟩
  have hq0 : NeZero q := ⟨by rintro rfl; exact not_isUnit_zero (M₀ := Γ(Z, ⊤)) (by simpa using hqU ⊤)⟩
  have hbasis : ∀ {U : Z.Opens} {y : Z}, y ∈ U → ∃ U' ∈ Z.affineOpens, y ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
  have haff : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := by
    intro y
    obtain ⟨U, hU, hy, -⟩ := hbasis (show y ∈ (⊤ : Z.Opens) from trivial)
    exact ⟨U, hU, hy⟩
  obtain ⟨U₀, hU₀, hx⟩ := haff x
  have : Nonempty U₀ := ⟨⟨x, hx⟩⟩
  obtain ⟨a₀, ha₀⟩ := prim_of_aic q Γ(Z, U₀) (hA U₀ hU₀ ⟨x, hx⟩) (hqU U₀)
  set ζ : Z.functionField := (Z.germToFunctionField U₀).hom a₀ with hζdef
  have hζ : IsPrimitiveRoot ζ q :=
    ha₀.map_of_injective (f := (Z.germToFunctionField U₀).hom) (Z.germToFunctionField_injective U₀)
  let ι := {V : Z.Opens // IsAffineOpen V ∧ Nonempty V}
  let U : ι → Z.Opens := fun i => i.1
  have instU : ∀ i : ι, Nonempty (U i) := fun i => i.2.2
  have hex : ∀ i : ι, ∃ s : Γ(Z, U i), (Z.germToFunctionField (U i)).hom s = ζ := fun i =>
    @local_root Z hI hA q hq0 hqU ζ hζ i.1 i.2.1 i.2.2
  let sf : ∀ i : ι, Γ(Z, U i) := fun i => Classical.choose (hex i)
  have hsf : ∀ i : ι, (Z.germToFunctionField (U i)).hom (sf i) = ζ := fun i => Classical.choose_spec (hex i)
  have hcov : (⊤ : Z.Opens) ≤ iSup U := by
    intro y _
    obtain ⟨V, hV, hy⟩ := haff y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨⟨y, hy⟩⟩⟩, hy⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have : Nonempty (U i ⊓ U j : Z.Opens) := by
      obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (U i).isOpen (U j).isOpen
        (by obtain ⟨⟨y, hy⟩⟩ := i.2.2; exact ⟨y, hy⟩) (by obtain ⟨⟨y, hy⟩⟩ := j.2.2; exact ⟨y, hy⟩)
      exact ⟨⟨y, hy⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf i)) = Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨s0, hs, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov sf hcomp
  let s : Γ(Z, ⊤) := s0
  change ∀ i : ι, Z.presheaf.map (homOfLE le_top).op s = sf i at hs
  have hgs : (Z.germToFunctionField ⊤).hom s = ζ := by
    have h1 := hs ⟨U₀, hU₀, inferInstance⟩
    have h2 := hsf ⟨U₀, hU₀, inferInstance⟩
    rw [← h1] at h2
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ s) = ζ at h2
    rw [TopCat.Presheaf.germ_res_apply] at h2
    exact h2
  have hps : IsPrimitiveRoot s q := by
    have h' : IsPrimitiveRoot ((Z.germToFunctionField ⊤).hom s) q := by rw [hgs]; exact hζ
    exact IsPrimitiveRoot.of_map_of_injective h' (Z.germToFunctionField_injective ⊤)
  have : NeZero (q : Γ(Z, ⊤)) := ⟨(hqU ⊤).ne_zero⟩
  refine ⟨⟨s, hqU ⊤, ?_⟩⟩
  have hr := (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := s)).2 hps
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hr

end LateralTheory.E.RootPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.longPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.longPf
open LateralTheory.E.CxDescPf

def LES : Prop := ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x)

theorem four_inj {A B C D A' B' C' D' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D']
    (α : A →+ B) (β : B →+ C) (γ : C →+ D) (α' : A' →+ B') (β' : B' →+ C') (γ' : C' →+ D')
    (a : A →+ A') (b : B →+ B') (c : C →+ C') (d : D →+ D')
    (h2 : Function.Exact α β) (h2' : Function.Exact α' β') (h3 : Function.Exact β γ)
    (s1 : ∀ x, b (α x) = α' (a x)) (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x))
    (ha : Function.Surjective a) (hb : Function.Injective b) (hd : Function.Injective d) : Function.Injective c := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have : γ x = 0 := hd (by rw [s3, hx, map_zero, map_zero])
  obtain ⟨y, rfl⟩ := (h3 x).1 this
  have : β' (b y) = 0 := by rw [← s2]; exact hx
  obtain ⟨z', hz'⟩ := (h2' (b y)).1 this
  obtain ⟨z, rfl⟩ := ha z'
  have : α z = y := hb (by rw [s1, hz'])
  rw [← this]; exact h2.apply_apply_eq_zero z

theorem four_surj {B C D E B' C' D' E' : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D'] [AddCommGroup E']
    (β : B →+ C) (γ : C →+ D) (δ : D →+ E) (β' : B' →+ C') (γ' : C' →+ D') (δ' : D' →+ E')
    (b : B →+ B') (c : C →+ C') (d : D →+ D') (e : E →+ E')
    (h2' : Function.Exact β' γ') (h3 : Function.Exact γ δ) (h3' : Function.Exact γ' δ')
    (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x)) (s4 : ∀ x, e (δ x) = δ' (d x))
    (hb : Function.Surjective b) (hd : Function.Surjective d) (he : Function.Injective e) : Function.Surjective c := by
  intro x'
  obtain ⟨y, hy⟩ := hd (γ' x')
  have : δ y = 0 := he (by rw [s4, hy, map_zero, h3'.apply_apply_eq_zero])
  obtain ⟨w, rfl⟩ := (h3 y).1 this
  have : γ' (x' - c w) = 0 := by rw [map_sub, ← s3, hy, sub_self]
  obtain ⟨u', hu'⟩ := (h2' _).1 this
  obtain ⟨u, rfl⟩ := hb u'
  exact ⟨w + β u, by rw [map_add (f := _), s2, hu', add_sub_cancel]⟩

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre_mk]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_sq {R : Type} [CommRing R] {A B C D : Cx R} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (w : f ≫ g = f' ≫ g') (I : Cx R) (n : ℤ) (x) :
    cpull f I n (cpull g I n x) = cpull f' I n (cpull g' I n x) := by
  rw [← cpull_comp, ← cpull_comp, w]

def Ses : Prop := ∀ (R : Type) [CommRing R] (N : ℕ), ∃ (i : ∀ K : Cx R, tr K N ⟶ tr K (N + 1))
  (p : ∀ K : Cx R, tr K (N + 1) ⟶ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ))))
  (w : ∀ K, i K ≫ p K = 0), (∀ K, (ShortComplex.mk (i K) (p K) (w K)).ShortExact) ∧
  ∀ {K L : Cx R} (g : K ⟶ L), i K ≫ trm g (N + 1) = trm g N ≫ i L ∧
    p K ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) = trm g (N + 1) ≫ p L

theorem long_of (hLES : LES) (hSes : Ses) : LateralTheory.E.CxDescPf.long := by
  intro R _ I _ hI K L _ _ g m N h3 h1
  obtain ⟨d, hex, hnat⟩ := hLES R I hI
  obtain ⟨i, p, w, hse, hn⟩ := hSes R N
  let MainNotions := ShortComplex.mk (i K) (p K) (w K)
  let SL := ShortComplex.mk (i L) (p L) (w L)
  let φ : MainNotions ⟶ SL := ShortComplex.Hom.mk (trm g N) (trm g (N + 1))
    ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) (hn g).1.symm (hn g).2.symm
  have sf : ∀ j x, cpull φ.τ₁ I j (cpull SL.f I j x) = cpull MainNotions.f I j (cpull φ.τ₂ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₁₂ I j x
  have sg : ∀ j x, cpull φ.τ₂ I j (cpull SL.g I j x) = cpull MainNotions.g I j (cpull φ.τ₃ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₂₃ I j x
  have inj : ∀ n : ℤ, n + 1 ≤ m → Function.Injective (cpull φ.τ₂ I (n + 1)) := by
    intro n hn
    refine four_inj (d SL (hse L) n) (cpull SL.g I (n + 1)) (cpull SL.f I (n + 1))
      (d MainNotions (hse K) n) (cpull MainNotions.g I (n + 1)) (cpull MainNotions.f I (n + 1))
      (cpull φ.τ₁ I n) (cpull φ.τ₃ I (n + 1)) (cpull φ.τ₂ I (n + 1)) (cpull φ.τ₁ I (n + 1))
      (hex SL (hse L) n).2.2 (hex MainNotions (hse K) n).2.2 (hex SL (hse L) (n + 1)).1
      (fun x => hnat MainNotions SL (hse K) (hse L) φ n x) (sg (n + 1)) (sf (n + 1))
      (h1.1 n (by omega)).2 ?_ ?_
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h3.1 _ h).1
      · rw [h]; exact h3.2
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h1.1 _ h).1
      · rw [h]; exact h1.2
  have surj : ∀ j : ℤ, j < m → Function.Surjective (cpull φ.τ₂ I j) := by
    intro j hj
    refine four_surj (cpull SL.g I j) (cpull SL.f I j) (d SL (hse L) j)
      (cpull MainNotions.g I j) (cpull MainNotions.f I j) (d MainNotions (hse K) j)
      (cpull φ.τ₃ I j) (cpull φ.τ₂ I j) (cpull φ.τ₁ I j) (cpull φ.τ₃ I (j + 1))
      (hex MainNotions (hse K) j).1 (hex SL (hse L) j).2.1 (hex MainNotions (hse K) j).2.1
      (sg j) (sf j) (fun x => hnat MainNotions SL (hse K) (hse L) φ j x)
      (h3.1 j hj).2 (h1.1 j hj).2 ?_
    rcases lt_or_eq_of_le (show j + 1 ≤ m by omega) with h | h
    · exact (h3.1 _ h).1
    · rw [h]; exact h3.2
  have inj' : ∀ j : ℤ, j ≤ m → Function.Injective (cpull φ.τ₂ I j) := by
    intro j hj
    have := inj (j - 1) (by omega)
    rwa [sub_add_cancel] at this
  exact ⟨fun j hj => ⟨inj' j hj.le, surj j hj⟩, inj' m le_rfl⟩

end LateralTheory.E.longPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ProjGPf
noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjGPf

variable {S : Type} [CommRing S]

theorem isUnit_f_fg (f g : S) : IsUnit (algebraMap S (Localization.Away (f * g)) f) :=
  isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g)) (IsLocalization.Away.algebraMap_isUnit (f * g))

theorem rL_alg (f g : S) (a : S) :
    rL f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_alg (f g : S) (a : S) :
    rR f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_surj {ι : Type} [Finite ι] (f g : S) (w : ι → Localization.Away (f * g)) :
    ∃ (n : ℕ) (x : ι → Localization.Away f), ∀ k, rL f g (x k) = algebraMap S _ (g ^ n) * w k := by
  obtain ⟨⟨b, hb'⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hb'
  choose a ha using hb
  refine ⟨n, fun k => IsLocalization.mk' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f), fun k => ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (f ^ n)) := by
    rw [map_pow]; exact (isUnit_f_fg f g).pow n
  apply hu.mul_left_cancel
  have hs := IsLocalization.mk'_spec' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  change algebraMap S _ (f ^ n) * _ = _ at hs
  rw [← rL_alg, ← map_mul, hs, rL_alg, ha k, Algebra.smul_def]
  change algebraMap S _ ((f * g) ^ n) * w k = _
  rw [mul_pow, map_mul, mul_assoc, rL_alg]

theorem rL_ker (f g : S) (x : Localization.Away f) (hx : rL f g x = 0) :
    ∃ n : ℕ, algebraMap S _ (g ^ n) * x = 0 := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have h0 : algebraMap S (Localization.Away (f * g)) a = 0 := by
    rw [← rL_alg, ← hs, map_mul, hx, zero_mul]
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ a).mp h0
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away f) (f ^ n * s)) :=
    IsLocalization.map_units (Localization.Away f)
      (⟨f ^ n * s, Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers f) n) s.2⟩ : Submonoid.powers f)
  apply (hu.mul_left_eq_zero).mp
  have e1 : algebraMap S (Localization.Away f) (g ^ n) * x * algebraMap S _ (f ^ n * s)
      = algebraMap S _ (g ^ n * f ^ n) * (x * algebraMap S _ (s : S)) := by
    simp only [map_mul]; ring
  rw [e1, hs, ← map_mul, show g ^ n * f ^ n * a = (f * g) ^ n * a by ring, hm, map_zero]

theorem rL_ker_fam {ι : Type} [Fintype ι] (f g : S) (x : ι → Localization.Away f)
    (hx : ∀ k, rL f g (x k) = 0) : ∃ n : ℕ, ∀ k, algebraMap S _ (g ^ n) * x k = 0 := by
  choose n hn using fun k => rL_ker f g (x k) (hx k)
  refine ⟨Finset.univ.sup n, fun k => ?_⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : n k ≤ _), pow_add, map_mul, mul_assoc, hn k,
    mul_zero]

theorem twist_apply {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}
    (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

theorem ProjG_of : ProjG := by
  intro q _ S _ f g hfg ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr2 f g hε).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have e : algebraMap (Tor f g hε) (ZMod q → Localization.Away g) (algebraMap S (Tor f g hε) g ^ n)
        = fun _ => algebraMap S (Localization.Away g) g ^ n := by
      rw [map_pow]; rfl
    rw [e]
    exact Pi.isUnit_iff.mpr fun _ => (IsLocalization.Away.algebraMap_isUnit g).pow n
  · intro y
    obtain ⟨n, x, hx⟩ := rL_surj f g (twist hε (fun k => rR f g (y k)))
    have hmem : ((x, fun k => algebraMap S _ (g ^ n) * y k) : Amb f g q) ∈ Tor f g hε := by
      show h1 f g _ = h2 f g hε _
      funext k
      change rL f g (x k) = ∑ c, ε c * rR f g (algebraMap S _ (g ^ n) * y (k + c))
      rw [hx k, twist_apply]
      simp only [map_mul, rR_alg]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    refine ⟨(⟨_, hmem⟩, ⟨algebraMap S _ g ^ n, n, rfl⟩), ?_⟩
    show y * pr2 f g hε (torMap f g hε g ^ n) = pr2 f g hε ⟨_, hmem⟩
    rw [map_pow]
    funext k
    change y k * (algebraMap S (Localization.Away g) g) ^ n = algebraMap S _ (g ^ n) * y k
    rw [map_pow, mul_comm]
  · intro t1 t2 h
    have h0 : (t1 - t2).1.2 = 0 := by
      have : pr2 f g hε (t1 - t2) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr h
      exact this
    have hx : ∀ k, rL f g ((t1 - t2).1.1 k) = 0 := by
      intro k
      have hm : h1 f g (t1 - t2).1 = h2 f g hε (t1 - t2).1 := (t1 - t2).2
      have hk := congrFun hm k
      change rL f g ((t1 - t2).1.1 k) = ∑ c, ε c * rR f g ((t1 - t2).1.2 (k + c)) at hk
      rw [hk, h0]; simp
    obtain ⟨n, hn⟩ := rL_ker_fam f g (fun k => (t1 - t2).1.1 k) hx
    refine ⟨⟨algebraMap S _ g ^ n, n, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    show torMap f g hε g ^ n * (t1 - t2) = 0
    apply Subtype.ext
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · change (algebraMap S (Localization.Away f) g) ^ n * (t1 - t2).1.1 k = 0
      rw [← map_pow]; exact hn k
    · change (algebraMap S (Localization.Away g) g) ^ n * (t1 - t2).1.2 k = 0
      rw [h0]; simp

end LateralTheory.E.ProjGPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StageBPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

namespace LateralTheory.E.StageBPf

theorem pp {q : ℕ} {i n : ℤ} {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Ht q (sch.obj Z) n i) :
    pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) = pull _ (sch.map (a ≫ b)) (tw q i) n x := by
  rw [Functor.map_comp, pull_comp]

theorem indep {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j j' : J) :
    c.π.app j ≫ ι j = c.π.app j' ≫ ι j' := by
  rw [← c.w (IsCofiltered.minToLeft j j'), ← c.w (IsCofiltered.minToRight j j'), Category.assoc, Category.assoc, hι, hι]

theorem qc_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : CompactSpace Y) : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace f
theorem qs_of {X Y : Scheme.{0}} (f : X ⟶ Y) (h : IsAffineHom f) (hY : QuasiSeparatedSpace Y) : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated f
theorem aff_canc {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom (f ≫ g)) (h2 : IsAffineHom g) : IsAffineHom f := by
  have := IsSeparated.of_isAffineHom g; exact IsAffineHom.of_comp f g
theorem aff_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h1 : IsAffineHom f) (h2 : IsAffineHom g) : IsAffineHom (f ≫ g) :=
  inferInstance

variable {A : Type} [CommRing A] [IsLocalRing A]

def DO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0})
    (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) : J ⥤ Over (Spec (CommRingCat.of A)) where
  obj j := Over.mk (ι j ≫ g)
  map f := Over.homMk (D.map f) (by dsimp; rw [← Category.assoc, hι])
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp

def CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
    (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J) :
    Cone (DO g D ι hι) where
  pt := Over.mk ((c.π.app j0 ≫ ι j0) ≫ g)
  π := { app := fun j => Over.homMk (c.π.app j) (by show c.π.app j ≫ ι j ≫ g = _; rw [← Category.assoc, indep D c ι hι j j0]; rfl)
         naturality := by intro j k f; ext; exact (c.w f).symm }

def isLimit_CO {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) : IsLimit (CO g D c ι hι j0) := by
  haveI := IsCofiltered.isConnected J
  exact isLimitOfReflects (Over.forget _) hl

def isLimit_fib {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {J : Type} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y) (hι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) (j0 : J)
    (hl : IsLimit c) :
    IsLimit ((Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι j0))) := by
  haveI := IsCofiltered.isConnected J
  haveI := (Over.mapPullbackAdj (cpt A)).rightAdjoint_preservesLimits
  exact isLimitOfPreserves _ (isLimitOfPreserves _ (isLimit_CO g D c ι hι j0 hl))

theorem fm_comp {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) {U V : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (d : U ⟶ V)
    (hd : d ≫ v = u) (h : pullback (u ≫ g) (cpt A) ⟶ pullback (v ≫ g) (cpt A))
    (h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d) (h2 : h ≫ pullback.snd _ _ = pullback.snd _ _) :
    h ≫ fm v g = fm u g := by
  apply pullback.hom_ext
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, h1, Category.assoc, hd]
  · simp only [fm, pullback.map, Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd, Category.comp_id, Category.comp_id, h2]

end LateralTheory.E.StageBPf

namespace LateralTheory.E.StageBPf

theorem StageB_of : StageB := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n z
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  have hι' : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j := fun f => (hD f).1
  obtain ⟨w, hw⟩ := (hp j0 n).2 (pull _ (sch.map (fm (c.π.app j0 ≫ ι j0) g)) _ _ z)
  obtain ⟨j1, u, hu⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).1 w
  have hfa : ∀ j, IsAffineHom (pullback.fst (ι j ≫ g) (cpt A)) := fun j =>
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have hκ : IsUnit (q : IsLocalRing.ResidueField A) := by simpa using hq.map (IsLocalRing.residue A)
  let Cg := (Over.forget _).mapCone ((Over.pullback (cpt A)).mapCone (CO g D c ι hι' j0))
  have hlim : IsLimit Cg := isLimit_fib g D c ι hι' j0 hl
  have hEaff : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f) := by
    intro j k f
    have e : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι k ≫ g) (cpt A) =
        pullback.fst (ι j ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
    refine aff_canc _ (pullback.fst (ι k ≫ g) (cpt A)) ?_ (hfa k)
    rw [e]; exact aff_comp _ _ (hfa j) (hD f).2
  have hEc : ∀ j, CompactSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qc_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hcs j)
  have hEq : ∀ j, QuasiSeparatedSpace (((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j) := fun j =>
    qs_of (pullback.fst (ι j ≫ g) (cpt A)) (hfa j) (hqs j)
  have hEu : ∀ j, IsUnit (q : Γ((((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).obj j), ⊤)) := fun j =>
    unit_of hκ (pullback.snd (ι j ≫ g) (cpt A))
  have key1 : Cg.π.app j1 ≫ pullback.fst (ι j1 ≫ g) (cpt A) = pullback.fst _ _ ≫ c.π.app j1 := pullback.lift_fst _ _ _
  have key1s : Cg.π.app j1 ≫ pullback.snd (ι j1 ≫ g) (cpt A) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have key2 : Cg.π.app j1 ≫ fm (ι j1) g = fm (c.π.app j0 ≫ ι j0) g :=
    fm_comp g (c.π.app j0 ≫ ι j0) (ι j1) (c.π.app j1) (indep D c ι hι' j1 j0) _ key1 key1s
  have hv : pull _ (sch.map (Cg.π.app j1)) _ _ (pull _ (sch.map (pullback.fst (ι j1 ≫ g) (cpt A))) _ _ u -
      pull _ (sch.map (fm (ι j1) g)) (tw q i) n z) = 0 := by
    erw [map_sub, pp, pp, key1, key2, ← pp, hu, hw, sub_self]
  obtain ⟨k, f, hk⟩ := (hC H q _ Cg hlim hEaff hEc hEq hEu n i).2 j1 _ hv
  refine ⟨k, pull _ (sch.map (D.map f)) _ _ u, ?_⟩
  have key3 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.fst (ι j1 ≫ g) (cpt A) =
      pullback.fst (ι k ≫ g) (cpt A) ≫ D.map f := pullback.lift_fst _ _ _
  have key5 : ((DO g D ι hι' ⋙ Over.pullback (cpt A)) ⋙ Over.forget _).map f ≫ pullback.snd (ι j1 ≫ g) (cpt A) =
      pullback.snd (ι k ≫ g) (cpt A) := pullback.lift_snd _ _ _
  have key4 := fm_comp g (ι k) (ι j1) (D.map f) (hι' f) _ key3 key5
  erw [map_sub, pp, pp, key3, key4, ← pp, sub_eq_zero] at hk
  exact hk

end LateralTheory.E.StageBPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTruncPf
noncomputable section
open CategoryTheory Limits Pretriangulated Triangulated

namespace LateralTheory.E.LeafTruncPf

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

lemma mono_H_ι (Y : DerivedCategory C) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) Y
  have := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (n - 1) n (by lia)).2
    (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE _ (n + 1) (n - 1) (by lia)) _ _)
  exact this

lemma epi_H_π (X : DerivedCategory C) (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished n X
  have := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT n (n + 1) (by lia)).2
    (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isLE _ (n - 1) (n + 1) (by lia)) _ _)
  exact this

lemma lift_LT {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : φ ≫ (DerivedCategory.TStructure.t.truncGEπ n).app Y = 0) :
    ∃ ψ : X ⟶ (DerivedCategory.TStructure.t.truncLT n).obj Y,
      φ = ψ ≫ (DerivedCategory.TStructure.t.truncLTι n).app Y :=
  Triangle.coyoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n Y) φ h

lemma desc_GE {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ φ = 0) :
    ∃ ψ : (DerivedCategory.TStructure.t.truncGE n).obj X ⟶ Y,
      φ = (DerivedCategory.TStructure.t.truncGEπ n).app X ≫ ψ :=
  Triangle.yoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n X) φ h

lemma heart_zero {X Y : DerivedCategory C} (n : ℤ) [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (χ : X ⟶ Y) (hχ : (DerivedCategory.homologyFunctor C n).map χ = 0) : χ = 0 := by
  obtain ⟨A, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨B, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor C n).map_surjective (eX.inv ≫ χ ≫ eY.hom)
  have ha0 : a = 0 := by
    have eq := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) a
    dsimp at eq
    rw [← eq, ha]
    simp [hχ]
  have : χ = eX.hom ≫ (eX.inv ≫ χ ≫ eY.hom) ≫ eY.inv := by simp
  rw [this, ← ha, ha0, Functor.map_zero]
  simp

lemma zero_of_H {X Y : DerivedCategory C} (n : ℤ) [X.IsLE n] [Y.IsGE n] (φ : X ⟶ Y)
    (hφ : (DerivedCategory.homologyFunctor C n).map φ = 0) : φ = 0 := by
  have h1 : φ ≫ (DerivedCategory.TStructure.t.truncGEπ (n + 1)).app Y = 0 :=
    DerivedCategory.TStructure.t.zero _ n (n + 1)
  obtain ⟨ψ, hψ⟩ := lift_LT (n + 1) φ h1
  have h2 : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ ψ = 0 :=
    DerivedCategory.TStructure.t.zero _ (n - 1) n
  obtain ⟨χ, hχ⟩ := desc_GE n ψ h2
  have hHχ : (DerivedCategory.homologyFunctor C n).map χ = 0 := by
    have := mono_H_ι Y n
    have := epi_H_π X n
    rw [hψ, hχ, Functor.map_comp, Functor.map_comp] at hφ
    rw [← cancel_epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)),
      ← cancel_mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y))]
    simpa using hφ
  have : χ = 0 := heart_zero n χ hHχ
  rw [hψ, hχ, this]
  simp

end LateralTheory.E.LeafTruncPf

open LateralTheory.E.LeafTruncPf in
theorem LateralTheory.E.LeafGhostRelCut.LeafTrunc_of : LateralTheory.E.LeafGhostRelCut.LeafTrunc := by
  intro A _ _ _ K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  have : K0.IsLE 2 := (DerivedCategory.isLE_iff K0 2).2 hK0
  have : K2.IsGE 0 := (DerivedCategory.isGE_iff K2 0).2 hK2
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 (fun i hi => hL i (by lia))
  have : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 2).obj K1) 1 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have hP : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 1).obj K2) 0 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have e1 : f ≫ (DerivedCategory.TStructure.t.truncGEπ 2).app K1 = 0 :=
    zero_of_H 2 _ (by simp [Functor.map_comp, hf])
  obtain ⟨f', hf'⟩ := lift_LT 2 f e1
  have e2 : ((DerivedCategory.TStructure.t.truncLTι 2).app K1 ≫ g) ≫
      (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    zero_of_H 1 _ (by simp [Functor.map_comp, hg])
  obtain ⟨w, hw⟩ := lift_LT 1 _ e2
  have e3 : ℓ ≫ (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    DerivedCategory.TStructure.t.zero _ 0 1
  obtain ⟨ℓ', hℓ'⟩ := lift_LT 1 ℓ e3
  have hiso : IsIso ℓ' := by
    rw [DerivedCategory.isIso_iff]
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · have hm0 := mono_H_ι K2 0
      rw [zero_add] at hm0
      have hc : IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ' ≫
          (DerivedCategory.homologyFunctor A 0).map
            ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := by
        rw [← Functor.map_comp, ← hℓ']; exact hℓ
      have : Epi ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) :=
        epi_of_epi ((DerivedCategory.homologyFunctor A 0).map ℓ') _
      have : IsIso ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := isIso_of_mono_of_epi _
      exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor A 0).map
        ((DerivedCategory.TStructure.t.truncLTι 1).app K2))
    · have hZ : IsZero ((DerivedCategory.homologyFunctor A m).obj
          ((DerivedCategory.TStructure.t.truncLT 1).obj K2)) := by
        rcases lt_or_gt_of_ne hm with h | h
        · exact DerivedCategory.isZero_of_isGE _ 0 m h
        · exact DerivedCategory.isZero_of_isLE _ 0 m h
      exact ⟨⟨0, (hL m hm).eq_of_src _ _, hZ.eq_of_src _ _⟩⟩
  refine ⟨f' ≫ w ≫ inv ℓ', ?_⟩
  rw [hf', hℓ']
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, hw]

end
end
