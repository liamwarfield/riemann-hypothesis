module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOrigin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPoints
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.VertUnits

private theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  intro T E _ _ _ _ _ Q _ hQ
  set I : Ideal (Polynomial T) := (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
    with hI
  have hIQ : I ≤ Q.comap (algebraMap (Polynomial T) E) := hQ.ge
  let f : Polynomial T ⧸ I →+* E ⧸ Q := Ideal.quotientMap Q (algebraMap (Polynomial T) E) hIQ
  let K := T ⧸ maximalIdeal T
  let _ : Field K := Ideal.Quotient.field _
  let e : Polynomial K ≃+* Polynomial T ⧸ I :=
    Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)
  have : IsJacobsonRing (Polynomial T ⧸ I) :=
    isJacobsonRing_of_surjective ⟨e.toRingHom, e.surjective⟩
  have hnf : ¬ IsField (Polynomial T ⧸ I) := fun h =>
    Polynomial.not_isField K (MulEquiv.isField h e.toMulEquiv)
  have hft : f.FiniteType := by
    have h1 : ((Ideal.Quotient.mk Q).comp (algebraMap (Polynomial T) E)).FiniteType :=
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    rw [← Ideal.quotientMap_comp_mk hIQ] at h1
    exact RingHom.FiniteType.of_comp_finiteType h1
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (E ⧸ Q)
  have hcm : (m.comap f).IsMaximal := by
    let _ := Ideal.Quotient.field m
    let g : Polynomial T ⧸ I →+* (E ⧸ Q) ⧸ m := (Ideal.Quotient.mk m).comp f
    have hgft : g.FiniteType :=
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft
    have hgint : g.IsIntegral :=
      (RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hgft).to_isIntegral
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' g hgint ⊥
    have heq : m.comap f = (⊥ : Ideal ((E ⧸ Q) ⧸ m)).comap g := by
      ext a
      simp [g, Ideal.Quotient.eq_zero_iff_mem]
    rw [heq]
    exact this
  have hcm0 : m.comap f ≠ ⊥ := by
    intro h
    rw [h] at hcm
    exact hnf (Ring.isField_iff_maximal_bot.mpr hcm)
  refine ⟨m.comap (Ideal.Quotient.mk Q), Ideal.comap_isMaximal_of_surjective _
    Ideal.Quotient.mk_surjective, fun x hx => ?_, ?_, ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  · intro hy
    apply hcm0
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hp : p ∈ (m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E) := by
      simpa [f, Ideal.quotientMap_mk] using ha
    rw [hy] at hp
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hp
  · have hle : maximalIdeal T ≤
        ((m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E)).comap
          (Polynomial.C : T →+* Polynomial T) := by
      intro t ht
      simp only [Ideal.mem_comap]
      have h1 : Polynomial.C t ∈ I := Ideal.mem_map_of_mem _ ht
      have h2 : algebraMap (Polynomial T) E (Polynomial.C t) ∈ Q := hIQ h1
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr h2]
    have hp : (((m.comap (Ideal.Quotient.mk Q)).comap (algebraMap (Polynomial T) E)).comap
        (Polynomial.C : T →+* Polynomial T)).IsPrime := by
      have : (m.comap (Ideal.Quotient.mk Q)).IsPrime := Ideal.comap_isPrime _ _
      exact Ideal.comap_isPrime _ _
    exact ((maximalIdeal.isMaximal T).eq_of_le hp.ne_top hle).symm

private theorem isSeparable_apply_of_etale (R A K L : Type) [CommRing R] [CommRing A] [Field K]
    [Field L] [Algebra R A] [Algebra.Etale R A] [Algebra R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] (h : A →ₐ[R] L) (a : A) : IsSeparable K (h a) := by
  let H : TensorProduct R K A →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) h (fun _ _ => Commute.all _ _)
  let f := Ideal.kerLiftAlg H
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective H
  have : (RingHom.ker H).IsPrime := RingHom.ker_isPrime (H : TensorProduct R K A →+* L)
  have : Algebra.Etale K (TensorProduct R K A) := inferInstance
  have : Algebra.EssFiniteType K (TensorProduct R K A) := inferInstance
  have hx : f (Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight a)) = h a := by
    simp [f, H]
  rw [← hx]
  show (minpoly K (f _)).Separable
  rw [minpoly.algHom_eq f hf]
  exact Algebra.IsSeparable.isSeparable K _

private theorem specialisation_map : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  intro R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hSy hOQ hflat hpieces
  have : (IsLocalRing.maximalIdeal S).LiesOver y := ⟨hSy.symm⟩
  obtain ⟨𝔭, -, _, h𝔭⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y)
    (IsLocalRing.maximalIdeal S) hQy
  have h𝔭Q : Q = 𝔭.comap (algebraMap R S) := h𝔭.over
  let F := IsLocalRing.ResidueField O
  have hF : Q ≤ RingHom.ker (algebraMap R F) := fun x hx => by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R O F,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    rw [← hOQ] at hx
    exact hx
  have hF' : Q.primeCompl ≤ (IsUnit.submonoid F).comap (algebraMap R F) := fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    rw [isUnit_iff_ne_zero, IsScalarTower.algebraMap_apply R O F, ne_eq,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    intro h
    apply hx
    rw [← hOQ]
    exact h
  let κQ := Q.ResidueField
  let κ𝔭 := 𝔭.ResidueField
  let _ : Algebra κQ F := (Ideal.ResidueField.lift Q (algebraMap R F) hF hF').toAlgebra
  have hRQF : IsScalarTower R κQ F := IsScalarTower.of_algebraMap_eq (fun r =>
    (Ideal.ResidueField.lift_algebraMap Q (algebraMap R F) hF hF' r).symm)
  let _ : Algebra κQ κ𝔭 := (Ideal.ResidueField.map Q 𝔭 (algebraMap R S) h𝔭Q).toAlgebra
  have hRQP : IsScalarTower R κQ κ𝔭 := IsScalarTower.of_algebraMap_eq (fun r => by
    change _ = Ideal.ResidueField.map Q 𝔭 (algebraMap R S) h𝔭Q (algebraMap R κQ r)
    rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply])
  have hsepS : ∀ s : S, algebraMap S κ𝔭 s ∈ separableClosure κQ κ𝔭 := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hpc⟩ := hpieces
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hpc i
    let g : Localization.AtPrime q →ₐ[R] κ𝔭 :=
      (IsScalarTower.toAlgHom R S κ𝔭).comp ((Si i).val.comp e.toAlgHom)
    let h : A →ₐ[R] κ𝔭 := g.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))
    obtain ⟨z, hz⟩ := e.surjective ⟨s, hi⟩
    have hgz : g z = algebraMap S κ𝔭 s := by simp [g, hz]
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (M := q.primeCompl)
      (S := Localization.AtPrime q) z
    have hat' : IsLocalization.mk' (Localization.AtPrime q) a t = z := hat
    rw [← hat'] at hgz
    have hu : IsUnit (h t) := (IsLocalization.map_units (Localization.AtPrime q) t).map g
    have hgz' : g (IsLocalization.mk' (Localization.AtPrime q) a t) = h a * (h t)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hu.ne_zero]
      change _ = g (algebraMap A _ a)
      rw [← IsLocalization.mk'_spec (Localization.AtPrime q) a t, map_mul]
      rfl
    rw [← hgz, hgz']
    exact (separableClosure κQ κ𝔭).mul_mem
      (mem_separableClosure_iff.mpr (isSeparable_apply_of_etale R A κQ κ𝔭 h a))
      ((separableClosure κQ κ𝔭).inv_mem
        (mem_separableClosure_iff.mpr (isSeparable_apply_of_etale R A κQ κ𝔭 h t)))
  have hsep : Algebra.IsSeparable κQ κ𝔭 := ⟨fun x => by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (S ⧸ 𝔭) x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk]
    exact mem_separableClosure_iff.mp ((separableClosure κQ κ𝔭).div_mem (hsepS u) (hsepS v))⟩
  let ι : κ𝔭 →ₐ[κQ] F := IsSepClosed.lift (K := κQ) (L := κ𝔭) (M := F)
  let χ : S →ₐ[R] F :=
    { toRingHom := (ι : κ𝔭 →+* F).comp (algebraMap S κ𝔭)
      commutes' := fun r => by
        show ι (algebraMap S κ𝔭 (algebraMap R S r)) = algebraMap R F r
        rw [← IsScalarTower.algebraMap_apply R S κ𝔭, IsScalarTower.algebraMap_apply R κQ κ𝔭,
          ι.commutes, ← IsScalarTower.algebraMap_apply R κQ F] }
  obtain ⟨φ, -⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 χ
  exact ⟨φ⟩

private theorem sh_at {T E : Type} [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S) (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  let L := Localization.AtPrime y
  let Ω := SeparableClosure (IsLocalRing.ResidueField L)
  obtain ⟨S, _, _, _, hloc, hsep, hflat, -, -, hpieces⟩ := GlobalTheory.exists_strictHenselisation L Ω
  have : IsSepClosed (IsLocalRing.ResidueField S) := hsep
  let _ : Algebra E S := ((algebraMap L S).comp (algebraMap E L)).toAlgebra
  have hELS : IsScalarTower E L S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : Algebra (Polynomial T) S :=
    ((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra
  let _ : Algebra T S := ((algebraMap E S).comp (algebraMap T E)).toAlgebra
  have hTES : IsScalarTower T E S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hPES : IsScalarTower (Polynomial T) E S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hTPS : IsScalarTower T (Polynomial T) S := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap E S (algebraMap T E x) =
      algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) E x])
  have hPLS : IsScalarTower (Polynomial T) L S := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply (Polynomial T) E L x]
    rfl)
  have hmax : (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y := by
    rw [IsScalarTower.algebraMap_eq E L S, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap (algebraMap L S)]
    exact IsLocalization.AtPrime.under_maximalIdeal L y
  have hflatE : Module.Flat E S := Module.Flat.trans E L S
  have hLE : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (Si : ι → Subalgebra E L), Monotone Si ∧ (∀ s : L, ∃ i, s ∈ Si i) ∧
      ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra E A) (_ : Algebra.Etale E A) (q : Ideal A)
        (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[E] Si i) :=
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨E, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩
  have hLP : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (Si : ι → Subalgebra (Polynomial T) L), Monotone Si ∧ (∀ s : L, ∃ i, s ∈ Si i) ∧
      ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A)
        (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A)
        (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[Polynomial T] Si i) :=
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨E, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩
  have hpE : GlobalTheory.LocAcyc.LocPiecesEtale E S := GlobalTheory.indEtale_localPieces_trans E L S hLE hpieces
  obtain ⟨P, _, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S
    (GlobalTheory.indEtale_localPieces_trans (Polynomial T) L S hLP hpieces)
  have hP : P = y.comap (algebraMap (Polynomial T) E) := by
    have : IsLocalHom φ := hsh.2.2.1
    rw [← hmax, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, ← hφ, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap φ]
    exact (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P).symm
  subst hP
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, hTES, inferInstance, hTPS,
    hPES, hmax, hflatE, hpE, φ, hφ, hsh⟩

private theorem stage : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (b c : O) (s : T), b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (g g' : E),
      ψ g = b ∧ ψ g' = c ∧ g * g' = algebraMap T E s := by
  intro T O _ _ _ _ _ P _ φ hφ hind b c s hbc
  let r : MvPolynomial (Fin 2) (Polynomial T) :=
    MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (Polynomial.C s)
  let Z := MvPolynomial (Fin 2) (Polynomial T) ⧸ Ideal.span {r}
  have : Algebra.FinitePresentation (Polynomial T) Z :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton r)
  let g0 : MvPolynomial (Fin 2) (Polynomial T) →ₐ[Polynomial T] O := MvPolynomial.aeval ![b, c]
  have hg0 : ∀ a ∈ Ideal.span {r}, g0 a = 0 := by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [g0, r, map_mul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hbc,
      IsScalarTower.algebraMap_apply T (Polynomial T) O s, Polynomial.algebraMap_eq, sub_self,
      mul_zero]
  let gZ : Z →ₐ[Polynomial T] O := Ideal.Quotient.liftₐ _ g0 hg0
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.T.exists_etale_factorization_of_isIndEtale (Polynomial T) O P φ hφ hind Z gZ
  let _ : Algebra T W := ((algebraMap (Polynomial T) W).comp (algebraMap T (Polynomial T))).toAlgebra
  have hW : IsScalarTower T (Polynomial T) W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let x₀ : Z := Ideal.Quotient.mk _ (MvPolynomial.X 0)
  let x₁ : Z := Ideal.Quotient.mk _ (MvPolynomial.X 1)
  have hv : ∀ z : Z, v (u z) = gZ z := fun z => by rw [← AlgHom.comp_apply, huv]
  refine ⟨W, inferInstance, inferInstance, inferInstance, hW, inferInstance, v, u x₀, u x₁,
    ?_, ?_, ?_⟩
  · rw [hv]
    change g0 (MvPolynomial.X 0) = b
    simp [g0]
  · rw [hv]
    change g0 (MvPolynomial.X 1) = c
    simp [g0]
  · have hx : x₀ * x₁ = algebraMap (Polynomial T) Z (Polynomial.C s) := by
      rw [← Ideal.Quotient.mk_algebraMap, ← map_mul]
      refine Ideal.Quotient.eq.mpr (Ideal.subset_span ?_)
      rw [Set.mem_singleton_iff, MvPolynomial.algebraMap_eq]
    rw [← map_mul, hx, u.commutes]
    rfl

theorem divConstGeneric_of_divConstClosedPts : DivConstClosedPts → DivConstGeneric := by
  intro hcl T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hPgen b c s hs hbc
  obtain ⟨hHen, hSep, hloc, hind⟩ := hsh
  obtain ⟨E, _, _, _, _, _, ψ, g, g', hg, hg', hgg⟩ := stage T O P φ hφ hind b c s hbc
  let _ : Algebra E O := ψ.toRingHom.toAlgebra
  have hEO : ∀ e : E, algebraMap E O e = ψ e := fun _ => rfl
  let Q : Ideal E := (maximalIdeal O).comap (algebraMap E O)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q.comap (algebraMap (Polynomial T) E) =
      (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) := by
    rw [← hPgen]
    ext p
    have h1 : algebraMap E O (algebraMap (Polynomial T) E p) =
        φ (algebraMap (Polynomial T) (Localization.AtPrime P) p) := by
      rw [hEO, ψ.commutes, ← hφ, RingHom.comp_apply]
    simp only [Q, Ideal.mem_comap, h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_map_iff φ]
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P p
  obtain ⟨y, hymax, hQy, hyne, hyT⟩ := exists_maximal_over_closedPt T E Q hQP
  have : y.IsPrime := hymax.isPrime
  obtain ⟨S, _, _, _, _, _, _, _, _, hSy, hflat, hpieces, φ', hφ', hsh'⟩ := sh_at (T := T) (E := E) y
  have hdiv : DivConst T S := hcl T S hT _ φ' hφ' hsh' hyT hyne
  obtain ⟨a, w, ha⟩ := hdiv (algebraMap E S g) (algebraMap E S g') s hs (by
    rw [← map_mul, hgg, ← IsScalarTower.algebraMap_apply])
  have : HenselianLocalRing O := hHen
  have : IsSepClosed (IsLocalRing.ResidueField O) := hSep
  obtain ⟨χ⟩ := specialisation_map E S O Q y hQy hSy rfl hflat hpieces
  refine ⟨a, Units.map χ.toRingHom.toMonoidHom w, ?_⟩
  have hχT : χ (algebraMap T S a) = algebraMap T O a := by
    rw [IsScalarTower.algebraMap_apply T E S, χ.commutes, hEO,
      IsScalarTower.algebraMap_apply T (Polynomial T) E, ψ.commutes,
      ← IsScalarTower.algebraMap_apply]
  calc b = ψ g := hg.symm
    _ = χ (algebraMap E S g) := by rw [χ.commutes, hEO]
    _ = algebraMap T O a * χ w := by rw [ha, map_mul, hχT]
    _ = _ := rfl

end GlobalTheory.VertUnits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPointsStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints : GlobalTheory.VertUnits.DivConstClosedPts → GlobalTheory.VertUnits.DivConstGeneric := by
  first | exact @GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | exact GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | (intros; apply GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibre
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits


open GlobalTheory.LocAcyc in
open CategoryTheory in
theorem divConstAll_of_divConstLocal : DivConstLocal → DivConstAll := by
  intro hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2
  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])
  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_under p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_under p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.under_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']
  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have key : DivConst T' O := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial

  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hle
  intro b c s hs hbc
  have hs' : algebraMap T T' s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  rw [IsScalarTower.algebraMap_apply T T' O] at hbc
  obtain ⟨a', w, hb⟩ := key b c _ hs' hbc
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
  obtain ⟨v, hv⟩ := hunit u
  refine ⟨a, v⁻¹ * w, ?_⟩
  rw [hb, Units.val_mul, ← mul_assoc]
  congr 1
  rw [Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a,
    IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.VertUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibreStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre : GlobalTheory.VertUnits.DivConstLocal → GlobalTheory.VertUnits.DivConstAll := by
  first | exact @GlobalTheory.VertUnits.divConstAll_of_divConstLocal | exact GlobalTheory.VertUnits.divConstAll_of_divConstLocal | (intros; apply GlobalTheory.VertUnits.divConstAll_of_divConstLocal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOrigin
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstClosedPts_of_divConstOrigin :
    GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  intro hKO
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith at hKO
  unfold GlobalTheory.VertUnits.DivConstClosedPts GlobalTheory.VertUnits.DivConstWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.LocAcyc.Translate.exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP'

end GlobalTheory.VertUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOriginStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin : GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  first | (exact @GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (exact GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnit
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem units_of_divConst (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    (h : DivConst T O)
    (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) :
    ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧
      (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O d) =
        algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O c) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  by_cases hL : Subsingleton (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
  · exact ⟨1, 1, 1, one_ne_zero, one_ne_zero, Subsingleton.elim _ _⟩
  rw [not_subsingleton_iff_nontrivial] at hL
  obtain ⟨⟨b, s₁⟩, hb⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨⟨c, s₂⟩, hc⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨t₁, ht₁, hs₁⟩ := s₁.2
  obtain ⟨t₂, ht₂, hs₂⟩ := s₂.2
  have h1 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ((s₁ : O) * (s₂ : O)) := by
    have hu : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) = 1 := u.mul_inv
    rw [← hb, ← hc, ← IsLocalization.mk'_mul] at hu
    have := IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) (s₁ * s₂)
    rw [hu, one_mul] at this
    rw [← this]; rfl
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).1 h1
  obtain ⟨t₀, ht₀, hm₀⟩ := m.2
  have hmem : t₀ * t₁ * t₂ ∈ nonZeroDivisors T :=
    mul_mem (mul_mem ht₀ ht₁) ht₂
  have hne : t₀ * t₁ * t₂ ≠ 0 := nonZeroDivisors.ne_zero hmem
  obtain ⟨a, w, hbw⟩ := h b ((m : O) * c) (t₀ * t₁ * t₂) hne (by
    rw [map_mul, map_mul, hm₀, hs₁, hs₂]
    calc b * ((m : O) * c) = (m : O) * (b * c) := by ring
      _ = (m : O) * ((s₁ : O) * (s₂ : O)) := hm
      _ = (m : O) * (s₁ : O) * (s₂ : O) := by ring)
  have key : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b := by
    rw [← hb]; exact IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b s₁
  refine ⟨a, t₁, w, ?_, nonZeroDivisors.ne_zero ht₁, ?_⟩
  · intro ha
    have h0 : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = 0 := by
      rw [key, hbw, ha]; simp
    exact (u.isUnit.mul (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s₁)).ne_zero h0
  · rw [hs₁, key, hbw, map_mul]

theorem main_of_divConstAll (hAll : DivConstAll) : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  intro T O _ _ _ _ _ _ _ _ _ hroot hO u
  obtain ⟨P, hP, φ, hφ, hsh⟩ :=
    GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hO
  exact units_of_divConst T O (hAll T O hroot P φ hφ hsh) u

end GlobalTheory.VertUnits

namespace GlobalTheory.VertUnits

theorem units_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) :=
  main_of_divConstAll (GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre (divConstLocal_of
    (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin) (GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin))))

end GlobalTheory.VertUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnitStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  first | (exact @GlobalTheory.VertUnits.units_eq_const_mul_unit) | (exact GlobalTheory.VertUnits.units_eq_const_mul_unit) | (intros; apply GlobalTheory.VertUnits.units_eq_const_mul_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPowEq
open Polynomial IsLocalRing

namespace GlobalTheory.UnitPowerExistence

theorem exists_unit_pow_eq (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hpos : 0 < q)
    (w : Oˣ) : ∃ v : Oˣ, v ^ q = w := by
  have hq0 : (q : ResidueField O) ≠ 0 := by
    have h := hq.map (residue O)
    rw [map_natCast] at h
    exact h.ne_zero
  have hw : residue O (w : O) ≠ 0 := (w.isUnit.map (residue O)).ne_zero
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (X ^ q - C (residue O (w : O)))
    (by rw [degree_X_pow_sub_C hpos]; exact_mod_cast hpos.ne') (separable_X_pow_sub_C _ hq0 hw)
  obtain ⟨b, rfl⟩ := residue_surjective a₀
  have hb : b ^ q - (w : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_sub, map_pow]
    simpa [IsRoot] using ha₀
  have hbu : IsUnit b := by
    by_contra hb'
    have h2 : b ^ q ∈ maximalIdeal O := Ideal.pow_mem_of_mem _ ((mem_maximalIdeal b).2 hb') q hpos
    have h3 : (w : O) ∈ maximalIdeal O := by simpa using sub_mem h2 hb
    exact (mem_maximalIdeal _).1 h3 w.isUnit
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ q - C (w : O)) (monic_X_pow_sub_C _ hpos.ne') b
    (by simpa using hb) (by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X]
      exact hq.mul (hbu.pow (q - 1)))
  have hapow : a ^ q = w := by simpa [IsRoot, sub_eq_zero] using ha
  have hau : IsUnit a := (isUnit_pow_iff hpos.ne').1 (hapow ▸ w.isUnit)
  exact ⟨hau.unit, Units.ext (by simpa using hapow)⟩

end GlobalTheory.UnitPowerExistence
end

open IsLocalRing

namespace GlobalTheory.LocAcycUnits

open Polynomial

theorem units_pow_surj_of_sepClosed (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hq0 : 0 < q) (w : Oˣ) :
    ∃ v : Oˣ, v ^ q = w := by
  first
  | exact @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | (apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq ..)

theorem units_localization_pow_surj : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ v : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, v ^ q = u := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hO u
  obtain ⟨_, hroot⟩ := hT
  obtain ⟨c, d, w, hc, hd, hu⟩ := GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit T O hroot hO u
  set L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have root : ∀ x : T, x ≠ 0 → ∃ y : T, y ≠ 0 ∧ y ^ q = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hroot (X ^ q - C x) (monic_X_pow_sub_C _ hq0.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hq0)
    have hyq : y ^ q = x := by simpa [sub_eq_zero] using hy
    refine ⟨y, ?_, hyq⟩
    rintro rfl; exact hx (by rw [← hyq, zero_pow hq0.ne'])
  have unitOf : ∀ x : T, x ≠ 0 → IsUnit (algebraMap O L (algebraMap T O x)) := fun x hx =>
    IsLocalization.map_units L (⟨algebraMap T O x,
      Algebra.mem_algebraMapSubmonoid_of_mem (⟨x, mem_nonZeroDivisors_of_ne_zero hx⟩ :
        nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  obtain ⟨c', hc', hcq⟩ := root c hc
  obtain ⟨d', hd', hdq⟩ := root d hd
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  obtain ⟨w', hw'⟩ := units_pow_surj_of_sepClosed O q hqO hq0 w
  have powU : ∀ (x y : T) (hx : x ≠ 0) (hy : y ≠ 0), y ^ q = x →
      (unitOf y hy).unit ^ q = (unitOf x hx).unit := by
    intro x y hx hy hxy
    apply Units.ext
    simp [← map_pow, hxy]
  have hMw : (Units.map (algebraMap O L).toMonoidHom w') ^ q = Units.map (algebraMap O L).toMonoidHom w := by
    rw [← map_pow, hw']
  have huU : u * (unitOf d hd).unit = (unitOf c hc).unit * Units.map (algebraMap O L).toMonoidHom w := by
    apply Units.ext; simpa using hu
  refine ⟨(unitOf c' hc').unit * Units.map (algebraMap O L).toMonoidHom w' * (unitOf d' hd').unit⁻¹, ?_⟩
  rw [mul_pow, mul_pow, inv_pow, powU c c' hc hc' hcq, powU d d' hd hd' hdq, hMw, ← huU]
  group

end GlobalTheory.LocAcycUnits
