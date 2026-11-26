module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DimFormula
open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.dimFormula :
    ∀ {R : Type} [CommRing R] [IsDomain R], HasBase R → IsNoetherianRing R ∧ ReciprocityTheory.CA.DimFormula R := by
  intro R _ _ h
  obtain ⟨A, _, _, i, hA, hinj, hf⟩ := h
  let : Algebra A R := i.toAlgebra
  have : Module.Finite A R := hf
  have : IsDomain A := hA.dom
  have : IsIntegrallyClosed A := hA.normal
  have : IsNoetherianRing A := hA.cm.1
  have hinj' : Function.Injective (algebraMap A R) := hinj
  have : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing A R
  refine ⟨this, fun q _ => ?_⟩
  set p := q.comap (algebraMap A R) with hp
  have : q.LiesOver p := ⟨rfl⟩
  have h1 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  have h2 : q.height ≤ p.height := by
    have e1 := PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum R)
    have e2 := PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum A)
    simp only at e1 e2
    rw [e1, e2]
    exact Order.height_le_height_apply_of_strictMono
      (fun P : PrimeSpectrum R => (⟨P.asIdeal.comap (algebraMap A R),
        inferInstance⟩ : PrimeSpectrum A))
      (fun P Q hPQ => Ideal.IsIntegral.comap_lt_comap (R := A)
        (show P.asIdeal < Q.asIdeal from hPQ)) _
  rw [le_antisymm h2 h1,
    ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A) q,
    hA.cm.height_add_ringKrullDim_quotient,
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj']
end

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.compDim :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R], CohenType R → ∀ (p q : Ideal R) (s : Finset R), p.IsPrime →
      q ∈ (p ⊔ Ideal.span (s : Set R)).minimalPrimes → ringKrullDim (R ⧸ p) ≤ ringKrullDim (R ⧸ q) + s.card := by
  classical
  intro R _ _ hC p q s hp hq
  have hpq : p ≤ q := le_sup_left.trans hq.1.2
  haveI := hp
  haveI := hq.1.1
  obtain ⟨-, hDF⟩ := dimFormula (hC p hp)
  set f := Ideal.Quotient.mk p
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ q := by rw [Ideal.mk_ker]; exact hpq
  haveI hQ : (q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hmin : q.map f ∈ (Ideal.span ((s.image f : Finset (R ⧸ p)) : Set (R ⧸ p))).minimalPrimes := by
    rw [Finset.coe_image, ← Ideal.map_span, Ideal.minimalPrimes_map_of_surjective hf]
    refine ⟨q, ?_, rfl⟩
    rw [Ideal.mk_ker, sup_comm]
    exact hq
  have hh : (q.map f).height ≤ s.card :=
    (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans
      (by exact_mod_cast Finset.card_image_le)
  have e := hDF (q.map f)
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)] at e
  rw [← e, add_comm]
  gcongr
  exact_mod_cast hh
