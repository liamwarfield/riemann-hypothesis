module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish (δ : DividedPowers J) (a : B) (N : ℕ)
    (h : ∀ n, N ≤ n → δ.dpow n a = 0) :
    _root_.GlobalTheory.Cris.dpExp δ a = ∑ n ∈ Finset.range N, δ.dpow n a := by
  unfold _root_.GlobalTheory.Cris.dpExp
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  exact hn (h n (not_lt.mp hlt))


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.IsNilDP.dpExp_add_eq_mul {δ : DividedPowers J}
    (h : _root_.GlobalTheory.Cris.IsNilDP δ) {a b : B} (ha : a ∈ J) (hb : b ∈ J) :
    _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b := by
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ x ∈ J, ∀ n, N ≤ n → δ.dpow n x = 0 := by
    intro x hx n hn
    simpa using hN [(n, x)] (by simpa using hx) (by simpa using hn)
  have hpair : ∀ i j, N ≤ i + j → δ.dpow i a * δ.dpow j b = 0 := by
    intro i j hij
    simpa using hN [(i, a), (j, b)] (by simp [ha, hb]) (by simpa using hij)
  let F : ℕ × ℕ → B := fun p => δ.dpow p.1 a * δ.dpow p.2 b
  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ (a + b) N (hvan _ (J.add_mem ha hb)),
    _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N (hvan a ha), _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ b N (hvan b hb),
    Finset.sum_mul_sum, ← Finset.sum_product' (f := fun i j => δ.dpow i a * δ.dpow j b)]
  have hfilter : ∑ p ∈ Finset.range N ×ˢ Finset.range N with p.1 + p.2 < N, F p =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, F p := by
    refine Finset.sum_filter_of_ne fun p _ hp => ?_
    by_contra hlt
    exact hp (hpair p.1 p.2 (not_lt.mp hlt))
  rw [← hfilter, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2) (fun p hp => by simpa using (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [δ.dpow_add ha hb]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨i, j⟩
  simp only [Finset.mem_range] at hn
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  omega


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.dpExp_add_and_natural (B B' : Type) [CommRing B] [CommRing B'] (J : Ideal B) (J' : Ideal B')
    (δ : DividedPowers J) (δ' : DividedPowers J') (h : _root_.GlobalTheory.Cris.IsNilDP δ) :
    (∀ a ∈ J, ∀ b ∈ J, _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b) ∧
      (∀ f : B →+* B', IsDPMorphism δ δ' f → ∀ a ∈ J,
        f (_root_.GlobalTheory.Cris.dpExp δ a) = _root_.GlobalTheory.Cris.dpExp δ' (f a)) := by
  refine ⟨fun a ha b hb => h.dpExp_add_eq_mul ha hb, fun f hf a ha => ?_⟩
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ n, N ≤ n → δ.dpow n a = 0 := by
    intro n hn
    simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  have hvan' : ∀ n, N ≤ n → δ'.dpow n (f a) = 0 := by
    intro n hn
    rw [← hf.map_dpow ha, hvan n hn, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N hvan, _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ' (f a) N hvan',
    map_sum]
  exact Finset.sum_congr rfl fun n _ => hf.map_dpow ha

end GlobalTheory.Cris
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

variable {R' : Type} [CommRing R'] {I : Ideal R'} {S : Scheme.{0}}

def crysAct (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) : O →+* Module.End R' (Crys κ t A) :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; push κ t (a.act x)
      map_one' := haveI := a.hom 1; (push_congr κ t a.one).trans (push_id κ t)
      map_mul' x y := by
        haveI := a.hom
        exact (push_congr κ t (a.mul x y)).trans (push_comp κ t _ _) }
    fun x y ↦ by
      haveI := a.hom
      haveI : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (push_congr κ t (a.add x y)).trans (push_mul κ t _ _)

theorem crysAct_apply (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) (x : O) (h : Crys κ t A) :
    crysAct κ t a x h = (haveI := a.hom x; push κ t (a.act x) h) := rfl

@[reducible] def tensorModOf {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) : Module (C ⊗[ℤ] B) H :=
  Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId C (Module.End C H)) ρ.toIntAlgHom
    fun r _ ↦ Algebra.commutes r _).toRingHom

theorem tensorModOf_tmul {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) (r : C) (x : B) (h : H) :
    (letI := tensorModOf ρ; (r ⊗ₜ[ℤ] x : C ⊗[ℤ] B) • h) = r • ρ x h := rfl

end GlobalTheory.HTSummand
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

def LabelsChar (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (θ : Tor p d →* ℂˣ) (x : Fbar p) : Prop :=
  x ^ (p ^ d - 1) = 1 ∧ ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = GlobalTheory.GLq.thetaOf L d x ((u : (Fbar p)ˣ) : Fbar p)

def LabelsTame (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ) : Prop :=
  ∀ u : (ZMod p)ˣ, GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod p) (Fbar p) (a : ZMod p))
    (algebraMap (ZMod p) (Fbar p) (u : ZMod p)) = ((χ u : ℂˣ) : ℂ)

def rootElt {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (y : Σ c : Cyc b, Fin (cycLen b c)) : Fbar p :=
  x y.1 ^ p ^ (y.2 : ℕ)

def IsRootPoly {r : ℕ} {b : Fin r → Fin r} (x : Cyc b → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, x c ^ (p ^ cycLen b c - 1) = 1) ∧ f.Monic ∧ Formalism.CyclotomicNorms.rootsBar f = Finset.univ.val.map (rootElt x)

def Labels (L : GlobalTheory.GLq.LabelDatum p) {r : ℕ} (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]) : Prop :=
  (∀ c, LabelsChar L (s.2 c) (x c)) ∧ IsRootPoly x f

def cuspOn {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) :
    GlobalTheory.GLq.Gn p (Fintype.card ι) → ℂ := fun y =>
  cuspChar θ ((y : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (ZMod p)).submatrix
    (Fintype.equivFin ι) (Fintype.equivFin ι))

end GlobalTheory.ParamLabel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Host

namespace GlobalTheory.MuConj

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_involutive (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

noncomputable def starAlg (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : E ≃ₐ[F] E :=
  { (starRingAut : E ≃+* E) with commutes' := hF }

theorem mem_above_iff (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P ≠ P) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = P.under (𝓞 F) ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  have hc : starAlg hF ≠ 1 := by
    intro h
    apply hP
    ext x
    have e : cO E x = x := by
      apply RingOfIntegers.ext
      exact congrArg (fun σ : E ≃ₐ[F] E => σ (x : E)) h
    rw [mem_conjP, e]
  rw [GlobalTheory.Mem.Chr.under_eq_iff_conjPl (starAlg hF) hr hc P Q, GlobalTheory.Mem.Chr.conjPl_iff_mem]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · ext y
    rw [mem_conjP]
    refine (h (cO E y) y ?_).symm
    exact (star_star (y : E)).symm
  · subst h
    intro x y hxy
    have e : y = cO E x := RingOfIntegers.ext hxy
    rw [e, mem_conjP, cO_cO]


omit [StarRing E] in
theorem valuation_up (Q : HeightOneSpectrum (𝓞 E))
    (h : ¬ (Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q.asIdeal ^ 2) (x : F) :
    Q.valuation E (algebraMap F E x) = (Q.under (𝓞 F)).valuation F x := by
  have : Q.asIdeal.LiesOver (Q.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have he : Ideal.ramificationIdx' (Q.under (𝓞 F)).asIdeal Q.asIdeal = 1 := by
    by_contra hne
    exact h ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hne)
  rw [← HeightOneSpectrum.valuation_liesOver E (Q.under (𝓞 F)) Q,
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Q.under (𝓞 F)).ne_bot, he, pow_one]

end General

theorem mem_divs_of_mem {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) {P : HeightOneSpectrum A}
    (h : a ∈ P.asIdeal) : P ∈ divs a := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h1 := Ideal.finite_factors (I := Ideal.span {a}) (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha)
    refine h1.subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  unfold divs
  rw [dite_eq_left hfin, Set.Finite.mem_toFinset]
  exact h

theorem g_notMem {X : Fields} {Pr : Primes X} (h : Pr.Ok) (P : HeightOneSpectrum (𝓞 X.E)) (h1 : P ∉ Pr.vGs)
    (h2 : conjPrime₂ P ∉ Pr.vGs) (i : Fin 2) : ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (h.g_prime i).ne_zero
  rw [← h.piG_norm i] at hm hg
  have hsub : ∀ Q, Q ∈ Pr.vG i → Q ∈ Pr.vGs := by
    intro Q hQ
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases i
    · exact Or.inl hQ
    · exact Or.inr hQ
  have hne : X.conjO (Pr.piG i) ≠ 0 := right_ne_zero_of_mul hg
  rcases P.isPrime.mem_or_mem hm with h3 | h3
  · refine h2 (hsub _ (mem_divs_of_mem hne ?_))
    show cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal
    rw [cO_cO]
    exact h3
  · exact h1 (hsub _ (mem_divs_of_mem hne h3))

end GlobalTheory.MuConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E]

theorem loc_eq_one_of_prod (ψ : HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ k : Eˣ, ∏ P ∈ S, ψ.locK P k = 1) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S)
    (x : (w.adicCompletion E)ˣ) : ψ.loc w x = 1 := by
  classical
  choose n hn using fun P => GlobalTheory.Mem.UnrAe.exists_levelLe ψ P
  obtain ⟨y, hy0, hyw, hyv⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E S w x (S.sup n + 1)
  have lev : ∀ P ∈ S, ∀ z : (P.adicCompletion E)ˣ,
      Valued.v ((z : P.adicCompletion E) - 1) ≤ WithZero.exp (-((S.sup n + 1 : ℕ) : ℤ)) → ψ.loc P z = 1 := by
    intro P hP z hz
    have h1 : Valued.v ((z : P.adicCompletion E) - 1) < Valued.v (1 : P.adicCompletion E) := by
      rw [map_one]
      refine lt_of_le_of_lt hz ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hu : IsUnitAt P z := by
      unfold IsUnitAt
      have e : (z : P.adicCompletion E) = ((z : P.adicCompletion E) - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ h1, map_one]
    refine hn P z hu (hz.trans ?_)
    rw [WithZero.exp_le_exp]
    have : n P ≤ S.sup n := Finset.le_sup hP
    omega
  have hS := h (Units.mk0 y hy0)
  rw [← Finset.mul_prod_erase S _ hw, Finset.prod_eq_one (fun P hP => ?_), mul_one] at hS
  · have e : ψ.loc w x = ψ.locK w (Units.mk0 y hy0) * (ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹))⁻¹ := by
      rw [map_mul, map_inv, mul_inv, inv_inv, ← mul_assoc]; simp [HChar.locK]
    have h2 : ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹) = 1 := lev w hw _ (by
      have := hyw
      exact this)
    rw [e, hS, h2, inv_one, mul_one]
  · obtain ⟨hPw, hPS⟩ := Finset.mem_erase.1 hP
    refine lev P hPS _ ?_
    have h3 := hyv P hPS hPw
    show Valued.v (algebraMap E (P.adicCompletion E) y - 1) ≤ _
    rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub]
    first
      | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (y - 1)).trans_le h3
      | (rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h3)

end GlobalTheory.CMVal.InvConj

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

theorem conjE_apply (x : E) : conjE x = IsCMField.complexConj E x := rfl

theorem conjE_symm_apply (x : E) : (conjE (E := E)).symm x = IsCMField.complexConj E x := by
  rw [RingEquiv.symm_apply_eq, conjE_apply, IsCMField.complexConj_apply_apply]

theorem under_plMap (j : E ≃+* E) (hj : ∀ x : maximalRealSubfield E, j (x : E) = x) (P : HeightOneSpectrum (𝓞 E)) :
    (plMap j P).under (OF E) = P.under (OF E) := by
  ext a
  have e : RingOfIntegers.mapRingEquiv j (algebraMap (OF E) (𝓞 E) a) = algebraMap (OF E) (𝓞 E) a :=
    RingOfIntegers.ext (hj (a : maximalRealSubfield E))
  show algebraMap (OF E) (𝓞 E) a ∈ (plMap j P).asIdeal ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal
  rw [← mem_plMap j P, e]

theorem mem_aboveF (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset]
  rfl

theorem prod_locK_conj (χ : HChar E) (hχ : TrivOnF χ) (v : HeightOneSpectrum (OF E)) (k : Eˣ) :
    ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (χ * transport conjE χ).locK P k = 1 := by
  have h1 : ∀ P, (χ * transport conjE χ).locK P k = χ.locK P k * (transport conjE χ).locK P k := fun P => rfl
  have hs : ∀ x : maximalRealSubfield E, (conjE (E := E)).symm (x : E) = x := fun x => by
    rw [conjE_symm_apply]; exact IsCMField.complexConj_apply_eq_self E x
  have hc : ∀ x : maximalRealSubfield E, (conjE (E := E)) (x : E) = x := fun x =>
    IsCMField.complexConj_apply_eq_self E x
  have h2 : ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (transport conjE χ).locK P k =
      ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, χ.locK P (Units.map (conjE (E := E)).toMonoidHom k) := by
    symm
    refine Finset.prod_nbij' (fun P => plMap (conjE (E := E)).symm P) (fun P => plMap conjE P) ?_ ?_ ?_ ?_ ?_
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hs P]; exact hP
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hc P]; exact hP
    · intro P _; exact plMap_plMap_symm conjE P
    · intro P _; exact plMap_symm_plMap conjE P
    · intro P _
      show χ.loc P (atFin P _) = (transport conjE χ).loc (plMap (conjE (E := E)).symm P) (atFin _ k)
      rw [transport_loc, locMap_atFin]
  rw [Finset.prod_congr rfl (fun P _ => h1 P), Finset.prod_mul_distrib, h2, ← Finset.prod_mul_distrib]
  have hN : (k : E) * conjE (k : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_mul, conjE_apply, IsCMField.complexConj_apply_apply, mul_comm]
  have hN0 : (⟨_, hN⟩ : maximalRealSubfield E) ≠ 0 := fun h0 =>
    mul_ne_zero k.ne_zero ((map_ne_zero _).2 k.ne_zero) (congrArg Subtype.val h0)
  have h3 := hχ.1 v (Units.mk0 _ hN0)
  unfold HChar.resFin at h3
  have hp : ∀ (s : Finset (HeightOneSpectrum (𝓞 E)))
      (f : HeightOneSpectrum (𝓞 E) → (maximalRealSubfield E)ˣ →* ℂˣ)
      (x : (maximalRealSubfield E)ˣ), (∏ P ∈ s, f P) x = ∏ P ∈ s, f P x := by
    intro s f x
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => simp only [Finset.prod_insert ha, MonoidHom.mul_apply, ih]
  rw [hp] at h3
  simp only [MonoidHom.comp_apply] at h3
  rw [← h3]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [← map_mul]
  exact congrArg _ (Units.ext rfl)

theorem loc_transport (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    (transport conjE χ).loc P x = (χ.loc P x)⁻¹ := by
  have h := loc_eq_one_of_prod (χ * transport conjE χ) _ (prod_locK_conj χ hχ (P.under (OF E)))
    (w := P) ((mem_aboveF _ P).2 rfl) x
  change χ.loc P x * (transport conjE χ).loc P x = 1 at h
  exact eq_inv_of_mul_eq_one_right h

theorem unrAt_inv_iff (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) :
    χ⁻¹.UnrAt P ↔ χ.UnrAt (plMap conjE P) := by
  rw [← transport_unrAt_iff]
  unfold HChar.UnrAt
  change (∀ x, IsUnitAt P x → (χ.loc P x)⁻¹ = 1) ↔ _
  simp only [loc_transport χ hχ]

theorem val_inv_eq (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap conjE P)) :
    χ⁻¹.val P = χ.val (plMap conjE P) := by
  rw [← transport_val conjE χ P h]
  show (χ.loc P _)⁻¹ = (transport conjE χ).loc P _
  rw [loc_transport χ hχ]

theorem eulerFactor_inv (χ : HChar E) (hχ : TrivOnF χ) (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    eulerFactor χ⁻¹ s P = eulerFactor χ s (plMap conjE P) := by
  unfold eulerFactor
  by_cases h : χ.UnrAt (plMap conjE P)
  · rw [if_pos ((unrAt_inv_iff χ hχ P).2 h), if_pos h, val_inv_eq χ hχ P h, absNorm_plMap]
  · rw [if_neg (fun h' => h ((unrAt_inv_iff χ hχ P).1 h')), if_neg h]

end GlobalTheory.CMVal.InvConj


open Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj in
theorem GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  intro E _ _ _ χ Λ hχ hL
  refine ⟨hL.1, fun s hs => ?_⟩
  let e : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E) :=
    ⟨plMap conjE, plMap (conjE (E := E)).symm, plMap_symm_plMap conjE, plMap_plMap_symm conjE⟩
  have he : eulerFactor χ⁻¹ s = eulerFactor χ s ∘ e := funext fun P => eulerFactor_inv χ hχ s P
  rw [he, Equiv.hasProd_iff]
  exact hL.2 s hs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxRealStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  first | exact @GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | exact GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF | (intros; apply GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartEvNmulPowSelf
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem chart_ev_nmul_pow_self : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (i : Fin d), c.ev n (nmul c.μ (p ^ n) i) = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n i
  rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegral
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O]

theorem eq_zero_of_forall_dvd [IsHausdorff (Ideal.span {(p : O)}) O] (x : O)
    (h : ∀ n : ℕ, (p : O) ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact h n

variable {G : PDivGroup p O}

theorem exists_form (n : ℕ) (w : G.dual.omega) :
    ∃ φ : CartierDual O (G.A n), PDiv.dUnit (R := O) φ = w.1 n ∧ φ 1 = 0 := by
  obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
  refine ⟨φ - algebraMap O _ (φ 1), ?_, ?_⟩
  · change AugCot.d _ (φ - algebraMap O _ (φ 1)) = _
    rw [map_sub, AugCot.d_algebraMap, sub_zero]
    exact hφ
  · have h1 : (algebraMap O (CartierDual O (G.A n)) (φ 1)) 1 = φ 1 := by
      rw [Algebra.algebraMap_eq_smul_one]
      change φ 1 * Coalgebra.counit (R := O) (1 : G.A n) = _
      rw [Bialgebra.counit_one, mul_one]
    change φ 1 - (algebraMap O (CartierDual O (G.A n)) (φ 1)) 1 = 0
    rw [h1, sub_self]

theorem lie_eq_zero [IsHausdorff (Ideal.span {(p : O)}) O] (l : G.dual.Lie)
    (h : ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)), PDiv.dUnit (R := O) φ = w.1 n →
      φ 1 = 0 → (p : O) ^ n ∣ l w) : l = 0 :=
  LinearMap.ext fun w => eq_zero_of_forall_dvd _ fun n => by
    obtain ⟨φ, hφ, h1⟩ := exists_form n w
    exact h n w φ hφ h1

variable {σ τ R : Type} [CommRing R] [Finite σ]

theorem constantCoeff_subst_of {a : σ → MvPowerSeries τ R} (ha0 : ∀ i, constantCoeff (a i) = 0)
    (f : MvPowerSeries σ R) : constantCoeff (subst a f) = constantCoeff f := by
  have hs := hasSubst_of_constantCoeff_zero ha0
  have hg : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  calc constantCoeff (subst a f)
      = constantCoeff (subst a (C (constantCoeff f) + (f - C (constantCoeff f)))) := by rw [← e]
    _ = constantCoeff f := by
      have hC : (C (constantCoeff f) : MvPowerSeries σ R) =
          algebraMap R (MvPowerSeries σ R) (constantCoeff f) := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha0 hg, add_zero,
        ← coe_substAlgHom hs, hC, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
      simp

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_subst_eq (n : ℕ) (a : Fin d → MvPowerSeries (Fin d) O)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (hz : ∀ i, c.ev n (a i) = 0)
    (s : MvPowerSeries (Fin d) O) :
    ∃ y : G.A n, c.ev n (subst a s) = algebraMap O (G.A n) (constantCoeff s) + (p : O) ^ n • y := by
  have hs := hasSubst_of_constantCoeff_zero ha0
  obtain ⟨N, hN⟩ := (c.isEval n).2 n
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N) s with hP
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N →
      coeff α (subst a (s - (P : MvPowerSeries (Fin d) O))) = 0 := by
    have h1 : (N : ℕ∞) ≤ (s - (P : MvPowerSeries (Fin d) O)).order := by
      refine nat_le_order fun α hα => ?_
      rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
      intro i
      have : α i ≤ α.degree := Finsupp.le_degree i α
      have h' : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N) i = N := by simp
      rw [h']
      omega
    have h2 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
      le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
    have h3 := le_order_subst hs (s - (P : MvPowerSeries (Fin d) O))
    intro α hα
    apply coeff_of_lt_order
    calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
      _ = 1 * (N : ℕ∞) := (one_mul _).symm
      _ ≤ (⨅ i, (a i).order) * (s - (P : MvPowerSeries (Fin d) O)).order := mul_le_mul' h2 h1
      _ ≤ _ := h3
  obtain ⟨y, hy⟩ := hN _ hT
  refine ⟨y, ?_⟩
  have e : subst a s = subst a (P : MvPowerSeries (Fin d) O) +
      subst a (s - (P : MvPowerSeries (Fin d) O)) := by
    rw [← subst_add hs, add_sub_cancel]
  have hz' : (fun i => c.ev n (a i)) = 0 := funext hz
  rw [e, map_add (f := _), subst_coe, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, hy, hz',
    MvPolynomial.aeval_zero, Algebra.smul_def, map_pow, map_natCast, MvPolynomial.constantCoeff_eq,
    hP, coeff_trunc', if_pos (by simp), coeff_zero_eq_constantCoeff_apply]

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {E : Type} [CommRing E] [Algebra O E]

theorem lie_eq_zero_of_integral [IsHausdorff (Ideal.span {(p : O)}) O]
    (hz : ∀ n i, c.ev n (nmul c.μ (p ^ n) i) = 0) (s0 : MvPowerSeries (Fin d) O)
    (l : G.dual.Lie) (h : c.IsLie (map (algebraMap O E) s0) l) : l = 0 := by
  refine lie_eq_zero l fun n w φ hφ h1 => ?_
  have ha0 : ∀ i, constantCoeff (nmul c.μ (p ^ n) i) = 0 :=
    QLogDefect.constantCoeff_nmul c.isLaw.const _
  have hs := hasSubst_of_constantCoeff_zero ha0
  have hD : map (algebraMap O E) (((p ^ n : ℕ) : O) • s0 - subst (nmul c.μ (p ^ n)) s0) =
      defect c.μ (p ^ n) (map (algebraMap O E) s0) := by
    rw [defect, map_sub, map_subst hs]
    congr 1
    ext α
    simp [coeff_map]
  have h2 := h.2 n w φ _ hφ hD
  obtain ⟨y, hy⟩ := ev_subst_eq c n _ ha0 (hz n) s0
  have hφa : ∀ k : O, φ (algebraMap O (G.A n) k) = 0 := fun k => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  have e : φ (c.ev n (((p ^ n : ℕ) : O) • s0 - subst (nmul c.μ (p ^ n)) s0)) =
      (p : O) ^ n * (φ (c.ev n s0) - φ y) := by
    rw [map_sub, map_smul, hy, map_sub, map_smul, map_add (f := _), map_smul, hφa, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e] at h2
  have h3 := dvd_add h2 (dvd_mul_right ((p : O) ^ n) (φ (c.ev n s0) - φ y))
  rwa [sub_add_cancel] at h3

theorem quasiLogarithmDefect_eq_zero_of_coboundary (f : MvPowerSeries (Fin d) E) (hf : cob1 (up E c.μ) f = 0) (k : ℕ) :
    defect c.μ k f = 0 := by
  have hμ := c.isLaw.const
  have hM : ∀ j, constantCoeff (up E c.μ j) = 0 := fun j => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ j,
      map_zero]
  have hc : constantCoeff f = 0 := by
    have h := congrArg constantCoeff hf
    rw [cob1, inL, inR, map_sub, map_sub, constantCoeff_subst_of hM,
      constantCoeff_subst_of (fun _ => constantCoeff_X _),
      constantCoeff_subst_of (fun _ => constantCoeff_X _), map_zero] at h
    linear_combination -h
  induction k with
  | zero =>
    have h0 : up E (nmul c.μ 0) = 0 := by funext i; simp [up, nmul]
    rw [defect, h0, Nat.cast_zero, zero_smul, zero_sub, subst_zero_of_constantCoeff_zero hc,
      neg_zero]
  | succ k ih =>
    rw [QLogDefect.defect_succ c.μ hμ k f, ih, hf]
    have hE : ∀ j, constantCoeff (Sum.elim (up E (nmul c.μ k))
        (fun i => (X i : MvPowerSeries (Fin d) E)) j) = 0 := by
      rintro (j | j)
      · simp only [Sum.elim_inl, up]
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
          QLogDefect.constantCoeff_nmul hμ k j, map_zero]
      · simp
    rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero hE), map_zero, sub_zero]

theorem lie_eq_zero_of_cob1 [IsHausdorff (Ideal.span {(p : O)}) O] (f : MvPowerSeries (Fin d) E)
    (hf : cob1 (up E c.μ) f = 0) (l : G.dual.Lie) (h : c.IsLie f l) : l = 0 := by
  refine lie_eq_zero l fun n w φ hφ _ => ?_
  have h2 := h.2 n w φ 0 hφ (by rw [map_zero, quasiLogarithmDefect_eq_zero_of_coboundary c f hf])
  rwa [map_zero, map_zero, sub_zero] at h2

theorem exists_of_in {σ : Type} {f : MvPowerSeries σ E} (h : In (⊤ : Ideal O) f) :
    ∃ s : MvPowerSeries σ O, map (algebraMap O E) s = f := by
  choose b _ hb using h
  refine ⟨(show MvPowerSeries σ O from fun α => b α), ?_⟩
  ext α
  rw [coeff_map, hb α]
  rfl

theorem defect_add_smul (f g : MvPowerSeries (Fin d) E) (a : E) (k : ℕ) :
    defect c.μ k (f + a • g) = defect c.μ k f + a • defect c.μ k g := by
  have hU : ∀ j, constantCoeff (up E (nmul c.μ k) j) = 0 := fun j => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      QLogDefect.constantCoeff_nmul c.isLaw.const _ j, map_zero]
  have hsub := hasSubst_of_constantCoeff_zero hU
  simp only [defect]
  rw [subst_add hsub, subst_smul hsub, smul_add, smul_sub, smul_comm ((k : ℕ) : E) a g]
  abel

theorem isLie_add_smul (hinj : Function.Injective (algebraMap O E))
    {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (a : O)
    (hf : c.IsLie f l) (hg : c.IsLie g l') :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') := by
  have hmap : ∀ sf sg : MvPowerSeries (Fin d) O, map (algebraMap O E) (sf + a • sg) =
      map (algebraMap O E) sf + algebraMap O E a • map (algebraMap O E) sg := fun sf sg => by
    ext α
    simp [coeff_map]
    exact (Algebra.smul_def _ _).symm
  refine (c.isLie_iff hinj _ _).2 fun n => ?_
  obtain ⟨sf, hsf⟩ := exists_of_in (hf.1 n)
  obtain ⟨sg, hsg⟩ := exists_of_in (hg.1 n)
  refine ⟨sf + a • sg, by rw [hmap, defect_add_smul, hsf, hsg], fun w φ hφ => ?_⟩
  have h1 := hf.2 n w φ sf hφ hsf
  have h2 := hg.2 n w φ sg hφ hsg
  rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add (f := _),
    map_smul, smul_eq_mul]
  have h3 := dvd_add h1 (dvd_mul_of_dvd_right h2 a)
  convert h3 using 1
  ring

theorem isLie_add [Fact p.Prime] (hF : IsFrame p E (RingHom.id O))
    (_hL : IsLift (RingHom.id O) c.μ) {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (a : O)
    (hf : c.IsLie f l) (hg : c.IsLie g l') (_qf : QL c.μ ⊤ f) (_qg : QL c.μ ⊤ g) :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
  isLie_add_smul c hF.inj a hf hg

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' → (QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l')) ∧ ((∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f g l l' a hf hg
  have hz : ∀ n i, c.ev n (nmul c.μ (p ^ n) i) = 0 := fun n i => GlobalTheory.chart_ev_nmul_pow_self p C v O hv G d c n i
  have hL : IsLift (RingHom.id O) c.μ :=
    ⟨c.isLaw.const, c.isLaw.unit, c.isLaw.comm, by simpa using c.isLaw⟩
  refine ⟨fun qf qg => isLie_add c hF hL a hf hg qf qg, ?_, fun h => lie_eq_zero_of_cob1 c f h l hf⟩
  rintro ⟨s, rfl⟩
  exact lie_eq_zero_of_integral c hz s l hf

end GlobalTheory.LieLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' → (QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l')) ∧ ((∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  first | exact @GlobalTheory.LieLin.main | exact GlobalTheory.LieLin.main | (intros; apply GlobalTheory.LieLin.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalks
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

attribute [-instance] CategoryTheory.Limits.hasPullbackHorizPaste

theorem qcqsOver_sch {X S : Scheme.{0}} (r : X ⟶ S) [QuasiCompact r] [QuasiSeparated r] : QcqsOver (sch.map r) :=
  fun _ => ⟨X, r, Iso.refl _, inferInstance, inferInstance, by simp [sch]⟩

theorem isPullback_sch_comp {Y X S T : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (s : T ⟶ S) :
    IsPullback (sch.map (pullback.fst (f ≫ p) s)) (sch.map (pullback.snd (f ≫ p) s)) (sch.map f ≫ sch.map p) (sch.map s) := by
  have h := (IsPullback.of_hasPullback (f ≫ p) s).map sch
  rw [Functor.map_comp] at h
  exact h

set_option synthInstance.maxHeartbeats 200000

theorem bcMap_app_fst {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) (U : Over S) :
    (bcMap α p).app U ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E') = pullback.fst (α ≫ p) (sch.map U.hom) ≫ α :=
  pullback.lift_fst _ _ _

theorem bcMap_app_snd {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) (U : Over S) :
    (bcMap α p).app U ≫ (pullback.snd p (sch.map U.hom) : (bc p).obj U ⟶ _) = pullback.snd (α ≫ p) (sch.map U.hom) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem bcMap_sch_square {Y X S T : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (s : T ⟶ S) :
    (isPullback_sch_comp f p s).isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s) =
      sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫
        ((IsPullback.of_hasPullback p s).map sch).isoPullback.hom := by
  let P1 := isPullback_sch_comp f p s
  let P2 := (IsPullback.of_hasPullback p s).map sch
  apply pullback.hom_ext
  · have l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.fst (sch.map p) (sch.map s) =
        sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f := by
      refine (Category.assoc _ _ _).trans ?_
      erw [bcMap_app_fst]
      rw [← Category.assoc]
      exact congrArg (· ≫ sch.map f) P1.isoPullback_hom_fst
    have r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫
        pullback.fst (sch.map p) (sch.map s) = sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f := by
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
    exact l.trans r.symm
  · have l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.snd (sch.map p) (sch.map s) =
        sch.map (pullback.snd (f ≫ p) s) := by
      refine (Category.assoc _ _ _).trans ?_
      erw [bcMap_app_snd]
      exact P1.isoPullback_hom_snd
    have r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫
        pullback.snd (sch.map p) (sch.map s) = sch.map (pullback.snd (f ≫ p) s) := by
      rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp]
      exact congrArg sch.map ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
    exact l.trans r.symm

theorem eqv_sch_of_stalks : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (Y X S : Scheme.{0}) (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) F) → Eqv R (sch.map f) F := by
  intro R _ F hF Y X S f p _ _ _ _ hst
  refine GlobalTheory.T.equiv_of_stalkwise_base_change R F S (sch.obj Y) (sch.obj X) (sch.map f) (sch.map p) hF ?_ (qcqsOver_sch p) ?_
  · rw [← Functor.map_comp]; exact qcqsOver_sch (f ≫ p)
  · intro O _ s hs
    have hb := eqv_basic R F
    have hsq := bcMap_sch_square f p s
    have h1 := hb.1 _ _ (isPullback_sch_comp f p s).isoPullback.hom inferInstance
    have h2 := (hb.2.1 _ _ _ _ _).1 (hst O s hs) (hb.1 _ _ ((IsPullback.of_hasPullback p s).map sch).isoPullback.hom inferInstance)
    rw [← hsq] at h2
    exact (hb.2.1 _ _ _ _ _).2.1 h1 h2

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalksStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (Y X S : Scheme.{0}) (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) F) → Eqv R (sch.map f) F := by
  first
  | exact @GlobalTheory.EtC.eqv_sch_of_stalks
  | exact GlobalTheory.EtC.eqv_sch_of_stalks
  | (intros; apply GlobalTheory.EtC.eqv_sch_of_stalks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem isEtLevOver_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T T' : Over S) (l : D.La → (T ⟶ o.A)) (f : T' ⟶ T), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => f ≫ l y) := by
  intro p _ D R _ b N S s o w0 r T T' l f h
  obtain ⟨hadd, hlin, hker, hgeo⟩ := h
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ?_⟩
  · simp only [hadd, MonObj.comp_mul]
  · simp only [hlin, Category.assoc]
  · simp only [hker x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hgeo k (x ≫ f.left)
    let e : Over.mk (x ≫ T'.hom) ≅ Over.mk ((x ≫ f.left) ≫ T.hom) :=
      Over.isoMk (Iso.refl _) (by simp [Over.w f])
    have hfac : (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ f =
        e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) := by
      ext; simp [e]
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h1 : e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) ≫ l y = 1 := by
        rw [← Category.assoc, ← hfac, Category.assoc]; exact hy
      have h2 := congrArg (fun z => e.inv ≫ z) h1
      simpa [MonObj.comp_one] using h2
    · obtain ⟨y, hy⟩ := hsurj (e.inv ≫ g) (fun c hc => by
        exact (Category.assoc _ _ _).trans (by rw [hg c hc, MonObj.comp_one]))
      refine ⟨y, ?_⟩
      rw [← Category.assoc, hfac, Category.assoc, hy, Iso.hom_inv_id_assoc]

end GlobalTheory.UPel.HT.EtLev
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_level_base_change : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T T' : Over S) (l : D.La → (T ⟶ o.A)) (f : T' ⟶ T), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => f ≫ l y) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaEquivariantFrobenius
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem etale_of_killed_tangent_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  intro p _ D R _ b N w0 r S _ s o H i hfin hflat hkill hrep htan
  haveI := hfin
  haveI := hflat
  haveI : LocallyOfFinitePresentation H.hom := inferInstance
  have hinv : ∀ {T : Over S} (a : T ⟶ o.A) (f : o.A ⟶ o.A) [IsMonHom f], a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro T a f _
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_comp, inv_mul_cancel, one_comp]
  haveI : FormallyUnramified H.hom := by
    refine TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw => ?_
    let x : Sp k ⟶ S := TangentCrit.dualPt k ≫ w ≫ H.hom
    let W : epsPtR x ⟶ H := Over.homMk w hw
    let U : epsPtR x ⟶ H := Over.homMk (TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w)
      (by simp only [Category.assoc]; rfl)
    let e : Over.mk x ⟶ epsPtR x := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (TangentCrit.dualPt_dualBase_assoc k _)
    have heU : e ≫ W = e ≫ U := by
      ext1
      exact (TangentCrit.dualPt_dualBase_assoc k (TangentCrit.dualPt k ≫ w)).symm
    have hv : (W ≫ i) * (U ≫ i)⁻¹ = 1 := by
      refine htan k x _ ?_ ?_
      · have h1 : e ≫ ((W ≫ i) * (U ≫ i)⁻¹) = 1 := by
          rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, heU, mul_inv_cancel]
        exact congrArg (fun q => q.left) h1
      · intro c hc
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        rw [mul_comp, hinv, Category.assoc, Category.assoc, hkill c hc, comp_one, comp_one, inv_one, _root_.mul_one]
    have hWU : W ≫ i = U ≫ i := mul_inv_eq_one.1 hv
    have hk : ∀ c ∈ w0 ^ r, (W ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, hkill c hc, comp_one]
    obtain ⟨y, -, hy⟩ := hrep _ (W ≫ i) hk
    have hW := hy W rfl
    have hU := hy U hWU.symm
    exact congrArg (fun q => q.left) (hW.trans hU.symm)
  exact Etale.of_formallyUnramified_of_flat H.hom

end GlobalTheory.UPel.HT.EtLev
end
