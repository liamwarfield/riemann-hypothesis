module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.LvT.KerLat

theorem rowGen_diag_monomial_one (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (d : Fin r × Fin n →₀ ℕ) :
    rowGen R a a (monomial d 1) =
      (1 + Polynomial.X) ^ (Finsupp.weight (rowW r n) d a) * Polynomial.C (monomial d 1) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have e : (monomial (f + g) (1 : R) : MvPolynomial (Fin r × Fin n) R) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, map_add (f := _), Pi.add_apply, pow_add, map_mul]
    ring
  | single v c =>
    obtain ⟨b, s⟩ := v
    rw [← X_pow_eq_monomial, map_pow, map_pow]
    unfold rowGen
    rw [aeval_X]
    by_cases h : b = a
    · subst h
      have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) b = c := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index]
      rw [e, ← mul_pow]
      simp only [if_true]
      congr 1
      ring
    · have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) a = 0 := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index, Ne.symm h]
      rw [e]
      simp [h]

theorem rowGen_diag_homog (R : Type) [CommRing R] {r n : ℕ} (μ : Fin r → ℕ) (a : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    rowGen R a a f = (1 + Polynomial.X) ^ (μ a) * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : (monomial d (AddMonoidAlgebra.coeff f d) : MvPolynomial (Fin r × Fin n) R) = AddMonoidAlgebra.coeff f d • monomial d 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, rowGen_diag_monomial_one, hf (mem_support_iff.mp hd), ← mul_smul_comm,
    Polynomial.smul_C]

theorem rowDiv_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ →
    (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧
      ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  intro R _ r n μ f hf
  refine ⟨fun a b k => ?_, fun a k => ?_⟩
  · have hZ : IsWeightedHomogeneous (rowZ r n) f (fun i => (μ i : ℤ)) := by
      intro d hd
      funext i
      rw [weight_rowZ, hf hd]
    have h := rowDiv_shift R _ a b k f hZ
    refine ⟨fun i => ((((fun i => (μ i : ℤ)) + k • (Pi.single a 1 - Pi.single b 1) : Fin r → ℤ)) i).toNat,
      fun d hd => ?_⟩
    funext i
    rw [← h hd, weight_rowZ, Int.toNat_natCast]
  · unfold rowDiv
    rw [rowGen_diag_homog R μ a f hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow, nsmul_eq_mul]

end GlobalTheory.ValCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeightStatement
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ → (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧ ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  first | exact @GlobalTheory.ValCmp.rowDiv_rowWeight | exact GlobalTheory.ValCmp.rowDiv_rowWeight | (intros; apply GlobalTheory.ValCmp.rowDiv_rowWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeInterior
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem _root_.GlobalTheory.phiT_add_smul_homAt (K : Type) [Field K]
    {ST SG SG' S : Finset (HeightOneSpectrum (𝓞 E))}
    (d : _root_.Formalism.L2.Col.Deco E a ST SG) (d' : _root_.Formalism.L2.Col.Deco E b ST SG') (hd' : d'.Ok) (hS : ST ⊆ S) (c : 𝓞 E)
    (hc : ∀ P : ST, c ∈ P.1.asIdeal) (x y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S d.N d'.N) :
    _root_.Formalism.L2.Col.phiT K d d' (x + c • y₀) = _root_.Formalism.L2.Col.phiT K d d' x := by
  unfold _root_.Formalism.L2.Col.phiT
  have key : ∀ P : ST, ∀ y ∈ d.at P,
      ((x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
        (x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) := by
    intro P y hyP
    have hy0 : y₀ y ∈ d'.at P := hy P.1 (hS P.2) y hyP
    have hcy : c • y₀ y ∈ d'.at P := Submodule.smul_mem _ c hy0
    have hf0 : d'.f P (c • y₀ y) = 0 := by
      rw [hd'.f_smul P c _ hy0, Ideal.Quotient.eq_zero_iff_mem.2 (hc P), zero_mul]
    have happ : (x + c • y₀) y = x y + c • y₀ y := rfl
    rw [happ, Submodule.add_mem_iff_left _ hcy]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h2, hd'.f_add P _ h1 _ hcy, hf0, add_zero]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hd'.f_add P _ h1 _ hcy, hf0, add_zero, h2]⟩
  have hiff : (∀ P : ST, ∀ y ∈ d.at P,
      (x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P, x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) :=
    forall_congr' fun P => forall₂_congr fun y hyP => key P y hyP
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

omit [NumberField E] [StarRing E] in
theorem _root_.GlobalTheory.inFr_add (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (x y : _root_.Formalism.L2.Col.HomE E a b) :
    _root_.Formalism.L2.Col.inFr f f' (x + y) = _root_.Formalism.L2.Col.inFr f f' x + _root_.Formalism.L2.Col.inFr f f' y := by
  unfold _root_.Formalism.L2.Col.inFr
  rw [LinearMap.add_comp, LinearMap.comp_add]

theorem _root_.GlobalTheory.intAt_inFr_smul_homAt {S : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E a)}
    {N' : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E b)} {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ S)
    (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (hf : ∀ x, f x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ _root_.Formalism.L2.Col.stdAt E a P)
    (hf' : ∀ x, f' x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' ↔ x ∈ _root_.Formalism.L2.Col.stdAt E b P)
    (c r : 𝓞 E) (e : E) (he : e ≠ 0) (hc : algebraMap (𝓞 E) E c = e * algebraMap (𝓞 E) E r)
    (y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S N N') (s : Fin a) (l : Fin b) :
    _root_.Formalism.L2.Col.IntAt P (e⁻¹ * _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l) := by
  have hv : (Pi.single s 1 : _root_.Formalism.L2.Col.Sp E a) ∈ _root_.Formalism.L2.Col.stdAt E a P := by
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    rw [one_smul]
    refine Submodule.mem_pi.2 fun i _ => ?_
    by_cases h : i = s
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  have hz : y₀ (f (Pi.single s 1)) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := hy P hP _ ((hf _).2 hv)
  have hw : f'.symm (y₀ (f (Pi.single s 1))) ∈ _root_.Formalism.L2.Col.stdAt E b P :=
    (hf' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hz)
  obtain ⟨t, ht, htw⟩ := hw
  have hl : (t • f'.symm (y₀ (f (Pi.single s 1)))) l ∈ (1 : Submodule (𝓞 E) E) :=
    Submodule.mem_pi.1 htw l (Set.mem_univ l)
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hl
  have hval : _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l =
      algebraMap (𝓞 E) E c * f'.symm (y₀ (f (Pi.single s 1))) l := by
    show (f'.symm (c • y₀ (f (Pi.single s 1)))) l = _
    rw [← algebraMap_smul E c (y₀ (f (Pi.single s 1))), map_smul, Pi.smul_apply, smul_eq_mul]
  unfold _root_.Formalism.L2.Col.IntAt
  refine ⟨r * r', t, ht, ?_⟩
  rw [hval, hc, map_mul, hr', Pi.smul_apply, Algebra.smul_def]
  calc _ = (e⁻¹ * e) * (algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E r *
        f'.symm (y₀ (f (Pi.single s 1))) l)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ he, one_mul]; ring

end General

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumFibreEqSumOrbits
noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

theorem sum_inv_eq_sum_orbits {K M H X : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group H] [Finite H]
    [MulAction H X] [Fintype X] [Fintype (MulAction.orbitRel.Quotient H X)] (F : X → M)
    (hF : ∀ (g : H) (x : X), F (g • x) = F x) :
    ((Nat.card H : K))⁻¹ • ∑ x, F x =
      ∑ q : MulAction.orbitRel.Quotient H X, ((Nat.card (MulAction.stabilizer H q.out) : K))⁻¹ • F q.out := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmem : ∀ x : X, (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q ↔ x ∈ MulAction.orbit H q.out := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' q]
    rw [Quotient.eq'']
    exact MulAction.orbitRel_apply
  rw [Finset.sum_congr rfl (g := fun _ => F q.out) (by
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (Finset.mem_filter.1 hx).2
    exact hF g _), Finset.sum_const]
  have hc : (Finset.univ.filter fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q).card
      = Nat.card (MulAction.orbit H q.out) := by
    symm
    refine Nat.subtype_card _ fun x => ?_
    rw [Finset.mem_filter, ← hmem]
    simp
  have hm : Nat.card (MulAction.orbit H q.out) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H q.out)
  have h1 : (Nat.card (MulAction.stabilizer H q.out) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [hc, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  have : (Nat.card (MulAction.orbit H q.out) : K) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    exact_mod_cast congrArg (Nat.cast : ℕ → K) hm
  field_simp
  rw [← this]

theorem card_stabilizer_smul {G D : Type} [Group G] [MulAction G D] (g : G) (d : D) :
    Nat.card (MulAction.stabilizer G (g • d)) = Nat.card (MulAction.stabilizer G d) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := g) (a := d) (b := g • d) rfl).toEquiv).symm

theorem sum_fibre_eq_sum_orbits {K M G D D₀ : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group G]
    [MulAction G D] [MulAction G D₀] (pr : D → D₀) (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)
    [Fintype (MulAction.orbitRel.Quotient G D₀)] [Fintype (MulAction.orbitRel.Quotient G D)]
    (hs : ∀ x : D₀, Finite (MulAction.stabilizer G x)) [∀ x : D₀, Fintype (fibre pr hpr x)] (F : D → M)
    (hF : ∀ (g : G) (x : D), F (g • x) = F x) :
    ∑ c : MulAction.orbitRel.Quotient G D₀, ((Nat.card (MulAction.stabilizer G c.out) : K))⁻¹ •
        ∑ y : fibre pr hpr c.out, F y =
      ∑ q : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G q.out) : K))⁻¹ • F q.out := by
  classical
  let _ : ∀ x : D₀, Fintype (MulAction.orbitRel.Quotient (MulAction.stabilizer G x) (fibre pr hpr x)) :=
    fun x => Fintype.ofFinite _
  rw [← (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hs c.out
  rw [sum_inv_eq_sum_orbits (H := MulAction.stabilizer G c.out) (fun y : fibre pr hpr c.out => F y)
    (fun g y => hF (g : G) (y : D))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩
      = (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) : MulAction.orbitRel.Quotient G D) := by
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  obtain ⟨g, hg⟩ : ∃ g : G, g • ((q.out : fibre pr hpr c.out) : D) =
      ((orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩).out := by
    rw [h1]
    exact Quotient.exact' (Quotient.out_eq' (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) :
      MulAction.orbitRel.Quotient G D))
  rw [← hg, hF, card_stabilizer_smul, fibre_card_stab]

section Pairs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S S₁ : GSD K} {Y : Cpl S}

def cplFibreEquiv (Y : Cpl S) (x : S.D) :
    fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x ≃ Y.ys x where
  toFun p := ⟨p.1.1.2, by
    have h1 : p.1.1.1 = x := p.2
    exact (congrArg (fun z => p.1.1.2 ∈ Y.ys z) h1).mp p.1.2⟩
  invFun y := ⟨⟨(x, y.1), y.2⟩, rfl⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext (show p.1.1.1 = x from p.2).symm rfl))
  right_inv _ := rfl

theorem cplGSD_ok (Y : Cpl S) (h : S.Ok) : (cplGSD S Y).Ok := by
  refine {
    fin_orb := ?_
    fin_stab := ?_
    nab_smul := fun g d => h.nab_smul g d.1.1
    del_smul := fun g d => h.del_smul g d.1.1
    inv := h.inv }
  · have := h.fin_orb
    have : ∀ x : S.D, Finite (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
      have := (Y.fin x).to_subtype
      Finite.of_equiv _ (cplFibreEquiv Y x).symm
    exact Finite.of_equiv _ (orbitsFib (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) Quotient.out
      (fun c => Quotient.out_eq' c))
  · intro d
    have := h.fin_stab d.1.1
    have hle : MulAction.stabilizer S.G d ≤ MulAction.stabilizer S.G d.1.1 := fun g hg =>
      congrArg (fun p : Y.Pts => p.1.1) hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)

def cplKer1 (A : CplKer S₀ S S₁ Y) : ClsKer S₀ (cplGSD S Y) where
  k d₀ d := A.k1 d₀ d.1.1 d.1.2
  equiv g₀ g d₀ d := A.equiv1 g₀ g d₀ d.1.1 d.1.2

def cplKer2 (A : CplKer S₀ S S₁ Y) : ClsKer (cplGSD S Y) S₁ where
  k d d₁ := A.k2 d.1.1 d.1.2 d₁
  equiv g g₁ d d₁ := A.equiv2 g g₁ d.1.1 d.1.2 d₁

theorem cpl_comp_k (A : CplKer S₀ S S₁ Y) (h : S.Ok) (d₀ : S₀.D) (d₁ : S₁.D) :
    (A.comp h S.outSec).k d₀ d₁ =
      letI := (cplGSD_ok Y h).fintypeCl
      ∑ q : (cplGSD S Y).Cl, ((((cplGSD S Y).toCSDOf (cplGSD_ok Y h) (cplGSD S Y).outSec).wt q : K))⁻¹ •
        ((cplKer2 A).k ((cplGSD S Y).outSec.rep q) d₁) ∘ₗ ((cplKer1 A).k d₀ ((cplGSD S Y).outSec.rep q)) := by
  let i1 : Fintype (MulAction.orbitRel.Quotient S.G S.D) := h.fintypeCl
  let i2 : Fintype (MulAction.orbitRel.Quotient S.G Y.Pts) := (cplGSD_ok Y h).fintypeCl
  let i3 : ∀ x : S.D, Fintype (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
    have := (Y.fin x).to_subtype
    have := Finite.of_equiv _ (cplFibreEquiv Y x).symm
    Fintype.ofFinite _
  have key := sum_fibre_eq_sum_orbits (K := K) (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) h.fin_stab
    (fun p : Y.Pts => (A.k2 p.1.1 p.1.2 d₁) ∘ₗ (A.k1 d₀ p.1.1 p.1.2)) (by
      intro g p
      have e1 := A.equiv1 1 g d₀ p.1.1 p.1.2
      have e2 := A.equiv2 g 1 p.1.1 p.1.2 d₁
      rw [one_smul, inv_one, map_one] at e1
      rw [one_smul, map_one] at e2
      show (A.k2 (g • p.1.1) (g • p.1.2) d₁) ∘ₗ (A.k1 d₀ (g • p.1.1) (g • p.1.2)) = _
      rw [e1, e2]
      ext x
      simp only [LinearMap.comp_apply, one_apply_eq_self]
      rw [← mul_apply_eq_comp (S.ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self])
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  refine Eq.trans ?_ key
  show ∑ c : S.Cl, _ = _
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  congr 1
  let _ : Fintype (Y.ys c.out) := (Y.fin c.out).fintype
  refine (Finset.sum_subtype (p := fun y => y ∈ Y.ys c.out) (F := inferInstance) _
    (fun y => (Y.fin _).mem_toFinset) _).trans ?_
  exact ((cplFibreEquiv Y c.out).symm.sum_comp
    (fun y => (A.k2 y.1.1.1 y.1.1.2 d₁) ∘ₗ (A.k1 d₀ y.1.1.1 y.1.1.2)))

end Pairs

end GlobalTheory.GO
end
end
