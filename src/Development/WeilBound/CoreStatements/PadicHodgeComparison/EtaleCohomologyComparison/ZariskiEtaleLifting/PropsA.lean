module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConnectionOnDividedPowerBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleRootExt
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre

@[expose] public section

local instance (priority := high) : IsEmpty Empty := ⟨Empty.elim⟩

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapMemExt
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDAcyc

variable {B : Type} [CommRing B] {J : Ideal B}

theorem le_fil_one (δ : DividedPowers J) : J ≤ fil δ 1 := by
  intro j hj
  refine Ideal.subset_span ⟨[(1, j)], by simpa using hj, by simp, by simp [δ.dpow_one hj]⟩

theorem algebraMap_mem_ext (Q : PDPoly B) {j : B} (hj : j ∈ J) :
    algebraMap B Q.P j ∈ Q.ext J :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj)

theorem e_one_mem_ext (Q : PDPoly B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem map_e {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {μ q : B} (hμ : μ ∈ J) (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P μ + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) = ∑ j ∈ Finset.range (k + 1), (δ.dpow j μ * q ^ (k - j)) • Q.e (k - j) := by
  have he1 : Q.e 1 ∈ Q.ext J := e_one_mem_ext Q
  have hm : algebraMap B Q.P μ ∈ Q.ext J := algebraMap_mem_ext Q hμ
  have hq : algebraMap B Q.P q * Q.e 1 ∈ Q.ext J := Ideal.mul_mem_left _ _ he1
  have h0 : g (Q.e k) = η.dpow k (g (Q.e 1)) := by
    rw [hgd.dpow_comp _ he1, hS.var]
  rw [h0, h1, η.dpow_add hm hq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ η.dpow a (algebraMap B Q.P μ) * η.dpow b (algebraMap B Q.P q * Q.e 1))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [η.dpow_mul he1, hS.var, hS.dp.dpow_comp _ hμ, Algebra.smul_def, map_mul, map_pow]
  ring

noncomputable def qDer (Q : PDPoly B) (q : B) (ν : ℕ → B) : Q.P →ₗ[B] Q.P :=
  Q.e.constr B fun k ↦ (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
    ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1))

theorem qDer_e (Q : PDPoly B) (q : B) (ν : ℕ → B) (k : ℕ) :
    qDer Q q ν (Q.e k) = (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
      ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1)) := by
  simp only [qDer, Module.Basis.constr_basis]

theorem map_e_sub {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) - Q.e k = (q - 1) • qDer Q q ν (Q.e k) := by
  rw [map_e hS hμ g hgd h1, qDer_e, Finset.sum_range_succ', δ.dpow_zero hμ, smul_add,
    smul_smul, mul_geom_sum, Finset.smul_sum]
  simp only [hν, smul_smul, mul_assoc, Nat.sub_zero, one_mul, sub_smul, one_smul]
  abel

theorem map_sub_self {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgB : g.comp (algebraMap B Q.P) = algebraMap B Q.P)
    (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (z : Q.P) :
    g z - z = (q - 1) • qDer Q q ν z := by
  have hsm : ∀ (b : B) (w : Q.P), g (b • w) = b • g w := fun b w ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * g w) (RingHom.congr_fun hgB b)
  let gl : Q.P →ₗ[B] Q.P :=
    { toFun := g, map_add' := map_add g, map_smul' := fun b w ↦ by simpa using hsm b w }
  have key : gl - LinearMap.id = (q - 1) • qDer Q q ν :=
    Q.e.ext fun k ↦ by simpa [gl] using map_e_sub hS hμ hν g hgd h1 k
  simpa [gl] using LinearMap.congr_fun key z

theorem main : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B)
    (η : DividedPowers (Q.ext J)), Q.IsStd δ η → ∀ (p : ℕ), p.Prime → IsNilpotent (p : B) →
    ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → ∀ g : Q.P →+* Q.P,
    g.comp (algebraMap B Q.P) = algebraMap B Q.P → IsDPMorphism η η g →
    g (1 + Q.e 1) = algebraMap B Q.P (x ^ p) * (1 + Q.e 1) →
    Function.Injective (algebraMap B Q.P) ∧
    (∀ r, ∀ z ∈ fil η r, g z = z → ∃ m ∈ fil δ (r + 1),
      algebraMap B Q.P m = algebraMap B Q.P (x ^ p - 1) * z) ∧
    ∀ r, ∀ z ∈ fil η r, ∃ y ∈ fil η (r + 1), g y - y = algebraMap B Q.P (x ^ p - 1) * z := by
  intro B _ J δ Q η hS p hp hpn x hx g hgB hgd hg1
  have hrepr : ∀ b : B, Q.e.repr (algebraMap B Q.P b) 0 = b := fun b ↦ by
    rw [Algebra.algebraMap_eq_smul_one, ← Q.e_zero, map_smul]
    simp
  have hμ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hx
  obtain ⟨hqn, ν, hν1, hνd, hνf, hνn, hνz⟩ := GlobalTheory.T.cyclotomic_divided_power_expansion δ p hp hpn x hx
  obtain ⟨hfm, hfa, -, hfr⟩ := GlobalTheory.T.divided_power_polynomial_filtration δ Q η hS
  have h1 : g (Q.e 1) = algebraMap B Q.P (x ^ p - 1) + algebraMap B Q.P (x ^ p) * Q.e 1 := by
    have := hg1
    rw [map_add (f := _), map_one, mul_add, mul_one, add_comm (1 : Q.P)] at this
    rw [_root_.map_sub, map_one (algebraMap B Q.P)]
    linear_combination this
  have hg := map_sub_self hS hμ hνd g hgB hgd h1
  obtain ⟨hker, hsurj⟩ := GlobalTheory.T.connection_on_divided_power_basis Q.e (fil δ) p (x ^ p) ν (qDer Q (x ^ p) ν) hp.ne_zero hpn
    hqn hfm hfa hν1 hνf hνn hνz (qDer_e Q (x ^ p) ν)
  refine ⟨fun a b hab ↦ by rw [← hrepr a, hab, hrepr], ?_, ?_⟩
  · intro r z hz hgz
    have hD : qDer Q (x ^ p) ν ((x ^ p - 1) • z) = 0 := by
      rw [map_smul, ← hg, hgz, sub_self]
    obtain ⟨c, hc⟩ := hker _ hD
    have hc' : algebraMap B Q.P c = algebraMap B Q.P (x ^ p - 1) * z := by
      rw [← Algebra.smul_def, hc, Q.e_zero, Algebra.algebraMap_eq_smul_one]
    refine ⟨c, ?_, hc'⟩
    have hc0 : c = (x ^ p - 1) * Q.e.repr z 0 := by
      have := hrepr c
      rw [hc', ← Algebra.smul_def, map_smul] at this
      simpa using this.symm
    rw [hc0, add_comm]
    have hz0 : Q.e.repr z 0 ∈ fil δ r := by simpa using (hfr r z).1 hz 0
    exact hfm 1 r (Ideal.mul_mem_mul (le_fil_one δ hμ) hz0)
  · intro r z hz
    obtain ⟨y, hy, hDy⟩ := hsurj r z ((hfr r z).1 hz)
    refine ⟨y, (hfr (r + 1) y).2 hy, ?_⟩
    rw [hg, hDy, Algebra.smul_def]

end GlobalTheory.CompanionTheory.PDAcyc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDvdFactorialMul
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickLine

theorem pow_dvd_factorial_mul {p : ℕ} (hp : p.Prime) (N : ℕ) : p ^ N ∣ (p * N).factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem isNilpotent_of_mem {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {p : ℕ} (hp : p.Prime)
    (hn : IsNilpotent (p : A)) {x : A} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hn
  obtain ⟨k, hk⟩ := pow_dvd_factorial_mul hp N
  refine ⟨p * N, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hk]
  push_cast
  rw [hN]
  simp

theorem ringHom_eq {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

theorem e_one_mem {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem le_comap_ext {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) :
    J ≤ (Q.ext J).comap (algebraMap B Q.P) :=
  fun _ hx => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

variable (T : Thick (F.cr b ht κ)) (Q : PDPoly T.B) (η₀ : DividedPowers (Q.ext T.J)) (hη : Q.IsStd T.δ η₀)
  (hp : b.p ≠ 0)

def line : Thick (F.cr b ht κ) where
  B := Q.P
  i := (algebraMap T.B Q.P).comp T.i
  J := Q.ext T.J
  δ := η₀
  adm := ⟨fun _ => by simpa using (T.adm.1 hp).map (algebraMap T.B Q.P), fun h => absurd h hp⟩
  compat := IsDPMorphism.comp _ hη.dp T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map
    (CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J))) T.y
  inα := trivial
  w r := by
    change Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)
      ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w r]
    rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by rw [ht]; simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

def toLine : T ⟶ line T Q η₀ hη hp where
  φ := algebraMap T.B Q.P
  u j := j.elim
  comm _ := rfl
  dp := hη.dp
  hle := le_comap_ext Q T.J
  pt := rfl
  hx j := j.elim
  hs := by
    rw [s_eq_one T, map_one, mul_one]
    exact (Finset.prod_of_isEmpty (ι := Empty) _).symm
  hv j := j.elim

variable {T Q η₀ hη hp}

theorem exists_ext {T' : Thick (F.cr b ht κ)} (φ : T ⟶ T') {c : T'.B} (hc : c ∈ T'.J) :
    ∃ ψ : line T Q η₀ hη hp ⟶ T', toLine T Q η₀ hη hp ≫ ψ = φ ∧ ψ.φ (Q.e 1) = c := by
  obtain ⟨G, hG1, hG2⟩ := FubiniStudyChowHeightFormula₂.Adr.Fil.exists_lift Q T'.B φ.φ (fun k => T'.δ.dpow k c) (T'.δ.dpow_zero hc) (fun m k => T'.δ.mul_dpow hc)
  have hGa : G.comp (algebraMap T.B Q.P) = φ.φ := RingHom.ext hG1
  have hGdp : IsDPMorphism η₀ T'.δ G :=
    FubiniStudyChowHeightFormula₂.Adr.dp_of_std T.δ Q η₀ hη T'.δ G c hc (by rw [hGa]; exact φ.dp) hG2
  have hle : Q.ext T.J ≤ T'.J.comap G := Ideal.map_le_iff_le_comap.1 hGdp.1
  refine ⟨{ φ := G, u := fun j => j.elim, comm := fun r => ?_, dp := hGdp, hle := hle, pt := ?_,
            hx := fun j => j.elim, hs := ?_, hv := fun j => j.elim }, ?_, ?_⟩
  · exact (hG1 _).trans (φ.comm r)
  · refine Eq.trans ?_ φ.pt
    have e : CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle) =
        CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)) ≫
          CommRingCat.ofHom (Ideal.quotientMap T'.J G hle) := by
      refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      change Ideal.Quotient.mk T'.J (φ.φ a) = Ideal.Quotient.mk T'.J (G (algebraMap T.B Q.P a))
      rw [hG1]
    rw [e, Functor.map_comp]
    rfl
  · rw [s_eq_one T']
    refine Units.ext ?_
    change (1 : T'.B) = ((∏ j : Empty, (j.elim : T'.Bˣ)) * Units.map G.toMonoidHom 1 : T'.Bˣ)
    simp
  · exact Thick.Hom.ext hGa (funext fun j => j.elim)
  · change G (Q.e 1) = c
    rw [hG2 1]
    exact T'.δ.dpow_one hc

theorem hom_unique {T' : Thick (F.cr b ht κ)} {ψ ψ' : line T Q η₀ hη hp ⟶ T'}
    (h : toLine T Q η₀ hη hp ≫ ψ = toLine T Q η₀ hη hp ≫ ψ') (he : ψ.φ (Q.e 1) = ψ'.φ (Q.e 1)) : ψ = ψ' := by
  refine Thick.Hom.ext (ringHom_eq Q (fun a => ?_) fun k => ?_) (funext fun j => j.elim)
  · exact congrArg (fun f : T ⟶ T' => f.φ a) h
  · have h1 : T'.δ.dpow k (ψ.φ (Q.e 1)) = ψ.φ (η₀.dpow k (Q.e 1)) := ψ.dp.2 (Q.e 1) (e_one_mem Q T.J)
    have h2 : T'.δ.dpow k (ψ'.φ (Q.e 1)) = ψ'.φ (η₀.dpow k (Q.e 1)) := ψ'.dp.2 (Q.e 1) (e_one_mem Q T.J)
    rw [hη.var k] at h1 h2
    have h3 : T'.δ.dpow k (ψ.φ (Q.e 1)) = T'.δ.dpow k (ψ'.φ (Q.e 1)) := congrArg _ he
    exact h1.symm.trans (h3.trans h2)

def lineU (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime) :
    (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hpp.ne_zero) :=
  ⟨(isNilpotent_of_mem η₀ hpp (by simpa using (T.adm.1 hpp.ne_zero).map (algebraMap T.B Q.P))
      (e_one_mem Q T.J)).isUnit_one_add.unit,
    MonoidHom.mem_ker.2 (Units.ext (by
      change Ideal.Quotient.mk (Q.ext T.J) (1 + Q.e 1) = Ideal.Quotient.mk (Q.ext T.J) 1
      exact Ideal.Quotient.eq.2 (by simpa using e_one_mem Q T.J)))⟩

theorem map_lineU {T' : Thick (F.cr b ht κ)} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime)
    (ψ : line T Q η₀ hη hpp.ne_zero ⟶ T') :
    ((((thU (F.cr b ht κ) q hq).map ψ (lineU q hq hpp)).1 : T'.Bˣ) : T'.B) = 1 + ψ.φ (Q.e 1) := by
  change (ψ.φ : Q.P →+* T'.B) ((1 : Q.P) + Q.e 1) = 1 + _
  exact (map_add (ψ.φ : Q.P →+* T'.B) 1 (Q.e 1)).trans (by rw [map_one]; rfl)

theorem main : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (x : b.R), b.p.Prime → (q : b.R) = x ^ b.p → c μ = q - 1 → (∑ i ∈ Finset.range b.p, x ^ i) ∈ b.I → ∀ T : Thick (F.cr b ht κ), ∃ (T₁ : Thick (F.cr b ht κ)) (i : T ⟶ T₁) (η : (thU (F.cr b ht κ) q hq).U T₁), (∀ (T' : Thick (F.cr b ht κ)) (φ : T ⟶ T') (a : (thU (F.cr b ht κ) q hq).U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ (thU (F.cr b ht κ) q hq).map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → (thU (F.cr b ht κ) q hq).map g η = (thU (F.cr b ht κ) q hq).q _ * η → (pdFlt (F.cr b ht κ) c ρ hρ μ hμ).FAcyc i g := by
  intro O _ F b ht κ Λ _ c ρ hρ μ hμ q hq x hpp hqx hcμ hsum T
  have hp0 := hpp.ne_zero
  obtain ⟨Q⟩ : Nonempty (PDPoly T.B) := ⟨GlobalTheory.PDA.Model.pdPoly T.B⟩
  obtain ⟨η₀, hη⟩ := FubiniStudyChowHeightFormula₂.Adr.exists_std T.B T.J T.δ Q
  refine ⟨line T Q η₀ hη hp0, toLine T Q η₀ hη hp0, lineU q hq hpp, ?_, ?_⟩
  · intro T' φ a
    have hc : ((a.1 : T'.Bˣ) : T'.B) - 1 ∈ T'.J := by
      have h : Ideal.Quotient.mk T'.J ((a.1 : T'.Bˣ) : T'.B) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
      exact Ideal.Quotient.eq.1 (h.trans (map_one _).symm) |> fun h => by simpa using h
    obtain ⟨ψ, h1, h2⟩ := exists_ext (Q := Q) (η₀ := η₀) (hη := hη) (hp := hp0) φ hc
    refine ⟨ψ, ⟨h1, ?_⟩, ?_⟩
    · refine Subtype.ext (Units.ext ?_)
      refine (map_lineU q hq hpp ψ).trans ?_
      rw [h2]
      ring
    · rintro ψ' ⟨h1', h2'⟩
      have e : 1 + ψ'.φ (Q.e 1) = ((a.1 : T'.Bˣ) : T'.B) := (map_lineU q hq hpp ψ').symm.trans
        (congrArg (fun u : (thU (F.cr b ht κ) q hq).U T' => ((u.1 : T'.Bˣ) : T'.B)) h2')
      refine hom_unique (h1'.trans h1.symm) ?_
      rw [h2]
      exact eq_sub_of_add_eq' e
  · intro g hg hgη
    let gφ : Q.P →+* Q.P := g.φ
    have hgφ : gφ.comp (algebraMap T.B Q.P) = algebraMap T.B Q.P :=
      congrArg (fun f : T ⟶ line T Q η₀ hη hp0 => f.φ) hg
    have hmul : gφ (1 + Q.e 1) = algebraMap T.B Q.P ((T.i x) ^ b.p) * (1 + Q.e 1) := by
      have e : gφ (1 + Q.e 1) = algebraMap T.B Q.P (T.i (q : b.R)) * (1 + Q.e 1) :=
        congrArg (fun u : (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hp0) =>
          ((u.1 : (line T Q η₀ hη hp0).Bˣ) : (line T Q η₀ hη hp0).B)) hgη
      rw [e, hqx, map_pow]
    have hsum' : (∑ i ∈ Finset.range b.p, (T.i x) ^ i) ∈ T.J := by
      have := T.i_mem hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_pow] using this
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.CompanionTheory.PDAcyc.main T.δ Q η₀ hη b.p hpp (T.adm.1 hp0) (T.i x) hsum' gφ hgφ g.dp hmul
    have hμ' : ∀ z : Q.P, algebraMap T.B Q.P ((T.i x) ^ b.p - 1) * z =
        algebraMap T.B Q.P (T.i (c μ)) * z := by
      intro z
      rw [hcμ, hqx, map_sub T.i, map_pow, map_one]
    refine ⟨h1, ?_, ?_⟩
    · intro r z hz hz'
      obtain ⟨m, hm, e⟩ := h2 (ρ r) z hz hz'
      exact ⟨m, T.pdPow_anti (hρ.2 r) hm, e.trans (hμ' z)⟩
    · intro r z hz
      obtain ⟨y, hy, e⟩ := h3 (ρ r) z hz
      exact ⟨y, (line T Q η₀ hη hp0).pdPow_anti (hρ.2 r) hy, e.trans (hμ' z)⟩

end GlobalTheory.CompanionTheory.ThickLine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsActOfHom
section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FirstChernClassMemHodgeFiltration
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.LogCris.CupModel

variable {b : Base} {L : b.Fun}

theorem isNilpotent_of_mem (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    simpa using this
  · obtain ⟨n, hn⟩ := T.adm.1 hp
    refine ⟨b.p ^ n, ?_⟩
    rw [← T.δ.factorial_mul_dpow_eq_pow hx]
    obtain ⟨c, hc⟩ : b.p ^ n ∣ (b.p ^ n).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero _ hp)) le_rfl
    rw [hc, Nat.cast_mul, Nat.cast_pow, hn, zero_mul, zero_mul]



end GlobalTheory.LogCris.CupModel

namespace GlobalTheory.CatH

end GlobalTheory.CatH
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickAct

theorem exists_act_of_hom {b : Base} {L : b.Fun} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (D : Thick L)
    {R : Type} [CommRing R] {d : ℕ} (τ : Fin d → Rˣ) (t : Fin d → D.B)
    (g : ∀ T : Thick L, R →+* T.B ⧸ T.J)
    (hcl : ∀ (T : Thick L) (c : D ⟶ T) (k : Fin d), Ideal.Quotient.mk T.J (c.φ (t k)) = g T (τ k))
    (hex : ∀ (T : Thick L) (u : Fin d → T.B), (∀ k, Ideal.Quotient.mk T.J (u k) = g T (τ k)) →
      ∃! c : D ⟶ T, ∀ k, c.φ (t k) = u k) :
    ∃ A : Act (𝟭 _) (thU L q hq) d D, ∀ (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) (k : Fin d),
      (A.act a c).φ (t k) = ((a k).1 : T.B) * c.φ (t k) := by
  classical
  have hunit : ∀ (T : Thick L) (x : T.B), IsUnit (Ideal.Quotient.mk T.J x) → IsUnit x := by
    intro T x hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    have hm : x * y' - 1 ∈ T.J := by
      rw [← Ideal.Quotient.eq, map_mul, map_one]
      exact hy
    have h1 : IsUnit (1 + (x * y' - 1)) := (GlobalTheory.LogCris.CupModel.isNilpotent_of_mem T hm).isUnit_one_add
    rw [add_sub_cancel] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hker : ∀ (T : Thick L) (x : (thU L q hq).U T), Ideal.Quotient.mk T.J ((x.1 : T.Bˣ) : T.B) = 1 :=
    fun T x => congrArg Units.val (MonoidHom.mem_ker.1 x.2)
  have hlift : ∀ (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) (k : Fin d),
      Ideal.Quotient.mk T.J (((a k).1 : T.B) * c.φ (t k)) = g T (τ k) := by
    intro T a c k
    rw [map_mul, hker, one_mul, hcl]
  have hu : ∀ (T : Thick L) (c₁ c₂ : D ⟶ T), (∀ k, c₁.φ (t k) = c₂.φ (t k)) → c₁ = c₂ := by
    intro T c₁ c₂ h
    obtain ⟨c, _, hc⟩ := hex T (fun k => c₂.φ (t k)) (fun k => hcl T c₂ k)
    exact (hc c₁ h).trans (hc c₂ fun _ => rfl).symm
  choose act hact using fun (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) =>
    (hex T _ (hlift T a c)).exists
  have hw : ∀ (T : Thick L) (e : D ⟶ T) (k : Fin d), IsUnit (e.φ (t k)) := fun T e k =>
    hunit T _ (by rw [hcl]; exact (τ k).isUnit.map (g T))
  refine ⟨⟨@fun T a c => act T a c, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro T c
    show act T 1 c = c
    apply hu
    intro k
    rw [hact]
    simp
  · intro T a b c
    show act T (a * b) c = act T a (act T b c)
    apply hu
    intro k
    rw [hact, hact, hact]
    exact mul_assoc (((a k).1 : T.Bˣ) : T.B) (((b k).1 : T.Bˣ) : T.B) (c.φ (t k))
  · intro T T' a c φ
    show act T a c ≫ φ = act T' (fun k => (thU L q hq).map φ (a k)) (c ≫ φ)
    apply hu
    intro k
    rw [hact]
    change φ.φ ((act T a c).φ (t k)) = _
    rw [hact, map_mul]
    rfl
  · intro T
    show Nonempty (D ⟶ T)
    choose u hu' using fun k => Ideal.Quotient.mk_surjective (I := T.J) (g T (τ k))
    exact ⟨(hex T u hu').exists.choose⟩
  · intro T
    show ∀ c c' : D ⟶ T, ∃! a, act T a c = c'
    intro c c'
    let a : Fin d → (thU L q hq).U T := fun k =>
      ⟨(hw T c' k).unit * ((hw T c k).unit)⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have e : Units.map (Ideal.Quotient.mk T.J).toMonoidHom (hw T c' k).unit =
            Units.map (Ideal.Quotient.mk T.J).toMonoidHom (hw T c k).unit := by
          apply Units.ext
          simp only [Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hcl]
        rw [e, mul_inv_cancel]⟩
    refine ⟨a, ?_, ?_⟩
    · apply hu
      intro k
      rw [hact]
      change (((hw T c' k).unit * ((hw T c k).unit)⁻¹ : T.Bˣ) : T.B) * c.φ (t k) = c'.φ (t k)
      rw [Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]
    · intro a' ha'
      funext k
      apply Subtype.ext
      apply Units.ext
      have h := congrArg (fun e : D ⟶ T => e.φ (t k)) ha'
      simp only [hact] at h
      change ((a' k).1 : T.B) = (((hw T c' k).unit * ((hw T c k).unit)⁻¹ : T.Bˣ) : T.B)
      rw [Units.val_mul, IsUnit.unit_spec (hw T c' k), ← h, mul_assoc, IsUnit.mul_val_inv, mul_one]
  · intro T a c k
    exact hact T a c k

theorem thick_act : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I), ∃ A : Act (𝟭 _) (thU (F.cr b ht κ) q hq) d (liftObj s ht 𝓛 δ hδ hp hn), ∀ (T : Thick (F.cr b ht κ)) (a : Fin d → (thU (F.cr b ht κ) q hq).U T) (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (k : Fin d), (A.act a c).φ (𝓛.t k) = ((a k).1 : T.B) * c.φ (𝓛.t k) := by
  intro O _ F d s b ht κ 𝓛 δ hδ hp hn q hq
  choose g hg using fun T => GlobalTheory.T.exists_lift_to_thickening s ht 𝓛 δ hδ hp hn T
  exact exists_act_of_hom q hq (liftObj s ht 𝓛 δ hδ hp hn) s.T 𝓛.t g
    (fun T c k => (hg T).1 c (s.T k) (𝓛.t k) (𝓛.hT k).symm) (fun T u hu => (hg T).2.2 u hu)

end GlobalTheory.CompanionTheory.ThickAct
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubThickOnto
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickSub

theorem subThick_onto {O : Type} [CommRing O] {F : Fn O} (V : F.Sub) (b : Base) (ht : b.t = 1)
    (κ : O →+* b.R ⧸ b.I) : Onto (subThick V b ht κ) fun T => V.In T.y.1.2 := by
  refine ⟨⟨fun {T T'} f => ⟨{
      φ := f.φ, u := f.u, comm := f.comm, dp := f.dp, hle := f.hle,
      pt := Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) f.pt)
        (Subtype.ext (congrArg (fun z => z.1.2) f.pt))),
      hx := fun j => j.elim, hs := f.hs, hv := fun j => j.elim }, rfl⟩⟩,
    ⟨fun {T T'} f g h => Thick.Hom.ext (congrArg (fun m => m.φ) h) (funext fun j => j.elim)⟩,
    fun T => T.y.1.2.2, fun T h => ?_⟩
  refine ⟨{ B := T.B, i := T.i, J := T.J, δ := T.δ, adm := T.adm, compat := T.compat, α := (),
            y := ⟨(T.y.1.1, ⟨T.y.1.2, h⟩), T.y.2⟩, inα := trivial, w := T.w, x := T.x, v := T.v, s := T.s,
            hx := fun j => j.elim, hs := T.hs, hv := T.hv }, ⟨eqToIso rfl⟩⟩

end GlobalTheory.CompanionTheory.ThickSub
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PreimageOpenTopOfJacobsonSurjection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.SchAtlas

open GlobalTheory.AbLaw GlobalTheory.PrimSec

variable {O : Type} [CommRing O] {X : Scheme.{0}}

def subOf (q : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens) : (schFn q).Sub where
  In {B} y := ⊤ ≤ (show Spec B ⟶ X from y) ⁻¹ᵁ U
  in_map {B B'} φ y h := by
    intro p _
    exact h (show (Spec.map φ p : Spec B) ∈ (⊤ : (Spec B).Opens) from trivial)

theorem fromSpec_comp_cst (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (cst q W)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hW (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem small_of_affine (q : X ⟶ Spec (CommRingCat.of O)) (V : (schFn q).Sub) {W : X.Opens}
    (hW : IsAffineOpen W)
    (hV : ∀ {B : CommRingCat.{0}} (y : Spec B ⟶ X), V.In (B := B) y ↔ ⊤ ≤ y ⁻¹ᵁ W)
    {d : ℕ} (T : Fin d → Γ(X, W)ˣ)
    (et : (MvPolynomial.eval₂Hom (cst q W) fun k => (T k : Γ(X, W))).Etale) :
    Nonempty (V.fn.Small d) := by
  refine ⟨{ R := Γ(X, W), a := cst q W, T := T, et := et,
            y₀ := ⟨hW.fromSpec, (hV _).2 hW.fromSpec_preimage_self.ge⟩,
            ov := fromSpec_comp_cst q hW,
            univ := ?_ }⟩
  intro B y f _
  have hy : ⊤ ≤ (show Spec B ⟶ X from y.1) ⁻¹ᵁ W := (hV _).1 y.2
  have hr : Set.range (show Spec B ⟶ X from y.1) ⊆ Set.range hW.fromSpec := by
    rintro _ ⟨p, rfl⟩
    exact hW.range_fromSpec.ge (hy (show p ∈ (⊤ : (Spec B).Opens) from trivial))
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec (show Spec B ⟶ X from y.1) hr)).hom, ?_, ?_⟩
  · refine Subtype.ext ?_
    exact (congrArg (· ≫ hW.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)
  · intro g hg
    have h1 : Spec.map (CommRingCat.ofHom g) ≫ hW.fromSpec = (show Spec B ⟶ X from y.1) :=
      congrArg Subtype.val hg
    have h2 : Spec.map (CommRingCat.ofHom g) =
        IsOpenImmersion.lift hW.fromSpec (show Spec B ⟶ X from y.1) hr := by
      rw [← cancel_mono hW.fromSpec, IsOpenImmersion.lift_fac, h1]
    have h3 := Spec.map_injective (h2.trans (Spec.map_preimage _).symm)
    exact congrArg CommRingCat.Hom.hom h3

theorem rs_etale {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) :
    (rs X h).Etale := by
  have h1 := (𝟙 X : X ⟶ X).etale_appLE hU hW h
  have e : (𝟙 X : X ⟶ X).appLE U W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
  rw [e] at h1
  exact h1

theorem et_res (q : X ⟶ Spec (CommRingCat.of O)) {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (et : (MvPolynomial.eval₂Hom (cst q U) t).Etale) :
    (MvPolynomial.eval₂Hom (cst q W) fun k => rs X h (t k)).Etale := by
  have e : MvPolynomial.eval₂Hom (cst q W) (fun k => rs X h (t k)) =
      (rs X h).comp (MvPolynomial.eval₂Hom (cst q U) t) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_
    · simp [rs_cst]
    · simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ et (rs_etale hU hW h)

theorem et_shift {R : Type} [CommRing R] (a : O →+* R) {d : ℕ} (t : Fin d → R) (e : Fin d → O)
    (et : (MvPolynomial.eval₂Hom a t).Etale) :
    (MvPolynomial.eval₂Hom a fun k => t k + a (e k)).Etale := by
  let σ : MvPolynomial (Fin d) O →+* MvPolynomial (Fin d) O :=
    MvPolynomial.eval₂Hom MvPolynomial.C fun k => MvPolynomial.X k + MvPolynomial.C (e k)
  let σ' : MvPolynomial (Fin d) O →+* MvPolynomial (Fin d) O :=
    MvPolynomial.eval₂Hom MvPolynomial.C fun k => MvPolynomial.X k - MvPolynomial.C (e k)
  have h1 : σ.comp σ' = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ, σ']
  have h2 : σ'.comp σ = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ, σ']
  have hb : Function.Bijective σ := Function.bijective_iff_has_inverse.2
    ⟨σ', fun x => RingHom.congr_fun h2 x, fun x => RingHom.congr_fun h1 x⟩
  have e1 : MvPolynomial.eval₂Hom a (fun k => t k + a (e k)) =
      (MvPolynomial.eval₂Hom a t).comp σ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hb) et

theorem exists_unit_chart (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ (n : ℕ) (T : Fin n → Γ(X, U)ˣ),
      (MvPolynomial.eval₂Hom (cst q U) fun k => (T k : Γ(X, U))).Etale := by
  classical
  obtain ⟨V, hV, hx, -, n, φ, hφC, hφ⟩ := exists_etale_chart q (U := ⊤) (x := x) trivial
  let t : Fin n → Γ(X, V) := fun k => φ (MvPolynomial.X k)
  have e0 : φ = MvPolynomial.eval₂Hom (cst q V) t := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_
    · simpa using RingHom.congr_fun hφC r
    · simp [t]
  rw [e0] at hφ
  let P : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have hP : P.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  have hc : ∀ k, ∃ e : O, t k + cst q V e ∉ P := by
    intro k
    by_cases h : t k ∈ P
    · refine ⟨1, fun h' => hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
      have := P.sub_mem h' h
      simpa using this
    · exact ⟨0, by simpa using h⟩
  choose e he using hc
  have et := et_shift (cst q V) t e hφ
  let t' : Fin n → Γ(X, V) := fun k => t k + cst q V (e k)
  let h : Γ(X, V) := ∏ k, t' k
  have hh : h ∉ P := by
    intro hm
    obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).1 hm
    exact he k hk
  have hxW : x ∈ X.basicOpen h := (mem_basicOpen_iff hV ⟨x, hx⟩ h).2 hh
  have hle : X.basicOpen h ≤ V := X.basicOpen_le h
  have hW := hV.basicOpen h
  have hunit : IsUnit (rs X hle h) := RingedSpace.isUnit_res_basicOpen _ h
  have hu : ∀ k, IsUnit (rs X hle (t' k)) := fun k =>
    isUnit_of_dvd_unit (map_dvd (rs X hle) (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))) hunit
  exact ⟨X.basicOpen h, hW, hxW, n, fun k => (hu k).unit, et_res q hV hW hle t' et⟩

theorem exists_unimodular_cover_refining_opens {A : Type} (U : A → X.Opens) (hU : ∀ x : X, ∃ α, x ∈ U α) {B : CommRingCat.{0}}
    (y : Spec B ⟶ X) : ∃ (m : ℕ) (s : Fin m → B), Ideal.span (Set.range s) = ⊤ ∧
      ∀ k (B' : CommRingCat.{0}) (φ : B ⟶ B'), IsUnit (φ.hom (s k)) →
        ∃ α, ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U α := by
  classical
  let S : Set B := {s | ∃ α, ∀ p : PrimeSpectrum B, s ∉ p.asIdeal → y p ∈ U α}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum B := ⟨M, hM.isPrime⟩
    obtain ⟨α, hα⟩ := hU (y p)
    have hop : IsOpen {p : PrimeSpectrum B | y p ∈ U α} := (y ⁻¹ᵁ U α).isOpen
    obtain ⟨_, ⟨r, rfl⟩, hpr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ {p : PrimeSpectrum B | y p ∈ U α} from hα) hop
    have hr : r ∈ S := ⟨α, fun p' hp' => hsub hp'⟩
    exact hpr (hle (Ideal.subset_span hr))
  obtain ⟨s', hs', hspan⟩ := (Ideal.span_eq_top_iff_finite S).1 hS
  refine ⟨s'.card, fun k => (s'.equivFin.symm k).1, ?_, ?_⟩
  · have : Set.range (fun k => (s'.equivFin.symm k).1) = (s' : Set B) := by
      ext b
      constructor
      · rintro ⟨k, rfl⟩
        exact (s'.equivFin.symm k).2
      · intro hb
        exact ⟨s'.equivFin ⟨b, hb⟩, by simp⟩
    rw [this, hspan]
  · intro k B' φ hu
    obtain ⟨α, hα⟩ := hs' (s'.equivFin.symm k).2
    refine ⟨α, fun p' _ => ?_⟩
    have h1 : (s'.equivFin.symm k).1 ∉ (PrimeSpectrum.comap φ.hom p').asIdeal := fun hm =>
      (p' : PrimeSpectrum B').isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
    exact hα _ h1

theorem preimage_open_top_of_jacobson_surjection (U : X.Opens) (B B' : CommRingCat.{0}) (φ : B ⟶ B') (y : Spec B ⟶ X)
    (hs : Function.Surjective φ.hom) (hk : RingHom.ker φ.hom ≤ (⊥ : Ideal B).jacobson)
    (h : ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (p : PrimeSpectrum B).asIdeal (p : PrimeSpectrum B).isPrime.ne_top
  let m : PrimeSpectrum B := ⟨M, hM.isPrime⟩
  have hker : RingHom.ker φ.hom ≤ M := hk.trans (sInf_le ⟨bot_le, hM⟩)
  haveI := hM.isPrime
  let m' : PrimeSpectrum B' := ⟨M.map φ.hom, Ideal.map_isPrime_of_surjective hs hker⟩
  have hm' : PrimeSpectrum.comap φ.hom m' = m := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap φ.hom (M.map φ.hom) = M
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left]
    exact hker
  have h1 : y m ∈ U := by
    have := h (show (m' : Spec B') ∈ (⊤ : (Spec B').Opens) from trivial)
    rw [← hm']
    exact this
  exact ((PrimeSpectrum.le_iff_specializes _ _).mp hle).mem_open (y ⁻¹ᵁ U).isOpen h1

theorem mem_biInf_of_finite {A : Type} [Finite A] (S : Set A) (U : A → X.Opens) {x : X}
    (h : ∀ β ∈ S, x ∈ U β) : x ∈ ⨅ β ∈ S, U β := by
  let G : X.Opens := ⟨⋂ β ∈ S, (U β : Set X), S.toFinite.isOpen_biInter fun β _ => (U β).isOpen⟩
  have hG : G ≤ ⨅ β ∈ S, U β :=
    le_iInf₂ fun β hβ y hy => Set.mem_iInter₂.1 hy β hβ
  exact hG (Set.mem_iInter₂.2 h)

theorem exists_atlas {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))
    [Smooth q] [IsSeparated q] [QuasiCompact q] : ∃ d, Nonempty ((schFn q).Atlas d) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  haveI : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from q]
    infer_instance
  choose U hU hx n T et using exists_unit_chart q
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => (U x : Set X))
    (fun x _ => (U x).isOpen.mem_nhds (hx x))
  have hcov : ∀ x : X, ∃ α : {x // x ∈ t}, x ∈ U α.1 := by
    intro x
    have := ht.2 (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, ha, hxa⟩ := this
    exact ⟨⟨a, ha⟩, hxa⟩
  refine ⟨t.sup n, ⟨⟨{x // x ∈ t}, inferInstance, fun α => subOf q (U α.1),
    fun B y => ?_, fun α B B' φ y hs hk h => ?_, fun S hS => ?_⟩⟩⟩
  · exact exists_unimodular_cover_refining_opens (fun α : {x // x ∈ t} => U α.1) hcov y
  · exact preimage_open_top_of_jacobson_surjection (U α.1) B B' φ y hs hk h
  · obtain ⟨α, hα⟩ := hS
    have hW : IsAffineOpen (⨅ β ∈ S, U (Subtype.val β)) :=
      IsAffineOpen.biInf S S.toFinite ⟨α, hα⟩ fun i _ => hU i.1
    have hle : (⨅ β ∈ S, U (Subtype.val β)) ≤ U α.1 := iInf₂_le α hα
    refine ⟨n α.1, Finset.le_sup α.2, ?_⟩
    refine small_of_affine q _ hW ?_ (fun k => Units.map (rs X hle).toMonoidHom (T α.1 k))
      (et_res q (hU α.1) hW hle _ (et α.1))
    intro B y
    change (∀ β ∈ S, ⊤ ≤ y ⁻¹ᵁ U β.1) ↔ _
    constructor
    · intro h p _
      exact mem_biInf_of_finite S (fun β : {x // x ∈ t} => U β.1)
        fun β hβ => h β hβ (show p ∈ (⊤ : (Spec B).Opens) from trivial)
    · intro h β hβ p hp
      exact (iInf₂_le (f := fun (β : {x // x ∈ t}) (_ : β ∈ S) => U β.1) β hβ) (h hp)

end GlobalTheory.CompanionTheory.SchAtlas
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.elift : ∀ {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ} (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I), (MvPolynomial.eval₂Hom a T).Etale → Nonempty (Lift a T Λ I κ) :=
  @GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift

theorem CrystallineSemistableComparison.B.P.lift_flat : ∀ {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ} (t : Fin d → D), (MvPolynomial.eval₂Hom i t).Etale → i.Flat ∧ ∀ (J : Ideal D) (μ : D) (g : D →+* D), (∀ x ∈ J, IsNilpotent x) → g.comp i = i → (∀ k, g (t k) - t k ∈ Ideal.span {μ}) → (∀ z, g z - z ∈ J) → ∀ z, g z - z ∈ Ideal.span {μ} :=
  @GlobalTheory.CompanionTheory.LiftFlat.lift_flat

theorem CrystallineSemistableComparison.B.P.thick_onto : ∀ {O : Type} [CommRing O] {F : Fn O} (V : F.Sub) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I), Onto (subThick V b ht κ) fun T => V.In T.y.1.2 :=
  @GlobalTheory.CompanionTheory.ThickSub.subThick_onto

theorem CrystallineSemistableComparison.B.P.thick_zar : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) {d : ℕ} (𝒜 : F.Atlas d), b.p ≠ 0 → ∀ r : ℕ, ZarCov (pdS (F.cr b ht κ) c r).fn fun T => ∃ α, (𝒜.V α).In T.y.1.2 :=
  @GlobalTheory.CompanionTheory.ThickZar.zarCov_pdS

theorem CrystallineSemistableComparison.B.P.thick_act : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I), ∃ A : Act (𝟭 _) (thU (F.cr b ht κ) q hq) d (liftObj s ht 𝓛 δ hδ hp hn), ∀ (T : Thick (F.cr b ht κ)) (a : Fin d → (thU (F.cr b ht κ) q hq).U T) (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (k : Fin d), (A.act a c).φ (𝓛.t k) = ((a k).1 : T.B) * c.φ (𝓛.t k) :=
  @GlobalTheory.CompanionTheory.ThickAct.thick_act

theorem CrystallineSemistableComparison.B.P.thick_line : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (x : b.R), b.p.Prime → (q : b.R) = x ^ b.p → c μ = q - 1 → (∑ i ∈ Finset.range b.p, x ^ i) ∈ b.I → ∀ T : Thick (F.cr b ht κ), ∃ (T₁ : Thick (F.cr b ht κ)) (i : T ⟶ T₁) (η : (thU (F.cr b ht κ) q hq).U T₁), (∀ (T' : Thick (F.cr b ht κ)) (φ : T ⟶ T') (a : (thU (F.cr b ht κ) q hq).U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ (thU (F.cr b ht κ) q hq).map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → (thU (F.cr b ht κ) q hq).map g η = (thU (F.cr b ht κ) q hq).q _ * η → (pdFlt (F.cr b ht κ) c ρ hρ μ hμ).FAcyc i g :=
  @GlobalTheory.CompanionTheory.ThickLine.main

theorem CrystallineSemistableComparison.B.P.atlas : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q] [IsSeparated q] [QuasiCompact q], ∃ d, Nonempty ((schFn q).Atlas d) :=
  @GlobalTheory.CompanionTheory.SchAtlas.exists_atlas
