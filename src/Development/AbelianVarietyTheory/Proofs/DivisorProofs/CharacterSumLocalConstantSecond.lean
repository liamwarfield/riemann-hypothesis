module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifC
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.BadPrimes

theorem false_of_isCoprime {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {a b : A}
    (h : IsCoprime a b) (ha : a ∈ P.asIdeal) (hb : b ∈ P.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := h
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)))

theorem eq_of_natCast_mem {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : (p : A) ∈ P.asIdeal) (hb : (q : A) ∈ P.asIdeal) : p = q := by
  by_contra hne
  exact false_of_isCoprime P (Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)) ha hb

variable {X : Fields} {Pr : Primes X}

theorem g_injective (hPr : Pr.Ok) : Function.Injective Pr.g := by
  intro i j h
  have := hPr.g_ne
  fin_cases i <;> fin_cases j <;> simp_all

theorem exists_vG {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : ∃ i, P ∈ Pr.vG i := by
  classical
  rcases Finset.mem_union.mp h with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piG_norm i ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)

theorem T_mem (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ (mem_of_mem_divs h)

theorem natCast_mem_of_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} (h : ((n : ℕ) : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal) :
    ((n : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast] at h
  exact h

theorem rowSG_one (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) :
    rowSG Pr sel (1 : Tup X.F X.E X.K Sg) = Pr.vGs := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with h | h
    · exact h
    · have h' : w ∈ QE sel ((mu0 X.F X.E X.K Sg : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) := h
      rw [twistPrimes_trivialTuple_empty sel Sg] at h'
      simp at h'
  · intro hw
    exact Finset.mem_union.mpr (Or.inl hw)

theorem prod_qOf_vGs (hPr : Pr.Ok) : ∏ P ∈ Pr.vGs, Formalism.L2.Col.qOf P = (Pr.g 0 * Pr.g 1) ^ X.f := by
  classical
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := Finset.disjoint_left.2 fun P h0 h1 =>
    hPr.g_ne (eq_of_natCast_mem P (hPr.g_prime 0) (hPr.g_prime 1) (g_mem hPr h0) (g_mem hPr h1))
  have hi : ∀ i, ∏ P ∈ Pr.vG i, Formalism.L2.Col.qOf P = Pr.g i ^ X.f := fun i => by
    unfold Formalism.L2.Col.qOf
    rw [Finset.prod_congr rfl (g := fun _ => Pr.g i) (fun P hP => hPr.vG_norm i P hP), Finset.prod_const, hPr.vG_card]
  have hu : Pr.vGs = (Pr.vG 0).disjUnion (Pr.vG 1) hd := by
    ext w
    simp [Primes.vGs]
  rw [hu, Finset.prod_disjUnion, hi, hi, mul_pow]

theorem odd_g (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (i : Fin 2) : Odd (Pr.g i) :=
  Nat.odd_iff.2 ((hPr.g_cong i).of_dvd h2)

theorem two_notMem_vT (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    (2 : 𝓞 X.E) ∉ P.asIdeal := by
  intro hP
  obtain ⟨c, hc⟩ := hPr.piT_cong u
  obtain ⟨k, hk⟩ := h2
  have h1 : Pr.piT u - 1 ∈ P.asIdeal := by
    rw [hc, hk]
    push_cast
    rw [mul_assoc, mul_assoc]
    exact Ideal.mul_mem_right _ _ hP
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (mem_of_mem_divs h) h1))

theorem odd_typePrime_of_two_dvd_cond (hX : X.Ok) (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (u : Pr.Word) : Odd (Pr.T u) := by
  obtain ⟨P, hP⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  refine (hPr.T_prime u).odd_of_ne_two fun h => two_notMem_vT hPr h2 hP ?_
  have := T_mem hPr hP
  rw [h] at this
  exact_mod_cast this

theorem conjP_notMem (hPr : Pr.Ok) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u ∨ P ∈ Pr.vGs) :
    ¬ (conjPrime₂ P ∈ Pr.vT u ∨ conjPrime₂ P ∈ Pr.vGs) := by
  rintro (h' | h')
  · rcases h with h | h
    · exact false_of_isCoprime P (hPr.piT_cop u) (mem_of_mem_divs h) (mem_of_mem_divs h' :)
    · obtain ⟨i, hi⟩ := exists_vG h
      exact hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i)
        (natCast_mem_of_conjP (T_mem hPr h')) (g_mem hPr hi))
  · obtain ⟨j, hj⟩ := exists_vG h'
    have hg := natCast_mem_of_conjP (g_mem hPr hj)
    rcases h with h | h
    · exact hPr.T_ne_g u j (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime j) (T_mem hPr h) hg)
    · obtain ⟨i, hi⟩ := exists_vG h
      obtain rfl : i = j := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime i) (hPr.g_prime j) (g_mem hPr hi) hg)
      have h1 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal := (mem_of_mem_divs hj :)
      rw [cO_cO] at h1
      exact false_of_isCoprime P (hPr.piG_cop i) h1 (mem_of_mem_divs hi)

end GlobalTheory.ColNorms.BadPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

def comb (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (z : X) (q : N.ι)
    (j : Fin mB) : X.presheaf.stalk z :=
  ∑ i, gs p z ⊤ (c i j) * gs φ z (N.U q) ((a i).f q)

def Generates (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q, φ z ∈ N.U q → ∃ j, IsUnit (comb a φ p c z q j)

def Proport (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (Ψ : X ⟶ B₀)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q k, φ z ∈ N.U q → Ψ z ∈ H.U k → ∀ j j',
    gs Ψ z (H.U k) ((b j).f k) * comb a φ p c z q j' = gs Ψ z (H.U k) ((b j').f k) * comb a φ p c z q j

def gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (z : X) : R →+* X.presheaf.stalk z :=
  (X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def Kills {R : Type} [CommRing R] (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (F : MvPolynomial (Fin mB) R) : Prop :=
  ∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0

def FormsOK {R : Type} [CommRing R] (a : Fin mA → LB.Sec N) (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀)
    (p : X ⟶ T) (t : T ⟶ Sp R) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin mB) R), F.IsHomogeneous d → Kills fB b F →
    ∀ z q, φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0

def IsVal {S : Scheme.{0}} (e : S ⟶ A₀) (u : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ) (s : LB.Sec N) (α : Γ(S, ⊤)) :
    Prop :=
  ∀ z q, e z ∈ N.U q → gs e z (N.U q) (s.f q) = gs (𝟙 S) z ⊤ α * (u z q).val

def Normal {S : Scheme.{0}} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤)) (α : Fin mA → Γ(S, ⊤)) (β : Fin mB → Γ(S, ⊤)) :
    Prop :=
  ∀ j, t.appTop (β j) = ∑ i, c i j * t.appTop (α i)

def θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A.left ⟶ (topS Rg ⊗ A).left :=
  (lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)).left

theorem θ_snd {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ (snd (topS Rg) A).left = 𝟙 A.left := by
  rw [θ, ← Over.comp_left, lift_snd]; rfl

abbrev fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : (topS Rg ⊗ A).left ⟶ Sp Rg := (topS Rg ⊗ A).hom

theorem coord_comp {Rg : Type} [CommRing Rg] {X' : Scheme.{0}} {n : ℕ} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin n) Rg)) (i : Fin n) : coord (h ≫ g) i = h.appTop (coord g i) := by
  rfl

def uFr {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (z : (𝟙_ (Over (Sp Rg))).left) (q : (LPow A L (k : ℤ) (topS Rg)).ι) :
    ((𝟙_ (Over (Sp Rg))).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 _) z _ (eA.s fun _ => q 0)) ^ k

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.UpIdeleMod

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]


omit [NumberField K] in
theorem valued_algebraMap {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.adicCompletion.valued_coe K v k

theorem valued_finiteCompletionMap (w : HeightOneSpectrum (𝓞 E)) (x : (w.under (𝓞 K)).adicCompletion K) :
    Valued.v (finiteCompletionMap K E w x) =
      Valued.v x ^ ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal) := by
  have he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, zero_pow he]
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K (w.under (𝓞 K))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set m := WithZero.log (Valued.v x)
  set k : K := π ^ (-m)
  have hvk : (w.under (𝓞 K)).valuation K k = Valued.v x := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, neg_mul_neg, mul_one]
    exact WithZero.exp_log hx0
  set c : (w.under (𝓞 K)).adicCompletion K := algebraMap K _ k
  have hc : Valued.v c = Valued.v x := (valued_algebraMap (w.under (𝓞 K)) k).trans hvk
  have hc0 : c ≠ 0 := fun h => hx0 (by rw [← hc, h, map_zero])
  set u := x * c⁻¹
  have hu0 : u ≠ 0 := mul_ne_zero hx (inv_ne_zero hc0)
  have hu : Valued.v u = 1 := by
    rw [map_mul, map_inv₀, hc, mul_inv_cancel₀ hx0]
  have hu1 : u ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have hu2 : u⁻¹ ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have a1 := finiteCompletionMap_mapsTo K E w hu1
  have a2 := finiteCompletionMap_mapsTo K E w hu2
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at a1 a2
  have hfu : Valued.v (finiteCompletionMap K E w u) = 1 := by
    have hprod : finiteCompletionMap K E w u * finiteCompletionMap K E w u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have h3 := congrArg Valued.v hprod
    rw [map_mul, map_one] at h3
    exact eq_one_of_one_le_mul_left a1 a2 h3.ge
  have hxu : x = u * c := by
    simp only [u, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  conv_lhs => rw [hxu, map_mul, map_mul, hfu, one_mul, finiteCompletionMap_coe, valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 K)) w k, hvk]
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot]

theorem factor_upIdele (t : (Af K)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((upIdele K E t : Af E) w)) =
      (((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : ℝ) ^
          WithZero.log (Valued.v ((t : Af K) (w.under (𝓞 K))))) ^
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  haveI := w.isMaximal
  haveI := (w.under (𝓞 K)).isMaximal
  have h1 : ((upIdele K E t : Af E) w) = finiteCompletionMap K E w ((t : Af K) (w.under (𝓞 K))) := rfl
  rw [h1, valued_finiteCompletionMap, WithZero.log_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 K)).asIdeal (w.under (𝓞 K)).isPrime
      (w.under (𝓞 K)).ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring


open Classical in
theorem sum_fiber (v : HeightOneSpectrum (𝓞 K)) (s : Finset (HeightOneSpectrum (𝓞 E)))
    (hs : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v → w ∈ s) :
    ∑ w ∈ s with w.under (𝓞 K) = v, w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) =
      Module.finrank K E := by
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E, ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine Finset.sum_bij'
    (fun w hw => (⟨w.asIdeal, w.isPrime, by
      rw [← (Finset.mem_filter.mp hw).2]
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under K E w⟩ : v.asIdeal.primesOver (𝓞 E)))
    (fun q _ => (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)))
    (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hq : (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 K) = v :=
    HeightOneSpectrum.ext q.2.2.over.symm
  exact Finset.mem_filter.mpr ⟨hs _ hq, hq⟩

theorem modF_upIdele (t : (Af K)ˣ) : modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  classical
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((t : Af K) v)) with ha
  have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}.Finite :=
    Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp t.isUnit).2
  have hT : ((fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 K)) ⁻¹'
      {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}).Finite := by
    have h2 := Filter.mem_cofinite.mp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K E hfin.compl_mem_cofinite)
    rwa [Set.preimage_compl, compl_compl] at h2
  set S := hfin.toFinset
  set T := hT.toFinset
  have haS : ∀ v, v ∉ S → a v = 1 := fun v hv => by
    have h3 : Valued.v ((t : Af K) v) = 1 := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr h)
    simp only [ha, h3, WithZero.log_one, zpow_zero]
  have h1 : modF t = ∏ v ∈ S, a v := by
    refine finprod_eq_prod_of_mulSupport_subset a fun v hv => ?_
    by_contra h
    exact hv (haS v h)
  have h2 : modF (upIdele K E t) = ∏ w ∈ T, a (w.under (𝓞 K)) ^
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
    unfold modF
    rw [finprod_congr (factor_upIdele t)]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    by_contra h
    apply hw
    have h4 : w.under (𝓞 K) ∉ S := fun h5 => h (hT.mem_toFinset.mpr (hfin.mem_toFinset.mp h5))
    show a (w.under (𝓞 K)) ^ _ = 1
    rw [haS _ h4, one_pow]
  rw [h2, h1, ← Finset.prod_fiberwise_of_maps_to (s := T) (t := S) (g := fun w => w.under (𝓞 K))
    (fun w hw => hfin.mem_toFinset.mpr (hT.mem_toFinset.mp hw)), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Finset.prod_congr rfl (g := fun w => a v ^ (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)))
      (fun w hw => by rw [(Finset.mem_filter.mp hw).2]),
    Finset.prod_pow_eq_pow_sum, sum_fiber v T fun w hw => hT.mem_toFinset.mpr (by
      show w.under (𝓞 K) ∈ {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}
      rw [hw]; exact hfin.mem_toFinset.mp hv)]

end GlobalTheory.UpIdeleMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtensionStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modF_finiteIdeleUpToExtension : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  first | exact @GlobalTheory.UpIdeleMod.modF_upIdele | exact GlobalTheory.UpIdeleMod.modF_upIdele | (intros; apply GlobalTheory.UpIdeleMod.modF_upIdele <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSemilocalHomLatticeClassesMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSemilocalHomLatticeClassesMod
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.SemilocalClasses

theorem card_finset_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
    (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
    (h0 : ∀ x : A, π (n • x) = 0) (s : Finset Q) : s.card ≤ n ^ Module.finrank ℚ V := by
  classical
  obtain ⟨σ, hσ⟩ := hπ.hasRightInverse
  let F : Submodule ℤ A := Submodule.span ℤ (↑(s.image σ) : Set A)
  haveI : Module.Finite ℤ F := Module.Finite.span_of_finite ℤ (Finset.finite_toSet _)
  let g : F →ₗ[ℤ] V := f.toIntLinearMap ∘ₗ F.subtype
  have hg : Function.Injective g := hf.comp F.subtype_injective
  haveI : HasUniqueDiv V := HasUniqueDiv.of_module_rat V
  haveI : Module.IsTorsionFree ℤ F := Function.Injective.moduleIsTorsionFree g hg (by simp)
  haveI : Module.Free ℤ F := Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank ℤ F ≤ Module.finrank ℚ V := by
    let b := Module.finBasis ℤ F
    have h1 : LinearIndependent ℤ (g ∘ b) := b.linearIndependent.map' g (LinearMap.ker_eq_bot.2 hg)
    have h2 : LinearIndependent ℚ (g ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h1
    simpa using h2.fintype_card_le_finrank
  let p : F →+ Q := π.comp F.subtype.toAddMonoidHom
  have hle : (nsmulAddMonoidHom (α := F) n).range ≤ p.ker := by
    rintro _ ⟨x, rfl⟩
    simpa [p] using h0 x
  have hidx : (nsmulAddMonoidHom (α := F) n).range.index = n ^ Module.finrank ℤ F :=
    AddSubgroup.index_range_nsmul F n
  have hpos : 0 < n ^ Module.finrank ℤ F := pow_pos hn _
  have hdvd : p.ker.index ∣ n ^ Module.finrank ℤ F := hidx ▸ AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_ker] at hdvd
  have hne : Nat.card p.range ≠ 0 := fun h => by
    rw [h] at hdvd; exact hpos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  haveI : Finite p.range := Nat.finite_of_card_ne_zero hne
  have hsub : (↑s : Set Q) ⊆ (p.range : Set Q) := fun q hq =>
    ⟨⟨σ q, Submodule.subset_span (by simpa using ⟨q, hq, rfl⟩)⟩, hσ q⟩
  calc s.card = Nat.card (↑s : Set Q) := by simp
    _ ≤ Nat.card p.range := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ n ^ Module.finrank ℤ F := Nat.le_of_dvd hpos hdvd
    _ ≤ n ^ Module.finrank ℚ V := Nat.pow_le_pow_right hn hr

theorem finite_card_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
    (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
    (h0 : ∀ x : A, π (n • x) = 0) : Finite Q ∧ Nat.card Q ≤ n ^ Module.finrank ℚ V := by
  have h := card_finset_le f hf π hπ n hn h0
  have hfin : Finite Q := by
    by_contra hinf
    haveI : Infinite Q := not_finite_iff_infinite.1 hinf
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq Q (n ^ Module.finrank ℚ V + 1)
    have := h s
    omega
  refine ⟨hfin, ?_⟩
  haveI := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card]
  exact h Finset.univ

theorem finite_card_classes : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ∧ Nat.card (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ≤ (cA * c) ^ (Module.finrank ℚ E * a * b) := by
  intro E _ _ _ a b S L L' cA c _ _ hA hc
  haveI : Module.Finite ℚ (HomE E a b) := Module.Finite.trans E (HomE E a b)
  have hd : Module.finrank ℚ (HomE E a b) = Module.finrank ℚ E * a * b := by
    rw [← Module.finrank_mul_finrank ℚ E (HomE E a b), Module.finrank_linearMap]
    simp [mul_assoc]
  rw [← hd]
  refine finite_card_le (divLat cA (homAt S L L')).subtype.toAddMonoidHom (Submodule.subtype_injective _)
    ((mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype).mkQ.toAddMonoidHom
    (Submodule.mkQ_surjective _) (cA * c) (Nat.mul_pos hA hc) fun x => ?_
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨(cA : 𝓞 E) • (x : HomE E a b), x.2, ?_⟩
  show (c : 𝓞 E) • (cA : 𝓞 E) • (x : HomE E a b) = (cA * c) • (x : HomE E a b)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, mul_nsmul]

end GlobalTheory.SemilocalClasses
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSemilocalHomLatticeClassesModStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_semilocal_hom_lattice_classes_mod : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ∧ Nat.card (↥(divLat cA (homAt S L L')) ⧸ (mulLat c (homAt S L L')).comap (divLat cA (homAt S L L')).subtype) ≤ (cA * c) ^ (Module.finrank ℚ E * a * b) := by
  first | exact @GlobalTheory.SemilocalClasses.finite_card_classes | exact GlobalTheory.SemilocalClasses.finite_card_classes | (intros; apply GlobalTheory.SemilocalClasses.finite_card_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem pairVr_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] (emb : ι → E →+* K) {n : ℕ}
    (lam : ι → DomWeight n) :
    pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) = pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) := by
  have e : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  rw [← e]
  rfl

theorem gram_posSemidef_and_sqAt : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  intro E K _ _ _ _ _ ι _ emb n lam σ
  rw [pairVr_one_eq]
  refine ⟨?_, fun x => ?_⟩
  · simp only [GlobalTheory.PeriodClassSum.pairK_one_basis]
    exact (GlobalTheory.PeriodClassSum.gramB_posDef lam σ).posSemidef
  · unfold sqAt
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, ← Complex.conj_re]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

end GlobalTheory.ColNorms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  first | exact @GlobalTheory.ColNorms.gram_posSemidef_and_sqAt | exact GlobalTheory.ColNorms.gram_posSemidef_and_sqAt | (intros; apply GlobalTheory.ColNorms.gram_posSemidef_and_sqAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulOfValLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {V : Type} [CommRing V] [IsDomain V]

theorem torsion_points (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) :
    ∃ x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
      (∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
        (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧
      ∀ z : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :=
    (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :) (by simp)) ρ.pt (S.r * S.N)
    ρ.pt_add (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

theorem frames (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) (lb : LBIso A.L (ρ.P.L.pull φ))
    (x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A))
    (hx : ∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
      (ρ.pt a).left) :
    ∃ (rig : LB.Gen (A.L.pull (eSec A.A)))
      (e : ∀ a, LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) (AlgebraicClosure (FractionRing V))).left) (K := Fin 1)
        (fun _ => (x a).left) (fun _ => 1))),
      rig.IsGen ∧ (∀ a, IsTorsFrame A rig (S.r * S.N) (x a) (e a)) ∧
      ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))),
        ∃ t : SecA A (AlgebraicClosure (FractionRing V)) k, ∀ (a : S.Gam) (c : S.R),
          IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) →
          ∀ z J, Good A.L z J → sA t (ptSecT A.A (x a)).left z J =
            @id ((TFK (R := V) (AlgebraicClosure (FractionRing V))).left.presheaf.stalk z)
              (cst (R := V) (AlgebraicClosure (FractionRing V)) z
                ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK c)) *
            (val (powFrame A.A A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  have hh : (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).left ⟶ (baseOver (Sp S.R)).left) ≫ (baseOver (Sp S.R)).hom =
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :=
    (Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _)))
  obtain ⟨rig, e, h₁, h₂, h₃⟩ := GlobalTheory.FrameMove.exists_move (T := baseOver (Sp S.R))
    (T' := TFK (R := V) (AlgebraicClosure (FractionRing V))) cart lb hh ρ.rig_gen hx ρ.fr_tors
  refine ⟨rig, e, h₁, h₂, fun k σ => ?_⟩
  obtain ⟨t, ht⟩ := h₃ k σ
  exact ⟨t, fun a c hc z J hJ => (ht a _ hc z J hJ).trans (congrArg (· * _) (GlobalTheory.FrameMove.gs_spMap _ z c))⟩

end GlobalTheory.ThetaDvr
end

namespace GlobalTheory.ThetaDvr

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_mul_of_val_le {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {x y : FractionRing V} (hy : y ≠ 0)
    (h : v (algebraMap (FractionRing V) F y) ≤ v (algebraMap (FractionRing V) F x)) :
    ∃ w : V, x = algebraMap V (FractionRing V) w * y ∧
      (v (algebraMap (FractionRing V) F y) < v (algebraMap (FractionRing V) F x) → w ∈ IsLocalRing.maximalIdeal V) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero, zero_mul], fun _ => zero_mem _⟩
  obtain ⟨n, u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ x hx
  obtain ⟨m, u', hu'⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ y hy
  have hn := hv x n ⟨u, hu⟩
  have hm := hv y m ⟨u', hu'⟩
  rw [hn, hm, WithTop.coe_le_coe, Int.cast_le] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hu'1 : algebraMap V (FractionRing V) (↑u'⁻¹ : V) * algebraMap V (FractionRing V) (u' : V) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨ϖ ^ k * u * ↑u'⁻¹, ?_, fun hlt => ?_⟩
  · rw [hu, hu', hk, zpow_add₀ hϖ0, zpow_natCast, map_mul, map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) ϖ ^ k *
      algebraMap V (FractionRing V) (u : V))) * hu'1
  · rw [hn, hm, WithTop.coe_lt_coe, Int.cast_lt] at hlt
    have hk0 : k ≠ 0 := by omega
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ?_ k (Nat.pos_of_ne_zero hk0)))
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.ThetaDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetDecoSetLatticeReps
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory

namespace DecoLatticeClasses

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def unitEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinearMap (Matrix.mulVecLin γ.conjTranspose) (Matrix.mulVecLin γ)
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])

theorem unitEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    unitEquiv γ h ∈ UF E n := by
  intro x y
  change star (γ.conjTranspose.mulVec x) ⬝ᵥ (γ.conjTranspose.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem mem_one_iff [NumberField E] (a : E) :
    a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

end DecoLatticeClasses


open DecoLatticeClasses in
theorem exists_finset_decoSet_lattice_reps :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    ∃ Rs : Finset (Submodule (𝓞 E) (Sp E n)),
      (Rs.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
        ∃ g : UF E n,
          (((g, (1 : GLG (E := E) (n := n) (SG := SG))) • d :
            DecoSet (E := E) (n := n) (ST := ST) (SG := SG))).1.N ∈ Rs := by
  intro E _ _ _ _ hs n
  obtain ⟨R, hR, H⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr E n
  refine ⟨R, hR, fun ST SG d => ?_⟩
  have hu : Formalism.HermitianLatticesTheory.dual (hStd E n) d.1.N = d.1.N := d.2.uni
  have hspan : Submodule.span E (d.1.N : Set (Sp E n)) = ⊤ := by
    let W := Submodule.span E (d.1.N : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    -- Self-duality puts the whole line through the orthogonal vector in the lattice.
    have hsmul (a : E) : a • e x ∈ d.1.N := by
      rw [← hu, mem_dual]
      intro y hy
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      rw [map_smul, hStd_isSymm.isRefl (e x) y hxy, smul_zero]
      exact Submodule.zero_mem _
    let i : E →ₗ[𝓞 E] d.1.N :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict d.1.N hsmul
    let : Module.Finite (𝓞 E) d.1.N := Module.Finite.iff_fg.mpr d.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H d.1.N d.2.lat.fg hspan (fun y => by
    conv_lhs => rw [← hu, mem_dual]
    simp only [mem_one_iff, hStd_apply, hs])
  have hγ' : γ * γ.conjTranspose = 1 := by
    rw [← hγ]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hs]
  refine ⟨⟨unitEquiv γ hγ', unitEquiv_mem γ hγ'⟩, ?_⟩
  have e : Formalism.HermitianLatticesTheory.gmap (unitEquiv γ hγ') d.1.N = L₀ := by
    ext x
    rw [mem_gmap, hm]
    rfl
  rw [← e] at hL₀
  exact hL₀

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.CurveTransport

open GlobalTheory.EllipticCM GlobalTheory.ConjPoint _root_.WeierstrassCurve
open GlobalTheory.Idele
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsLatOf IsInvIdealOf)

variable {K : Type} [Field K] [NumberField K]

theorem isLatOf_iff {ι : K →+* ℂ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair} :
    IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ Λ.lattice ↔ ∃ x ∈ 𝔞, ι x = z := by
  rw [IsLatOf, Set.ext_iff]
  rfl

theorem isInvIdealOf_inv_smul_one (t : (Af K)ˣ) :
    IsInvIdealOf t (t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K)) := by
  intro x
  rw [← algebraMap_mem_adelicIdeal (GlobalTheory.Idele.smul_ne_zero _ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)), ← mem_adelicIdeal_one_iff,
    ← mul_mem_adelicIdeal_smul t⁻¹ 1 ((t : Af K) * algebraMap K _ x), Units.inv_mul_cancel_left]

theorem mulEquiv_inv_mk (t : (Af K)ˣ) {x x' : K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) :
    mulEquiv t⁻¹ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) rfl
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x' := by
  rw [mulEquiv_mk_eq_mk_iff_adelic]
  have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
      ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
    rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
    ring
  rw [e, mul_mem_adelicIdeal_smul]
  exact neg_mem (mem_adelicIdeal_one_iff.2 h)

theorem exists_curve_torsTransport : ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K],
    Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ →
    Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra;
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  intro K _ _ _ _ ι Λ₀ Ω₀ hΛ₀ hΩ₀
  letI : Algebra K ℂ := ι.toAlgebra
  have hAlg : ∀ y : K, algebraMap K ℂ y = ι y := fun _ => rfl
  have hsubIff : ∀ {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair},
      (IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ idealSub 𝔞 ↔ z ∈ Λ.lattice) := fun {𝔞 Λ} => by
    rw [isLatOf_iff]
    exact forall_congr' fun z => by rw [mem_idealSub]; exact Iff.comm
  let M := GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀
  have hM : GlobalTheory.IsHomothetic Ω₀ Λ₀ M := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have hsub : ∀ z, z ∈ idealSub (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ Ω₀ * z ∈ M.lattice := fun z => by
    rw [hM z]; exact hsubIff.1 hΛ₀ z
  obtain ⟨ξ, hξ, hξz⟩ := exists_isAnalyticIso (X := latticeCurve M) (C := 1) (one_smul _ _) hΩ₀ hsub
  refine ⟨latticeCurve M, inferInstance, ξ, hξ, fun σ t ht => ?_⟩
  obtain ⟨η, ⟨hη, hηx⟩, -⟩ := ht
  obtain ⟨L', g2, g3⟩ := GlobalTheory.CMRam.exists_conj_lattice σ.toRingEquiv M
  have h' : (1 : VariableChange ℂ) • (latticeCurve M).map (σ : ℂ →+* ℂ) = latticeCurve L' := by
    rw [one_smul]
    simp [latticeCurve, WeierstrassCurve.map, g2, g3, map_ofNat]
  obtain ⟨α, hα0, hα, hηα⟩ := hη.exists_mul h'
  let Λ₁ := GlobalTheory.scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁ : GlobalTheory.IsHomothetic α⁻¹ L' Λ₁ := GlobalTheory.isHomothetic_scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁' : GlobalTheory.IsHomothetic α Λ₁ L' := fun z => by
    rw [← hΛ₁ (α * z), ← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
  have hlat1 : IsLatOf ι (t⁻¹ • 1) Λ₁ := hsubIff.2 fun z => by rw [hα, hΛ₁' z]
  refine ⟨Λ₁, α, hΩ₀, hα0, fun x => σ.commutes x, hΛ₀, ⟨_, isInvIdealOf_inv_smul_one t, hlat1⟩, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, ← hM.g₂_eq, ← g2, hΛ₁'.g₂_eq, div_eq_inv_mul]
  · rw [div_eq_inv_mul, ← hM.g₃_eq, ← g3, hΛ₁'.g₃_eq, div_eq_inv_mul]
  · intro x x' hx hint
    have e := hηx (Submodule.Quotient.mk x)
    rw [mulEquiv_inv_mk t hint, torsionIncl_mk, torsionIncl_mk, hξz, hηα, hAlg, hAlg] at e
    have hxM : Ω₀ * ι x ∉ M.lattice := fun h => hx ((hM _).1 h)
    rw [latticePoint_of_notMem M hxM] at e
    have hx' : α * ι x' ∉ L'.lattice := by
      intro h
      rw [latticePoint_of_mem L' h, map_zero, variableChangePoint_some] at e
      exact Affine.Point.some_ne_zero _ e
    rw [latticePoint_of_notMem L' hx', variableChangePoint_some, variableChangePoint_some] at e
    change Affine.Point.some _ _ _ = _ at e
    rw [Affine.Point.some.injEq] at e
    simp [VariableChange.one_def] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rw [div_eq_inv_mul, ← hM.weierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.weierstrassP_mul]
      exact e1
    · rw [div_eq_inv_mul, ← hM.derivWeierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.derivWeierstrassP_mul]
      rw [map_ofNat σ 2, div_left_inj' two_ne_zero] at e2
      exact e2

end GlobalTheory.LatVal.CurveTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriodStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod : ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra; ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic) (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point), GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ), GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ → ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  first | exact @GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | exact GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | (intros; apply GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

variable {D : D7}

def frPt {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : D.what₂.Tau → Fin m → Fin n → ℂ :=
  fun τ => (B' τ * Matrix.of (Z τ) * (B τ)⁻¹ : Matrix (Fin m) (Fin n) ℂ)

def sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ := ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2

def gZ (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (Z : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  f (iotaW σ T S (frPt B B' Z)) * Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ)

def thY (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (δ : ℂ)
    (Y : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  gZ σ S T B B' f (δ⁻¹ • Y)

end GlobalTheory.VacRealForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SwapPairing

theorem weilIs_swap_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift 1 u) (lift v 1) c → Out.WeilIs (G2 A) P n (lift u 1) (lift 1 v) c' → c = c' := by
  intro S A _ _ P hA hP hiso n T u v c c' h h'
  let ψ : G2 A ⟶ G2 A := lift (snd A A) (fst A A)
  haveI : IsMonHom ψ := inferInstanceAs (IsMonHom (lift (snd A A) (fst A A)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hx : lift u 1 ≫ ψ = lift 1 u := by ext <;> simp [ψ]
  have hy : lift 1 v ≫ ψ = lift v 1 := by ext <;> simp [ψ]
  have hw : LBIso (lbPow P 1) (P.pull ψ.left) :=
    LBIso.trans (isLB_lbPow hP 1) hP (pull_isLB hP _) (lbIso_lbPow_one hP) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift u 1) (y := lift 1 v)
    globalFns_holds hAA hP hP ψ hw (by rw [hx, hy]; exact h)
  rw [Nat.cast_one, _root_.mul_one] at h1
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hP h1 h'

end GlobalTheory.SwapPairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift 1 u) (lift v 1) c → Out.WeilIs (G2 A) P n (lift u 1) (lift 1 v) c' → c = c' := by
  first | (exact @GlobalTheory.SwapPairing.weilIs_swap_eq) | (exact GlobalTheory.SwapPairing.weilIs_swap_eq) | (intros; apply GlobalTheory.SwapPairing.weilIs_swap_eq  <;> assumption)
end
end
