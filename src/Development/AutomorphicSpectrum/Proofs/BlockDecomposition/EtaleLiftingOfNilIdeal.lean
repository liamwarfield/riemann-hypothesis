module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtNil

theorem isNilpotent_of_fg_of_le {B : Type} [CommRing B] {J J' : Ideal B}
    (hJ : ∀ x ∈ J, IsNilpotent x) (hfg : J'.FG) (hle : J' ≤ J) : IsNilpotent J' :=
  (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 fun x hx => mem_nilradical.2 (hJ x (hle hx))

theorem exists_lift {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallySmooth P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (g : E →ₐ[P] B ⧸ J) :
    ∃ h : E →ₐ[P] B, (Ideal.Quotient.mkₐ P J).comp h = g := by
  obtain ⟨n, π, hπ, hK⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  choose b hb using fun i => Ideal.Quotient.mk_surjective (g (π (MvPolynomial.X i)))
  let φ : MvPolynomial (Fin n) P →ₐ[P] B := MvPolynomial.aeval b
  have hφ : (Ideal.Quotient.mkₐ P J).comp φ = g.comp π :=
    MvPolynomial.algHom_ext fun i => by simp [φ, hb]
  have hφ' : ∀ p, Ideal.Quotient.mk J (φ p) = g (π p) := fun p => DFunLike.congr_fun hφ p
  let J' : Ideal B := (RingHom.ker π.toRingHom).map φ.toRingHom
  have hle : J' ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun p hp => ?_
    have hp0 : π p = 0 := hp
    refine Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    change Ideal.Quotient.mk J (φ p) = 0
    rw [hφ', hp0, map_zero]
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ (hK.map _) hle
  have hkill : ∀ a ∈ RingHom.ker π, ((Ideal.Quotient.mkₐ P J').comp φ) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ.toRingHom ha)
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let g' : E →ₐ[P] B ⧸ J' :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill).comp
      e.symm.toAlgHom
  have hg' : ∀ p, g' (π p) = Ideal.Quotient.mk J' (φ p) := fun p => by
    have : e.symm (π p) = Ideal.Quotient.mk (RingHom.ker π) p := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπ p).symm
    change Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill
      (e.symm (π p)) = _
    rw [this]
    rfl
  refine ⟨Algebra.FormallySmooth.lift J' hnil g', AlgHom.ext fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hπ x
  have h1 := Algebra.FormallySmooth.mk_lift J' hnil g' (π p)
  rw [hg', Ideal.Quotient.eq] at h1
  change Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J' hnil g' (π p)) = g (π p)
  rw [← hφ', Ideal.Quotient.eq]
  exact hle h1

theorem lift_unique {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallyUnramified P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (h₁ h₂ : E →ₐ[P] B)
    (H : ∀ x, Ideal.Quotient.mk J (h₁ x) = Ideal.Quotient.mk J (h₂ x)) : h₁ = h₂ := by
  obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  let d : Fin n → B := fun i => h₁ (π (MvPolynomial.X i)) - h₂ (π (MvPolynomial.X i))
  let J' : Ideal B := Ideal.span (Set.range d)
  have hfg : J'.FG := Submodule.fg_span (Set.finite_range d)
  have hle : J' ≤ J := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.Quotient.eq.1 (H _)
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ hfg hle
  have hc : (Ideal.Quotient.mkₐ P J').comp (h₁.comp π) =
      (Ideal.Quotient.mkₐ P J').comp (h₂.comp π) :=
    MvPolynomial.algHom_ext fun i =>
      Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
  refine Algebra.FormallyUnramified.ext J' hnil fun x => ?_
  obtain ⟨p, rfl⟩ := hπ x
  exact DFunLike.congr_fun hc p

end GlobalTheory.CompanionTheory.EtNil

theorem GlobalTheory.CompanionTheory.EtNil.etLift_of_nil : ∀ {B : Type} [CommRing B] (J : Ideal B),
    (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g hg
  letI := ψ.toAlgebra
  letI := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let gA : E →ₐ[P] B ⧸ J :=
    { g with commutes' := fun p => DFunLike.congr_fun hg p }
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.EtNil.exists_lift J hJ gA
  have hh' : ∀ x, Ideal.Quotient.mk J (h x) = g x := fun x => DFunLike.congr_fun hh x
  refine ⟨h.toRingHom, ⟨RingHom.ext fun p => h.commutes p, RingHom.ext hh'⟩, ?_⟩
  rintro h' ⟨h1, h2⟩
  let hA : E →ₐ[P] B := { h' with commutes' := fun p => DFunLike.congr_fun h1 p }
  have : hA = h := GlobalTheory.CompanionTheory.EtNil.lift_unique J hJ hA h fun x => by
    change Ideal.Quotient.mk J (h' x) = _
    rw [hh']
    exact DFunLike.congr_fun h2 x
  exact RingHom.ext fun x => DFunLike.congr_fun this x
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_lifting_of_nil_ideal : ∀ {B : Type} [CommRing B] (J : Ideal B), (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  first | exact @GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | exact GlobalTheory.CompanionTheory.EtNil.etLift_of_nil | (intros; apply GlobalTheory.CompanionTheory.EtNil.etLift_of_nil <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltration
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDFil

variable {B : Type} [CommRing B] {J : Ideal B}

theorem fil_mul_le (δ : DividedPowers J) (a c : ℕ) :
    GlobalTheory.PDA.fil δ a * GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ (a + c) := by
  unfold GlobalTheory.PDA.fil
  rw [Ideal.span_mul_span']
  refine Ideal.span_mono ?_
  rintro _ ⟨_, ⟨l, hl, hn, rfl⟩, _, ⟨m, hm, hk, rfl⟩, rfl⟩
  refine ⟨l ++ m, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hl p h
    · exact hm p h
  · simp only [List.map_append, List.sum_append]
    omega
  · simp only [List.map_append, List.prod_append]

theorem fil_anti (δ : DividedPowers J) {a c : ℕ} (h : a ≤ c) :
    GlobalTheory.PDA.fil δ c ≤ GlobalTheory.PDA.fil δ a := by
  refine Ideal.span_mono ?_
  rintro b ⟨l, h1, h2, h3⟩
  exact ⟨l, h1, h.trans h2, h3⟩

theorem fil_zero (δ : DividedPowers J) : GlobalTheory.PDA.fil δ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)

theorem dpow_mem_fil (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ GlobalTheory.PDA.fil δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

def coefFil (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Submodule B Q.P where
  carrier := {z | ∀ k, Q.e.repr z k ∈ GlobalTheory.PDA.fil δ (r - k)}
  add_mem' := by
    intro x y hx hy k
    simpa using Ideal.add_mem _ (hx k) (hy k)
  zero_mem' := by
    intro k
    simp
  smul_mem' := by
    intro c x hx k
    simpa using Ideal.mul_mem_left _ c (hx k)

theorem coefFil_anti (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} (h : a ≤ c) {z : Q.P}
    (hz : z ∈ coefFil δ Q c) : z ∈ coefFil δ Q a :=
  fun k ↦ fil_anti δ (by omega) (hz k)

theorem mem_coefFil_zero (δ : DividedPowers J) (Q : PDPoly B) (z : Q.P) :
    z ∈ coefFil δ Q 0 := by
  intro k
  simp [fil_zero]

theorem smul_e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r k : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (r - k)) : b • Q.e k ∈ coefFil δ Q r := by
  intro j
  by_cases h : j = k
  · subst h
    simpa using hb
  · have : Q.e.repr (b • Q.e k) j = 0 := by
      simp [Finsupp.single_apply, Ne.symm h]
    rw [this]
    exact Ideal.zero_mem _

theorem eq_sum_repr (Q : PDPoly B) (z : Q.P) :
    z = ∑ k ∈ (Q.e.repr z).support, Q.e.repr z k • Q.e k := by
  conv_lhs => rw [← Q.e.linearCombination_repr z]
  rfl

theorem smul_e_mul_smul_e_mem (δ : DividedPowers J) (Q : PDPoly B) {a c k l : ℕ} {b b' : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ (a - k)) (hb' : b' ∈ GlobalTheory.PDA.fil δ (c - l)) :
    (b • Q.e k) * (b' • Q.e l) ∈ coefFil δ Q (a + c) := by
  have h1 : b * b' ∈ GlobalTheory.PDA.fil δ (a + c - (k + l)) :=
    fil_anti δ (by omega) (fil_mul_le δ _ _ (Ideal.mul_mem_mul hb hb'))
  rw [smul_mul_smul_comm, Q.e_mul, ← nsmul_eq_mul, smul_comm]
  exact nsmul_mem (smul_e_mem_coefFil δ Q h1) _

theorem mul_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {a c : ℕ} {z w : Q.P}
    (hz : z ∈ coefFil δ Q a) (hw : w ∈ coefFil δ Q c) : z * w ∈ coefFil δ Q (a + c) := by
  rw [eq_sum_repr Q z, eq_sum_repr Q w, Finset.sum_mul_sum]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.sum_mem _ fun l _ ↦
    smul_e_mul_smul_e_mem δ Q (hz k) (hw l)

def coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (r : ℕ) : Ideal Q.P where
  carrier := coefFil δ Q r
  add_mem' := (coefFil δ Q r).add_mem
  zero_mem' := (coefFil δ Q r).zero_mem
  smul_mem' := by
    intro c x hx
    simpa using mul_mem_coefFil δ Q (mem_coefFil_zero δ Q c) hx

theorem algebraMap_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {r : ℕ} {b : B}
    (hb : b ∈ GlobalTheory.PDA.fil δ r) : algebraMap B Q.P b ∈ coefFil δ Q r := by
  have : algebraMap B Q.P b = b • Q.e 0 := by
    rw [Q.e_zero, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact smul_e_mem_coefFil δ Q (by simpa using hb)

theorem e_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) {n m : ℕ} (h : n ≤ m) :
    Q.e m ∈ coefFil δ Q n := by
  have : (1 : B) ∈ GlobalTheory.PDA.fil δ (n - m) := by
    rw [Nat.sub_eq_zero_of_le h, fil_zero]
    trivial
  simpa using smul_e_mem_coefFil δ Q this

theorem e_mem_ext (Q : PDPoly B) (J : Ideal B) (k : ℕ) : Q.e (k + 1) ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)

theorem dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) {y : Q.P} (hy : y ∈ Q.ext J) (n : ℕ) :
    η.dpow n y ∈ coefFil δ Q n := by
  let S : Ideal Q.P :=
    { carrier := {y | y ∈ Q.ext J ∧ ∀ n, η.dpow n y ∈ coefFil δ Q n}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Ideal.add_mem _ hx hy, fun n ↦ ?_⟩
        rw [η.dpow_add hx hy]
        refine Submodule.sum_mem _ fun p hp ↦ ?_
        have := mul_mem_coefFil δ Q (hx' p.1) (hy' p.2)
        rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hp] at this
      zero_mem' := by
        refine ⟨Ideal.zero_mem _, fun n ↦ ?_⟩
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact mem_coefFil_zero δ Q _
        · rw [η.dpow_eval_zero hn.ne']
          exact Submodule.zero_mem _
      smul_mem' := by
        rintro a y ⟨hy, hy'⟩
        refine ⟨Ideal.mul_mem_left _ a hy, fun n ↦ ?_⟩
        rw [smul_eq_mul, η.dpow_mul hy]
        exact (coefIdeal δ Q n).mul_mem_left _ (hy' n) }
  have hS : Q.ext J ≤ S := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun j hj ↦ ?_) (Ideal.span_le.2 ?_)
    · refine ⟨Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj), fun n ↦ ?_⟩
      rw [h.dp.dpow_comp j hj]
      exact algebraMap_mem_coefFil δ Q (dpow_mem_fil δ n hj)
    · rintro _ ⟨k, rfl⟩
      have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
      refine ⟨e_mem_ext Q J k, fun n ↦ ?_⟩
      show η.dpow n (Q.e (k + 1)) ∈ coefFil δ Q n
      rw [← h.var (k + 1), η.dpow_comp (Nat.succ_ne_zero k) h1, h.var, ← nsmul_eq_mul]
      exact nsmul_mem (e_mem_coefFil δ Q (Nat.le_mul_of_pos_right n (Nat.succ_pos k))) _
  exact (hS hy).2 n

theorem prod_dpow_mem_coefFil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (l : List (ℕ × Q.P)) (hl : ∀ p ∈ l, p.2 ∈ Q.ext J) :
    (l.map fun p ↦ η.dpow p.1 p.2).prod ∈ coefFil δ Q (l.map Prod.fst).sum := by
  induction l with
  | nil => simpa using mem_coefFil_zero δ Q 1
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact mul_mem_coefFil δ Q (dpow_mem_coefFil δ Q η h (hl p (by simp)) p.1)
      (ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq))

theorem fil_le_coefIdeal (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) : GlobalTheory.PDA.fil η r ≤ coefIdeal δ Q r := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hn, rfl⟩
  exact coefFil_anti δ Q hn (prod_dpow_mem_coefFil δ Q η h l hl)

theorem algebraMap_mem_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {b : B} (hb : b ∈ GlobalTheory.PDA.fil δ r) :
    algebraMap B Q.P b ∈ GlobalTheory.PDA.fil η r := by
  have : (GlobalTheory.PDA.fil δ r).map (algebraMap B Q.P) ≤ GlobalTheory.PDA.fil η r := by
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro _ ⟨l, hl, hn, rfl⟩
    have hmem : ∀ p ∈ l, algebraMap B Q.P p.2 ∈ Q.ext J := fun p hp ↦
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hl p hp))
    have key : algebraMap B Q.P (l.map fun p ↦ δ.dpow p.1 p.2).prod =
        ((l.map fun p ↦ (p.1, algebraMap B Q.P p.2)).map fun p ↦ η.dpow p.1 p.2).prod := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p hp ↦ ?_
      exact (h.dp.dpow_comp p.2 (hl p hp)).symm
    show algebraMap B Q.P _ ∈ GlobalTheory.PDA.fil η r
    rw [key]
    refine Ideal.subset_span ⟨_, ?_, ?_, rfl⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hmem q hq
    · simpa [List.map_map, Function.comp_def] using hn
  exact this (Ideal.mem_map_of_mem _ hb)

theorem coefFil_le_fil (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (r : ℕ) {z : Q.P} (hz : z ∈ coefFil δ Q r) : z ∈ GlobalTheory.PDA.fil η r := by
  rw [eq_sum_repr Q z]
  refine Ideal.sum_mem _ fun k _ ↦ ?_
  have h1 : Q.e 1 ∈ Q.ext J := e_mem_ext Q J 0
  have hk : Q.e k ∈ GlobalTheory.PDA.fil η k := by
    rw [← h.var k]
    exact dpow_mem_fil η k h1
  rw [Algebra.smul_def]
  exact fil_anti η (by omega)
    (fil_mul_le η _ _ (Ideal.mul_mem_mul (algebraMap_mem_fil δ Q η h _ (hz k)) hk))

theorem fil_pdPoly : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  intro B _ J δ Q η h
  exact ⟨fil_mul_le δ, fun _ _ hac ↦ fil_anti δ hac, fil_zero δ, fun r z ↦
    ⟨fun hz ↦ fil_le_coefIdeal δ Q η h r hz, fun hz ↦ coefFil_le_fil δ Q η h r hz⟩⟩

end GlobalTheory.CompanionTheory.PDFil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltrationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_polynomial_filtration : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  first | exact @GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | exact GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | (intros; apply GlobalTheory.CompanionTheory.PDFil.fil_pdPoly <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedDividedPowers
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDMap

variable {B : Type} [CommRing B] {J : Ideal B}

theorem fil_anti (δ : DividedPowers J) {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m := by
  refine Ideal.span_mono ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact ⟨l, h1, h.trans h2, rfl⟩

theorem fil_zero_top (δ : DividedPowers J) : fil δ 0 = ⊤ := by
  refine (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], ?_, ?_, ?_⟩) <;> simp

theorem dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n := by
  refine Ideal.subset_span ⟨[(n, x)], ?_, ?_, ?_⟩ <;> simp [hx]

theorem fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ⟨l, h1, h2, rfl⟩, b, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h1 p hp
    · exact h1' p hp
  · simpa using Nat.add_le_add h2 h2'
  · simp

theorem map_fil_le' {C : Type} [CommRing C] {J' : Ideal C} (δ : DividedPowers J) (δ' : DividedPowers J')
    (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) : (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

theorem fil_le_map {C : Type} [CommRing C] (δ : DividedPowers J) (f : B →+* C)
    (δ' : DividedPowers (J.map f)) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    fil δ' N ≤ (fil δ N).map f := by
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (fil_mul_le δ m n)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (dpow_mem_fil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (fil_anti δ h2) (hprod l h1)

theorem extended_dividedPowers : ∀ {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} (δ : DividedPowers J) (φ : B →+* B') (δ' : DividedPowers (J.map φ)), IsDPMorphism δ δ' φ → (∀ r, fil δ' r = (fil δ r).map φ) ∧ ∀ {B'' : Type} [CommRing B''] {J'' : Ideal B''} (δ'' : DividedPowers J'') (ψ : B' →+* B''), IsDPMorphism δ δ'' (ψ.comp φ) → IsDPMorphism δ' δ'' ψ := by
  intro B B' _ _ J δ φ δ' hφ
  refine ⟨fun r ↦ le_antisymm (fil_le_map δ φ δ' hφ r) (map_fil_le' δ δ' φ hφ r), ?_⟩
  intro B'' _ J'' δ'' ψ hψ
  refine IsDPMorphism.on_span δ' δ'' (S := φ '' (J : Set B)) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hψ.ideal_comp (Ideal.mem_map_of_mem (ψ.comp φ) ha)
  · rintro n _ ⟨a, ha, rfl⟩
    have h1 := hφ.dpow_comp (n := n) a ha
    have h2 := hψ.dpow_comp (n := n) a ha
    rw [h1]
    exact h2.symm

end GlobalTheory.CompanionTheory.PDMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueLiftOfNilpotent
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem existsUnique_lift_of_nilpotent {P E C D : Type} [CommRing P] [CommRing E] [CommRing C] [CommRing D]
    (ψ : P →+* E) (hψ : ψ.Etale) (u : C →+* D) (hu : Function.Surjective u)
    (hn : IsNilpotent (RingHom.ker u)) (f : P →+* C) (g : E →+* D) (h : g.comp ψ = u.comp f) :
    ∃! l : E →+* C, l.comp ψ = f ∧ u.comp l = g := by
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P C := f.toAlgebra
  letI : Algebra P D := (u.comp f).toAlgebra
  haveI : Algebra.Etale P E := hψ
  let uA : C →ₐ[P] D := { u with commutes' := fun _ => rfl }
  let gA : E →ₐ[P] D := { g with commutes' := fun r => congrArg (fun t : P →+* D => t r) h }
  have hn₁ : IsNilpotent (RingHom.ker (uA : C →+* D)) := hn
  have hn₂ : IsNilpotent (RingHom.ker uA) := hn
  let lA : E →ₐ[P] C := Algebra.FormallySmooth.liftOfSurjective gA uA hu hn₁
  have hl : ∀ x, u (lA x) = g x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply gA uA hu hn₂ x
  refine ⟨(lA : E →+* C), ⟨RingHom.ext fun r => lA.commutes r, RingHom.ext hl⟩, ?_⟩
  rintro l' ⟨h1, h2⟩
  let lA' : E →ₐ[P] C := { l' with commutes' := fun r => congrArg (fun t : P →+* C => t r) h1 }
  have : lA' = lA := Algebra.FormallyUnramified.ext' u hn lA' lA fun x => by
    rw [hl]; exact congrArg (fun t : E →+* D => t x) h2
  exact congrArg (fun t : E →ₐ[P] C => (t : E →+* C)) this

variable {B : Type} [CommRing B] (J : Ideal B)

abbrev toBase (n : ℕ) : B ⧸ J ^ (n + 1) →+* B ⧸ J :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))

theorem isNilpotent_ker_toBase (n : ℕ) : IsNilpotent (RingHom.ker (toBase J n)) := by
  refine ⟨n + 1, ?_⟩
  have hk : RingHom.ker (toBase J n) = J.map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    rw [Ideal.Quotient.factor_ker]
  rw [hk, ← Ideal.map_pow]
  simp

theorem existsUnique_level {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E) (hψ : ψ.Etale)
    (f : P →+* B) (g : E →+* B ⧸ J) (h : g.comp ψ = (Ideal.Quotient.mk J).comp f) (n : ℕ) :
    ∃! l : E →+* B ⧸ J ^ (n + 1), l.comp ψ = (Ideal.Quotient.mk _).comp f ∧ (toBase J n).comp l = g :=
  existsUnique_lift_of_nilpotent ψ hψ (toBase J n) (Ideal.Quotient.factor_surjective _)
    (isNilpotent_ker_toBase J n) _ g h

theorem iInf_pow_eq_bot (hJ : IsAdicComplete J B) : ⨅ i : ℕ, J ^ i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  refine (Ideal.mem_bot).2 (IsHausdorff.haus hJ.toIsHausdorff x fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact (Ideal.mem_iInf.1 hx) n

end GlobalTheory.CompanionTheory.EtaleLift


open GlobalTheory.CompanionTheory.EtaleLift in
theorem GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete :
    ∀ {B : Type} [CommRing B] (J : Ideal B), IsAdicComplete J B → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g h
  haveI := hJ
  choose l hl hu using existsUnique_level J ψ hψ f g h
  have hcomp : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J (Nat.succ_le_succ hle)).comp (l n) = l m := by
    intro m n hle
    refine (hu m _ ⟨?_, ?_⟩).symm ▸ rfl
    · rw [RingHom.comp_assoc, (hl n).1]
      rfl
    · rw [← (hl n).2, ← RingHom.comp_assoc]
      congr 1
      exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let F : (n : ℕ) → E →+* B ⧸ J ^ n := fun n => (Ideal.Quotient.factorPow J (Nat.le_succ n)).comp (l n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (F n) = F m := by
    intro m n hle
    simp only [F]
    rw [← hcomp hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let H : E →+* B := IsAdicComplete.liftRingHom J F hF
  have hH : ∀ n x, Ideal.Quotient.mk (J ^ n) (H x) = F n x := fun n x =>
    IsAdicComplete.mk_liftRingHom J F hF n x
  have h1 : H.comp ψ = f := by
    ext p
    rw [← sub_eq_zero]
    refine IsHausdorff.haus hJ.toIsHausdorff _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      RingHom.comp_apply, hH, sub_eq_zero]
    have := congrArg (fun t : P →+* B ⧸ J ^ (n + 1) => Ideal.Quotient.factorPow J (Nat.le_succ n) (t p)) (hl n).1
    exact this
  have h2 : (Ideal.Quotient.mk J).comp H = g := by
    ext x
    have e1 : (toBase J 0).comp (Ideal.Quotient.factorPow J (Nat.le_succ 1)) = toBase J 1 :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    have e2 : Ideal.Quotient.mk J (H x) = toBase J 0 (F 1 x) := by
      rw [← hH 1 x]
      rfl
    rw [RingHom.comp_apply, e2, ← (hl 1).2, ← e1]
    rfl
  refine ⟨H, ⟨h1, h2⟩, ?_⟩
  rintro H' ⟨h1', h2'⟩
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P B := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let A : E →ₐ[P] B := { H with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1 }
  let A' : E →ₐ[P] B := { H' with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1' }
  have : A' = A := Algebra.FormallyUnramified.ext_of_iInf J (iInf_pow_eq_bot J hJ) fun x => by
    exact (congrArg (fun t : E →+* B ⧸ J => t x) h2').trans (congrArg (fun t : E →+* B ⧸ J => t x) h2).symm
  exact congrArg (fun t : E →ₐ[P] B => (t : E →+* B)) this
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantToZModPow
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Per
namespace PeriodicSumRangeMul

private lemma per {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (h : ∀ (i : ℕ), g (i + P) = g i) (k x : ℕ) : g (k * P + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]

end PeriodicSumRangeMul

theorem UpperTheory.Reformulated.B.Yra7.main :
    ∀ {N : Type} [inst : AddCommGroup N] (g : ℕ → N) (P : ℕ),
      (∀ (i : ℕ), g (i + P) = g i) → ∀ (k : ℕ), ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i := by
  intro N _ g P h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PadicShift

theorem exists_period (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) :
    ∃ m : ℕ, ∀ x y : ℤ_[p], ((p : ℤ_[p]) ^ m) ∣ x - y → f x = f y := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric (s := (Set.univ : Set ℤ_[p]))
    (c := fun v : N => f ⁻¹' {v}) isCompact_univ (fun v => hf.isOpen_fiber v)
    (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ hp)
  refine ⟨m, fun x y hxy => ?_⟩
  obtain ⟨i, hi⟩ := h x (Set.mem_univ _)
  have hx : f x = i := hi (Metric.mem_ball_self hδ)
  have hy : f y = i := by
    apply hi
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    have : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ m} := Ideal.mem_span_singleton.2 hxy
    have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) m).2 this
    refine lt_of_le_of_lt h2 (lt_of_eq_of_lt ?_ hm)
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hx, hy]

theorem sum_periodic {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (hg : ∀ i, g (i + P) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i :=
  _root_.UpperTheory.Reformulated.B.Yra7.main g P hg k

theorem isLocallyConstant_toZModPow (p : ℕ) [Fact p.Prime] (M : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) M) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨Metric.closedBall x ((p : ℝ) ^ (-(M : ℤ))),
    IsUltrametricDist.isOpen_closedBall _ (zpow_pos hp _).ne',
    Metric.mem_closedBall_self (zpow_pos hp _).le, fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hy
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) M).1 hy
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1

theorem val_toZModPow_dvd (p : ℕ) [Fact p.Prime] (M : ℕ) (z : ℤ_[p]) :
    ((p : ℤ_[p]) ^ M) ∣ z - (((PadicInt.toZModPow (p := p) M z).val : ℕ) : ℤ_[p]) := by
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_self]

theorem exists_primitive (p : ℕ) [Fact p.Prime] {N : Type} [AddCommGroup N] (n : ℕ)
    (hN : ∀ x : N, p ^ n • x = 0) (f : ℤ_[p] → N) (hf : IsLocallyConstant f) :
    ∃ y : ℤ_[p] → N, IsLocallyConstant y ∧ ∀ z, y (z + 1) - y z = f z := by
  obtain ⟨m, hm⟩ := exists_period p f hf
  set M := n + m with hM
  haveI : NeZero (p ^ M) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let g : ℕ → N := fun i => f (i : ℤ_[p])
  have hper : ∀ i, g (i + p ^ m) = g i := by
    intro i
    apply hm
    refine ⟨1, ?_⟩
    push_cast
    ring
  have hsum : ∑ i ∈ Finset.range (p ^ M), g i = 0 := by
    rw [hM, pow_add, sum_periodic g (p ^ m) hper (p ^ n), hN]
  have hfg : ∀ z, f z = g (PadicInt.toZModPow (p := p) M z).val := by
    intro z
    apply hm
    exact (pow_dvd_pow _ (Nat.le_add_left m n)).trans (val_toZModPow_dvd p M z)
  refine ⟨fun z => ∑ i ∈ Finset.range (PadicInt.toZModPow (p := p) M z).val, g i,
    (isLocallyConstant_toZModPow p M).comp
      (fun a => ∑ i ∈ Finset.range a.val, g i), fun z => ?_⟩
  have hv : (PadicInt.toZModPow (p := p) M z).val < p ^ M := ZMod.val_lt _
  have hval : (PadicInt.toZModPow (p := p) M (z + 1)).val
      = ((PadicInt.toZModPow (p := p) M z).val + 1) % p ^ M := by
    rw [map_add (f := _), map_one, ← ZMod.val_natCast]
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp only [hval]
  rw [hfg z]
  generalize (PadicInt.toZModPow (p := p) M z).val = v at hv
  rcases Nat.lt_or_ge (v + 1) (p ^ M) with h | h
  · rw [Nat.mod_eq_of_lt h, Finset.sum_range_succ, add_sub_cancel_left]
  · have hv1 : v + 1 = p ^ M := by omega
    rw [hv1, Nat.mod_self, Finset.sum_range_zero, zero_sub, neg_eq_iff_add_eq_zero,
      ← Finset.sum_range_succ, hv1]
    exact hsum

theorem eq_of_shift_invariant (p : ℕ) [Fact p.Prime] {N : Type} (f : ℤ_[p] → N)
    (hf : IsLocallyConstant f) (h : ∀ z, f (z + 1) = f z) (z : ℤ_[p]) : f z = f 0 := by
  have hnat : ∀ k : ℕ, f (k : ℤ_[p]) = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, h, ih]
  have hcl : IsClosed {x : ℤ_[p] | f x = f 0} := hf.isClosed_fiber (f 0)
  exact PadicInt.denseRange_natCast.induction_on z hcl hnat

end GlobalTheory.CompanionTheory.PadicShift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftHomExistsUnique
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem lift_hom_existsUnique {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ}
    (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I) (𝓛 : Lift a T Λ I κ) {B : Type} [CommRing B]
    (J : Ideal B) : EtLift J → ∀ (h : Λ →+* B) (g : R →+* B ⧸ J) (u : Fin d → B), I ≤ J.comap h →
    (∀ o x, Ideal.Quotient.mk I x = κ o → g (a o) = Ideal.Quotient.mk J (h x)) →
    (∀ k, Ideal.Quotient.mk J (u k) = g (T k)) →
    ∃! f : 𝓛.D →+* B, f.comp 𝓛.i = h ∧ (∀ k, f (𝓛.t k) = u k) ∧
      ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk J (f z) = g r := by
  intro hEt h g u hIJ hg hu
  obtain ⟨g0, ⟨hg0i, hg0j⟩, hg0u⟩ := 𝓛.univ (B ⧸ J) ((Ideal.Quotient.mk J).comp h) g
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx)) (fun o x hx => hg o x hx)
  have hcomm : g0.comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) =
      (Ideal.Quotient.mk J).comp (MvPolynomial.eval₂Hom h u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hg0i c
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hu k]
      exact hg0j (T k) (𝓛.t k) (𝓛.hT k).symm
  obtain ⟨F, ⟨hFψ, hFg⟩, hFu⟩ :=
    hEt _ _ (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) 𝓛.et (MvPolynomial.eval₂Hom h u) g0 hcomm
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact RingHom.ext fun c => by simpa using RingHom.congr_fun hFψ (MvPolynomial.C c)
  · exact fun k => by simpa using RingHom.congr_fun hFψ (MvPolynomial.X k)
  · intro r z hz
    rw [← hg0j r z hz]
    exact RingHom.congr_fun hFg z
  · rintro f' ⟨hf'i, hf't, hf'j⟩
    apply hFu
    refine ⟨?_, ?_⟩
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact RingHom.congr_fun hf'i c
      · intro k
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        exact hf't k
    · apply hg0u
      refine ⟨?_, ?_⟩
      · rw [RingHom.comp_assoc, hf'i]
      · intro r z hz
        exact hf'j r z hz

end GlobalTheory.CompanionTheory.EtaleLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCastIsUnit
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.RootsDivide

theorem nilp_step {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (hpn : IsNilpotent (p : B))
    (y : B) (h : IsNilpotent (y ^ p - 1)) : IsNilpotent (y - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (y - 1) (1 : B)
  have e1 : (y - 1) ^ p = (y ^ p - 1) - (p : B) * ((y - 1) * r) := by
    have : (y - 1 + 1) = y := by ring
    rw [this] at hr
    rw [hr]; simp only [one_pow]; ring
  refine IsNilpotent.of_pow (m := p) ?_
  rw [e1]
  exact (Commute.all _ _).isNilpotent_sub h ((Commute.all _ _).isNilpotent_mul_right hpn)

theorem nilp_all {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (e : ℕ → B)
    (hpn : IsNilpotent (p : B)) (he : ∀ k, e (k + 1) ^ p = e k)
    (h0 : IsNilpotent (e 0 - 1)) (k : ℕ) : IsNilpotent (e k - 1) := by
  induction k with
  | zero => exact h0
  | succ k ih => exact nilp_step p hp hpn _ (by rw [he]; exact ih)

theorem pow_tower {B : Type} [CommRing B] (p : ℕ) (e : ℕ → B)
    (he : ∀ k, e (k + 1) ^ p = e k) (k n : ℕ) : e (k + n) ^ (p ^ n) = e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, ← add_assoc, he, ih]

theorem natCast_isUnit {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime)
    (hpn : IsNilpotent (p : B)) (c : ℕ) (hc : ¬ p ∣ c) : IsUnit (c : B) := by
  have hcop : IsCoprime (c : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hc).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : B) * (c : B) + (b : B) * (p : B) = 1 := by
    have := congrArg (Int.cast : ℤ → B) hab
    push_cast at this
    exact this
  have h2 : IsUnit ((a : B) * (c : B)) := by
    have : (a : B) * (c : B) = 1 - (b : B) * (p : B) := by rw [← h1]; ring
    rw [this]
    exact ((Commute.all _ _).isNilpotent_mul_left hpn).isUnit_one_sub
  exact isUnit_of_mul_isUnit_right h2

theorem geom_isUnit {B : Type} [CommRing B] (x : B) (hx : IsNilpotent (x - 1)) (n : ℕ)
    (hn : IsUnit (n : B)) : IsUnit (∑ i ∈ Finset.range n, x ^ i) := by
  have hd : (x - 1) ∣ (∑ i ∈ Finset.range n, x ^ i) - (n : B) := by
    have : (∑ i ∈ Finset.range n, x ^ i) - (n : B) = ∑ i ∈ Finset.range n, (x ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    refine Finset.dvd_sum fun i _ => ?_
    simpa using sub_dvd_pow_sub_pow x 1 i
  obtain ⟨t, ht⟩ := hd
  have hnil : IsNilpotent ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    rw [ht]; exact (Commute.all _ _).isNilpotent_mul_right hx
  have : (∑ i ∈ Finset.range n, x ^ i) = (n : B) + ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    ring
  rw [this]
  exact hnil.isUnit_add_left_of_commute hn (Commute.all _ _)

theorem sub_one_dvd : ∀ (p : ℕ), p.Prime → ∀ {B : Type} [CommRing B] (e : ℕ → B),
    IsNilpotent (p : B) → (∀ k, e (k + 1) ^ p = e k) → IsNilpotent (e 0 - 1) →
    ∀ m c : ℕ, ¬ p ^ m ∣ c → (e m ^ c - 1) ∣ (e 1 - 1) := by
  intro p hp B _ e hpn he h0 m c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero _)
  obtain ⟨j, c', hpc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.ne_one
  have hjm : j < m := by
    by_contra hle
    exact hc (Dvd.dvd.mul_right (pow_dvd_pow p (not_lt.1 hle)) c')
  obtain ⟨l, rfl⟩ : ∃ l, m = (l + 1) + j := ⟨m - j - 1, by omega⟩
  set x := e (l + 1) with hxdef
  have hem : e (l + 1 + j) ^ (p ^ j * c') = x ^ c' := by
    rw [pow_mul, pow_tower p e he]
  rw [hem]
  have hxn : IsNilpotent (x - 1) := nilp_all p hp e hpn he h0 _
  have hu : IsUnit (∑ i ∈ Finset.range c', x ^ i) :=
    geom_isUnit x hxn c' (natCast_isUnit p hp hpn c' hpc)
  have hfac : x ^ c' - 1 = (x - 1) * ∑ i ∈ Finset.range c', x ^ i := by
    rw [mul_comm, geom_sum_mul]
  rw [hfac, hu.mul_right_dvd]
  have h1 : x ^ (p ^ l) = e 1 := by
    have := pow_tower p e he 1 l
    rwa [add_comm 1 l] at this
  rw [← h1]
  simpa using sub_dvd_pow_sub_pow x 1 (p ^ l)

end GlobalTheory.CompanionTheory.RootsDivide
end
