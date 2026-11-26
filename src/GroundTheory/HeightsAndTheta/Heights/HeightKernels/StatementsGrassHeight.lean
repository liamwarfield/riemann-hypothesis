module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
public import ReciprocityTheory.ThetaQuasiPeriods.NormInvSmulMemSphere

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

abbrev PlIdx (j m : ℕ) : Type := {I : Finset (Fin (j + m)) // I.card = j}

def plAnchor (j m : ℕ) : PlIdx j m :=
  ⟨Finset.univ.map (Fin.castAddEmb m), by simp⟩

abbrev plBlocks (f j m : ℕ) : Fin f → Type := fun _ => PlIdx j m

abbrev GrassField (f j m : ℕ) : Type := FractionRing (MvPolynomial (Fin f × Fin j × Fin m) ℚ)

def grassPolyCoord (f j m : ℕ) : (Σ _ : Fin f, PlIdx j m) → MvPolynomial (Fin f × Fin j × Fin m) ℚ :=
  fun p => (colsOf (onePipe (fun a b => (X (p.1, a, b) : MvPolynomial (Fin f × Fin j × Fin m) ℚ)))
    p.2).det

def grassCoord (f j m : ℕ) : (Σ _ : Fin f, PlIdx j m) → GrassField f j m :=
  fun p => algebraMap _ _ (grassPolyCoord f j m p)

def grassIdeal (f j m : ℕ) : Ideal (MRing (plBlocks f j m)) :=
  mCoordIdeal (grassCoord f j m)

def fsMulti {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => 1)

def IsRootMatrix {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) : Prop :=
  ∀ τ a b, ∃ k : ℕ, 0 < k ∧ ζ τ a b ^ k = 1

def rootCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) : (Σ _ : Fin f, PlIdx j m) → ℂ :=
  fun p => (colsOf (onePipe (ζ p.1)) p.2).det

def rootPointIdeal {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    Ideal (MRing (plBlocks f j m)) :=
  mCoordIdeal (rootCoord ζ)

def rootFamily (f j m : ℕ) : Set (Ideal (MRing (plBlocks f j m))) :=
  {W | ∃ ζ : Fin f → Matrix (Fin j) (Fin m) ℂ, IsRootMatrix ζ ∧ W = rootPointIdeal ζ}

def grassConst (f j m : ℕ) : ℝ := ((f * j : ℕ) : ℝ) / 2 * Real.log (1 + m)

def rootAnchorSection (f j m : ℕ) : MRing (plBlocks f j m) :=
  ∏ τ : Fin f, X ⟨τ, plAnchor j m⟩

def coneRatios {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) : Set Ω :=
  Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩

def GrassHeightBound.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (f j m : ℕ), 1 ≤ f → ∀ II : IntersectionSystem, IsIntersectionSystem II →
    II (Fin f) (plBlocks f j m) (grassIdeal f j m) (f * j * m + 1) (fun _ => fsMulti (plBlocks f j m)) ≤
      ((f * j * m + 1 : ℕ) : ℝ) * grassConst f j m *
        geomDeg (grassIdeal f j m) (fsMulti (plBlocks f j m)) (f * j * m)

def CoordConeArithVar.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : ℕ) (t : Fin d → Ω),
    Nonempty K → (∀ k, y ⟨k, c k⟩ ≠ 0) → AlgebraicIndependent ℚ t →
    (∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios y c)) →
    (∀ r ∈ coneRatios y c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r) →
    IsArithVar (mCoordIdeal y) (d + 1)

def GrassArithVar.Statement : Prop :=
  ∀ (f j m : ℕ), 1 ≤ f → IsArithVar (grassIdeal f j m) (f * j * m + 1)

def RootArithVar.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → IsRootMatrix ζ →
    IsArithVar (rootPointIdeal ζ) 1

def FsLineSmooth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsSmoothHerm (fsMulti ι)

def FsLineLevi.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z w : (Σ k, ι k) → ℂ),
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 ≤ leviForm (fun z => Real.log ((fsMulti ι).h z)) z w

def FsLineSemipositive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsSemipositiveRel ⊥ P (fsMulti ι)

def NefOfNonneg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ),
    (∀ k, 0 ≤ a k) → NefOnFibres P a

def FsConjInvariant.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsConjInvariantH (fsMulti ι)

def MultiHomogMemCoord.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ),
    IsMultiHomog g a → (g ∈ mCoordIdeal y ↔ aeval y g = 0)

def GrassLeRoot.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), grassIdeal f j m ≤ rootPointIdeal ζ

def RootDense.Statement : Prop :=
  ∀ (f j m : ℕ), IsZariskiDense (grassIdeal f j m) (rootFamily f j m)

def RootAnchorNonzero.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ), ∀ τ, z ⟨τ, plAnchor j m⟩ ≠ 0

def RootPointConj.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ), ∀ τ, ∃ ζ' : Matrix (Fin j) (Fin m) ℂ,
      (∀ a b, ∃ k : ℕ, 0 < k ∧ ζ' a b ^ k = 1) ∧
        ∀ I : PlIdx j m, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * (colsOf (onePipe ζ') I).det

def RootLogNormBound.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ),
      -grassConst f j m ≤ logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z

def RootDivSuppEmpty.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    divSupp (rootPointIdeal ζ) (rootAnchorSection f j m) = ∅

abbrev McClasses {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (W : Ideal (MRing ι)) : Type _ :=
  Quot fun z z' : mcPts W => ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
    (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p

def RootPointsFinite.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    Finite (McClasses (rootPointIdeal ζ))

def RootHeight.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → IsRootMatrix ζ →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (rootPointIdeal ζ) 1 ![fsMulti (plBlocks f j m)] ≤
        grassConst f j m * degC (rootPointIdeal ζ)

def lineExampleCoord : (Σ _ : Unit, Fin 2) → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun p => if p.2 = 0 then 1 else algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)

def lineExampleT : Fin 1 → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun _ => algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLocallyPrincipalCoprime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace LocallyPrincipalCoprimeAlt

variable {L : Type} [Field L]

theorem finite_maximal_of_ne_zero [CharZero L] (B : Subring L) [Module.Finite ℤ B] {s : B} (hs : s ≠ 0) :
    Set.Finite {m : Ideal B | m.IsMaximal ∧ s ∈ m} := by
  have : Module.Free ℤ B := Module.free_of_finite_type_torsion_free'
  have hI : Ideal.span {s} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hs
  have : Finite (B ⧸ Ideal.span {s}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  refine Set.Finite.of_finite_image (f := fun m : Ideal B => Ideal.Quotient.mk (Ideal.span {s}) '' (m : Set B))
    (Set.toFinite _) ?_
  have key : ∀ m m' : Ideal B, s ∈ m' →
      Ideal.Quotient.mk (Ideal.span {s}) '' (m : Set B) = Ideal.Quotient.mk (Ideal.span {s}) '' (m' : Set B) →
      m ≤ m' := by
    intro m m' hs' h x hx
    obtain ⟨y, hy, hxy⟩ : Ideal.Quotient.mk (Ideal.span {s}) x ∈
        Ideal.Quotient.mk (Ideal.span {s}) '' (m' : Set B) := h ▸ ⟨x, hx, rfl⟩
    have hd : x - y ∈ Ideal.span {s} := Ideal.Quotient.eq.mp hxy.symm
    have hle : Ideal.span {s} ≤ m' := (Ideal.span_singleton_le_iff_mem _).mpr hs'
    have := m'.add_mem (hle hd) hy
    simpa using this
  intro m hm m' hm' h
  exact le_antisymm (key m m' hm'.2 h) (key m' m hm.2 h.symm)

theorem mem_span_of_local {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span B (Set.range a) := by
  set S := Submodule.span B (Set.range a)
  by_contra hzS
  have hJ : S.colon {z} ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ S.colon {z} := h ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hzS h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
  obtain ⟨i, hi⟩ := hloc m hm
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  apply hbm
  apply hJm
  have e : b • z = c • a i := by rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, hbc]
  rw [Submodule.mem_colon_singleton, e]
  exact S.smul_mem c (Submodule.subset_span ⟨i, rfl⟩)

theorem ne_zero_of_local {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L} {m : Ideal B} {i : ι}
    (hi : ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) (hM : M ≠ ⊥) : a i ≠ 0 := by
  obtain ⟨z, hzM, hz0⟩ : ∃ z ∈ M, z ≠ 0 := by
    by_contra h
    push Not at h
    exact hM ((AddSubgroup.eq_bot_iff_forall M).mpr h)
  obtain ⟨b, c, hbm, hbc⟩ := hi z hzM
  intro ha
  have hb : (b : L) ≠ 0 := fun h => hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)
  rw [ha, mul_zero] at hbc
  exact mul_ne_zero hb hz0 hbc

theorem exists_local_mult {B : Subring L} {M : AddSubgroup L} {ι : Type} [Fintype ι] {a : ι → L}
    (haM : ∀ i, a i ∈ M)
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    (hM : M ≠ ⊥) (m : Ideal B) (hm : m.IsMaximal) :
    ∃ (g : L) (i : ι), (∀ z ∈ M, g * z ∈ B) ∧ ∃ y : B, (y : L) = g * a i ∧ y ∉ m := by
  obtain ⟨i, hi⟩ := hloc m hm
  have hai := ne_zero_of_local hi hM
  set P := Submodule.span B {a i}
  have hK : ¬ (Finset.univ.inf fun j => P.colon {a j}) ≤ m := by
    rw [hm.isPrime.inf_le']
    rintro ⟨j, -, hj⟩
    obtain ⟨b, c, hbm, hbc⟩ := hi (a j) (haM j)
    apply hbm
    apply hj
    have e : b • a j = c • a i := by rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, hbc]
    rw [Submodule.mem_colon_singleton, e]
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
  obtain ⟨t, htK, htm⟩ := IsConcreteLE.not_le_iff_exists.mp hK
  refine ⟨t / a i, i, ?_, t, by field_simp, htm⟩
  intro z hz
  have hzN := mem_span_of_local hloc hz
  have hle : Submodule.span B (Set.range a) ≤ P.comap (t • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := Submodule.mem_colon_singleton.mp
      ((Finset.inf_le (f := fun j => P.colon {a j}) (Finset.mem_univ j)) htK)
    simpa using this
  have htz : t • z ∈ P := by simpa using hle hzN
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp htz
  rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul] at hc
  have : t / a i * z = c := by
    field_simp
    linear_combination -hc
  rw [this]
  exact c.2


open scoped Classical in
open Classical in
noncomputable def toB (B : Subring L) (x : L) : B := if h : x ∈ B then ⟨x, h⟩ else 0

theorem coe_toB {B : Subring L} {x : L} (h : x ∈ B) : (toB B x : L) = x := by
  simp [toB, h]

end LocallyPrincipalCoprimeAlt


open LocallyPrincipalCoprimeAlt in
theorem LocallyPrincipalCoprime.proof : LocallyPrincipalCoprime.Statement := by
  classical
  intro L _ _ B M ι _ a hfin hBM haM hden hloc hM s hs
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal B
  have : Nonempty ι := ⟨(hloc m₀ hm₀).choose⟩
  choose! g idx hgM y hy hym using exists_local_mult haM hloc hM
  have hS := finite_maximal_of_ne_zero B hs
  set S := hS.toFinset with hSdef
  have memS : ∀ m, m ∈ S ↔ m.IsMaximal ∧ s ∈ m := fun m => hS.mem_toFinset

  have havoid : ∀ m ∈ S, ∃ e : B, (∀ m' ∈ S.erase m, e ∈ m') ∧ e ∉ m := by
    intro m hmS
    have hmS' := (memS m).mp hmS
    have hnle : ¬ (S.erase m).inf id ≤ m := by
      rw [hmS'.1.isPrime.inf_le']
      rintro ⟨m', hm'S, hm'm⟩
      have h' := (memS m').mp (Finset.mem_of_mem_erase hm'S)
      exact Finset.ne_of_mem_erase hm'S (h'.1.eq_of_le hmS'.1.ne_top hm'm)
    obtain ⟨e, he, hem⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    exact ⟨e, fun m' hm' => Finset.inf_le (f := id) hm' he, hem⟩
  choose! e he hem using havoid
  set γ : L := (s : L) * g m₀ + ∑ m ∈ S, (e m : L) * g m with hγdef
  have hγM : ∀ z ∈ M, γ * z ∈ B := by
    intro z hz
    rw [hγdef, add_mul, Finset.sum_mul]
    refine B.add_mem ?_ (B.sum_mem fun m hm => ?_)
    · rw [mul_assoc]
      exact B.mul_mem s.2 (hgM m₀ hm₀ z hz)
    · rw [mul_assoc]
      exact B.mul_mem (e m).2 (hgM m ((memS m).mp hm).1 z hz)
  have hγm : ∀ m ∈ S, ∀ h : γ * a (idx m) ∈ B, (⟨_, h⟩ : B) ∉ m := by
    intro m hmS h hin
    have hmS' := (memS m).mp hmS
    have hw : (⟨_, h⟩ : B) = s * toB B (g m₀ * a (idx m)) +
        (e m * toB B (g m * a (idx m)) +
          ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m))) := by
      rw [Finset.add_sum_erase S (fun m' => e m' * toB B (g m' * a (idx m))) hmS]
      apply Subtype.ext
      push_cast
      rw [coe_toB (hgM m₀ hm₀ _ (haM _)), hγdef, add_mul, Finset.sum_mul]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [coe_toB (hgM m' ((memS m').mp hm').1 _ (haM _))]
        ring
    have hym' : toB B (g m * a (idx m)) = y m := by
      apply Subtype.ext
      rw [coe_toB (hgM m hmS'.1 _ (haM _)), hy m hmS'.1]
    have h1 : s * toB B (g m₀ * a (idx m)) ∈ m := m.mul_mem_right _ hmS'.2
    have h2 : ∑ m' ∈ S.erase m, e m' * toB B (g m' * a (idx m)) ∈ m := by
      refine m.sum_mem fun m' hm' => m.mul_mem_right _ (he m' (Finset.mem_of_mem_erase hm') m ?_)
      exact Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hm').symm, hmS⟩
    rw [hw] at hin
    have h3 : e m * toB B (g m * a (idx m)) ∈ m :=
      (m.add_mem_iff_left h2).mp ((m.add_mem_iff_right h1).mp hin)
    rw [hym'] at h3
    rcases hmS'.1.isPrime.mem_or_mem h3 with h4 | h4
    · exact hem m hmS h4
    · exact hym m hmS'.1 h4
  have hy0 : (y m₀ : L) ≠ 0 := fun h0 => hym m₀ hm₀ (by rw [show y m₀ = 0 from Subtype.ext h0]; exact m₀.zero_mem)
  have ha0 : a (idx m₀) ≠ 0 := by
    intro h0; apply hy0; rw [hy m₀ hm₀, h0, mul_zero]
  have hg0 : g m₀ ≠ 0 := by
    intro h0; apply hy0; rw [hy m₀ hm₀, h0, zero_mul]
  have hγ : γ ≠ 0 := by
    intro h0
    rcases S.eq_empty_or_nonempty with hE | ⟨m, hmS⟩
    · rw [hγdef, hE, Finset.sum_empty, add_zero] at h0
      have hs' : (s : L) ≠ 0 := fun h => hs (Subtype.ext h)
      exact mul_ne_zero hs' hg0 h0
    · have h : γ * a (idx m) ∈ B := by rw [h0, zero_mul]; exact B.zero_mem
      apply hγm m hmS h
      have : (⟨_, h⟩ : B) = 0 := Subtype.ext (by simp [h0])
      rw [this]; exact m.zero_mem
  obtain ⟨c₀, hc₀B, hc₀, hc₀a⟩ := hden (idx m₀)
  set a₀ := a (idx m₀)
  let I : Ideal B :=
    { carrier := {w | (w : L) * γ⁻¹ ∈ M}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at hu hv ⊢
        exact M.add_mem hu hv
      zero_mem' := by simp [M.zero_mem]
      smul_mem' := fun c u hu => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at hu ⊢
        exact hBM c c.2 _ hu }
  have memI : ∀ w : B, w ∈ I ↔ (w : L) * γ⁻¹ ∈ M := fun w => Iff.rfl
  refine ⟨⟨γ * a₀ * c₀, B.mul_mem (hγM _ (haM _)) hc₀B⟩, ⟨c₀ * a₀, hc₀a⟩, I, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : γ * a₀ * c₀ = 0 := congrArg Subtype.val h
    exact mul_ne_zero (mul_ne_zero hγ ha0) hc₀ h'
  · intro h
    have h' : c₀ * a₀ = 0 := congrArg Subtype.val h
    exact mul_ne_zero hc₀ ha0 h'
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have hsm : s ∈ m := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    have hmS : m ∈ S := (memS m).mpr ⟨hm, hsm⟩
    have hmem : (⟨_, hγM _ (haM (idx m))⟩ : B) ∈ I := by
      rw [memI]
      have : γ * a (idx m) * γ⁻¹ = a (idx m) := by field_simp
      rw [this]; exact haM _
    exact hγm m hmS _ (hle (Ideal.mem_sup_left hmem))
  · intro x
    constructor
    · intro hx
      refine ⟨⟨γ * x, hγM x hx⟩, ?_, ?_⟩
      · rw [memI]
        have : γ * x * γ⁻¹ = x := by field_simp
        rw [this]; exact hx
      · show γ * a₀ * c₀ * x = c₀ * a₀ * (γ * x)
        ring
    · rintro ⟨w, hwI, hxw⟩
      have hxw' : γ * a₀ * c₀ * x = c₀ * a₀ * w := hxw
      have h1 : (c₀ * a₀) * (γ * x) = (c₀ * a₀) * w := by linear_combination hxw'
      have h2 := mul_left_cancel₀ (mul_ne_zero hc₀ ha0) h1
      have hx : x = (w : L) * γ⁻¹ := by rw [← h2]; field_simp
      rw [hx]
      exact (memI w).mp hwI

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyLinearInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M N C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → C.det ≠ 0 → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

def ChartDiffEnergy.Statement : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → (∀ i, (T i).PosDef) →
    Integrable (ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i))
      (fun y => hermChartPot A y - hermChartPot B y) (fun y => hermChartPot A y - hermChartPot B y))

def ChartIbpCutoff.Statement : Prop :=
  ∀ (n : ℕ) (A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ i, (T i).PosDef) →
    Tendsto (fun k : ℕ => ∫ y : Fin (n + 1) → ℂ, chartCutoff k y *
        ((hermChartPot A y - hermChartPot B y) *
            maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
              fun i => hermChartPot (T i)) y -
          (hermChartPot C y - hermChartPot D y) *
            maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
              fun i => hermChartPot (T i)) y))
      atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ThetaGauss
set_option maxSynthPendingDepth 1

open Matrix MeasureTheory Real
open scoped MatrixOrder

namespace GroundTheory.Heights₂.Heights
namespace KTheta

noncomputable section

variable {g : ℕ}

theorem qf_star_mul_self (B : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    qf (star B * B) v = ∑ i, (B *ᵥ v) i ^ 2 := by
  unfold qf
  rw [← Matrix.mulVec_mulVec, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    Matrix.dotProduct_mulVec, vecMul_transpose]
  simp [dotProduct, sq]

theorem integral_exp_sum_sq (c : ℝ) :
    ∫ x : Fin g → ℝ, exp (-c * ∑ i, x i ^ 2) = (√(π / c)) ^ g := by
  have h : (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) = fun x => ∏ i, exp (-c * x i ^ 2) := by
    funext x; rw [Finset.mul_sum, Real.exp_sum]
  rw [h, integral_fintype_prod_volume_eq_prod (f := fun _ (t : ℝ) => exp (-c * t ^ 2))]
  simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem integral_comp_mulVec (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (f : (Fin g → ℝ) → ℝ) (hf : Continuous f) :
    ∫ v, f (B *ᵥ v) = |B.det|⁻¹ * ∫ x, f x := by
  have hdet : LinearMap.det (Matrix.toLin' B) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin g → ℝ))) hdet
  have hm : Measurable (Matrix.toLin' B) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toLin' B)).measurable
  have h1 : ∫ v, f (B *ᵥ v) = ∫ x, f x ∂(Measure.map (Matrix.toLin' B) volume) := by
    rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
    rfl
  rw [h1, hmap, integral_smul_measure, LinearMap.det_toLin']
  rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul]

theorem integral_exp_qf (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) :
    ∫ v, exp (-c * qf Y v) = (√(π / c)) ^ g * (√Y.det)⁻¹ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hdetY : Y.det = B.det ^ 2 := by
    rw [hB, det_mul, star_eq_conjTranspose, det_conjTranspose]; simp [sq]
  have hBdet : B.det ≠ 0 := by
    intro h; have := hY.det_pos; rw [hdetY, h] at this; simp at this
  calc ∫ v, exp (-c * qf Y v) = ∫ v, (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) (B *ᵥ v) := by
        congr 1; funext v; rw [hB, qf_star_mul_self]
    _ = |B.det|⁻¹ * ∫ x : Fin g → ℝ, exp (-c * ∑ i, x i ^ 2) :=
        integral_comp_mulVec B hBdet (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) (by fun_prop)
    _ = (√(π / c)) ^ g * (√Y.det)⁻¹ := by
        rw [integral_exp_sum_sq c, hdetY, Real.sqrt_sq_eq_abs]; ring

theorem integral_exp_two_pi_qf (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    ∫ v, exp (-(2 * π) * qf Y v) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) := by
  rw [integral_exp_qf Y hY (2 * π)]
  have hd := hY.det_pos
  have h2 : π / (2 * π) = (2 : ℝ)⁻¹ := by field_simp
  rw [h2, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
    Real.sqrt_inv, mul_inv, inv_pow]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]

theorem summable_exp_qf (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) (c : ℝ) (hc : 0 < c)
    (v : Fin g → ℝ) : Summable fun k : Fin g → ℤ => exp (-c * qf Y (intVec k + v)) := by
  set τ : Matrix (Fin g) (Fin g) ℂ := Complex.I • Y.map (fun y => (((c / π) * y : ℝ) : ℂ)) with hτ
  have him : τ.map Complex.im = (c / π) • Y := by
    ext i j; simp [hτ]
  have hYt : Yᵀ = Y := by
    have := hY.isHermitian; rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this; exact this
  have hdom : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin g) := by
    show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
    rw [him, transpose_smul, hYt, ← two_smul ℝ, smul_smul]
    exact hY.smul (by positivity)
  have hs := ReciprocityTheory.PTheta.thetaSummable_holds (Fin g) v 0 0 τ hdom
  refine hs.congr fun k => ?_
  unfold ReciprocityTheory.PTheta.thetaTerm
  rw [ReciprocityTheory.PTheta.sphereQuadraticPositivity.norm_eC, ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_arg, him]
  have hw : (fun i => (k i : ℝ) + v i) = intVec k + v := by funext i; simp [intVec]
  rw [hw]
  congr 1
  simp only [qf, smul_mulVec, dotProduct_smul, Pi.zero_apply, Complex.zero_im, smul_eq_mul]
  simp [dotProduct]
  field_simp

theorem intVec_mem_span (k : Fin g → ℤ) :
    intVec k ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g))) := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro i
  exact ⟨k i, by simp [intVec]⟩

theorem exists_int_of_mem_span {x : Fin g → ℝ}
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))) (i : Fin g) :
    ∃ n : ℤ, x i = n := by
  rw [Module.Basis.mem_span_iff_repr_mem] at hx
  obtain ⟨n, hn⟩ := hx i
  exact ⟨n, by simpa using hn.symm⟩

def latticeEquiv :
    (Fin g → ℤ) ≃ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup where
  toFun k := ⟨intVec k, intVec_mem_span k⟩
  invFun γ := fun i => ⌊(γ : Fin g → ℝ) i⌋
  left_inv k := by funext i; simp [intVec]
  right_inv γ := by
    apply Subtype.ext; funext i
    obtain ⟨n, hn⟩ := exists_int_of_mem_span γ.2 i
    simp [intVec, hn]

theorem integral_cube_tsum (F : (Fin g → ℝ) → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hFc : Continuous F)
    (hs : ∀ u, Summable fun k : Fin g → ℤ => F (intVec k + u)) :
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ∑' k : Fin g → ℤ, F (intVec k + u) = ∫ x, F x := by
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup :=
    (latticeEquiv (g := g)).symm.injective.countable
  have hD := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin g)) (volume : Measure (Fin g → ℝ))
  have hDI : ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin g)) =ᵐ[volume]
      Set.Icc (0 : Fin g → ℝ) 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, ← Set.pi_univ_Icc]
    exact Measure.ae_eq_set_pi (fun i _ => Ico_ae_eq_Icc)
  have hP : ∀ u, ∑' k, F (intVec k + u) = (∑' k, ENNReal.ofReal (F (intVec k + u))).toReal := by
    intro u
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 _) (hs u),
      ENNReal.toReal_ofReal (tsum_nonneg fun k => hF0 _)]
  have hPm : Measurable fun u => ∑' k : Fin g → ℤ, F (intVec k + u) := by
    simp_rw [hP]
    exact (Measurable.tsum fun k => ENNReal.measurable_ofReal.comp
      (hFc.measurable.comp (measurable_const_add _))).ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => tsum_nonneg fun k => hF0 _)
      hPm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFc.aestronglyMeasurable]
  congr 1
  rw [hD.lintegral_eq_tsum'' (fun x => ENNReal.ofReal (F x)), ← setLIntegral_congr hDI,
    ← lintegral_tsum (μ := volume.restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin g))))
      (f := fun (γ : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup)
        (x : Fin g → ℝ) => ENNReal.ofReal (F (γ +ᵥ x)))
      (fun γ => (ENNReal.measurable_ofReal.comp
        (hFc.measurable.comp (measurable_const_vadd γ))).aemeasurable)]
  refine setLIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) (fun u _ => ?_)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 _) (hs u)]
  rw [← (latticeEquiv (g := g)).tsum_eq]
  rfl

end

end KTheta

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyCocycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyCocycle.Statement : Prop :=
  ∀ (e : ℕ) (M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → P.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M P k =
      ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k + ∑ k ∈ Finset.range (e + 1), chartMixedEnergy N P k

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → ∀ k : ℕ,
    Integrable (fun y : Fin e → ℂ => (hermChartPot M y - hermChartPot N y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyDiagonal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyDiagonal.Statement : Prop :=
  ∀ (e : ℕ) (l : Fin (e + 1) → ℝ), (∀ j, 0 < l j) →
    ∑ k ∈ Finset.range (e + 1),
        chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) k =
      1 / 2 * (∑ j, Real.log (l j)) * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergySwap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def swapFirstTwo (e : ℕ) : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
  (Equiv.swap (0 : Fin (e + 1 + 1)) 1).permMatrix ℂ

def ChartEnergySwapInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ), M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) ((swapFirstTwo e)ᴴ * N * swapFirstTwo e) k =
      chartMixedEnergy M N k

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergySymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergySymm.Statement : Prop :=
  ∀ (e : ℕ) (A B C D : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (p : Fin e), A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ j, (T j).PosDef) →
    ∫ y : Fin e → ℂ, (hermChartPot A y - hermChartPot B y) *
        (maDensity (fun j => hermChartPot (Function.update T p C j)) y -
          maDensity (fun j => hermChartPot (Function.update T p D j)) y) =
      ∫ y : Fin e → ℂ, (hermChartPot C y - hermChartPot D y) *
        (maDensity (fun j => hermChartPot (Function.update T p A j)) y -
          maDensity (fun j => hermChartPot (Function.update T p B j)) y)

end

end GroundTheory.Heights₂.Heights
end
