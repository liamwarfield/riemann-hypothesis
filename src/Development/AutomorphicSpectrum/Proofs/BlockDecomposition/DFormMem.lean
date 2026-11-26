module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.CocProd

theorem tele {B : Type*} [CommRing B] (P : ℕ → B) (m : ℕ) :
    P 0 + ∑ i ∈ Finset.range m, (-1 : B) ^ (i + 1) * (P (i + 1) + P i) = (-1) ^ m * P m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    ring

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T)

theorem a_comp (i : Fin d) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    E.a σ i (φ ≫ ψ) = (Φ.A.map ψ).hom (E.a σ i φ) + E.a σ i ψ := by
  unfold Frame.a
  rw [E.add i (σ T ≫ φ ≫ ψ) (σ T' ≫ ψ) (σ T''), ← Category.assoc, E.nat]

def ga (i : Fin d) {n : ℕ} (s : ComposableArrows C n) (p q : Fin (n + 1)) (h : p ≤ q) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last q)))).hom (E.a σ i (s.map (homOfLE h)))

theorem ga_add (i : Fin d) {n : ℕ} (s : ComposableArrows C n) (p q r : Fin (n + 1)) (h : p ≤ q) (h' : q ≤ r) :
    ga E σ i s p r (h.trans h') = ga E σ i s p q h + ga E σ i s q r h' := by
  unfold ga
  have e : s.map (homOfLE (h.trans h')) = s.map (homOfLE h) ≫ s.map (homOfLE h') := by
    rw [← s.map_comp]; rfl
  have e2 : s.map (homOfLE (Fin.le_last q)) = s.map (homOfLE h') ≫ s.map (homOfLE (Fin.le_last r)) := by
    rw [← s.map_comp]; rfl
  rw [e, a_comp, map_add (f := _), e2, Functor.map_comp]
  rfl

theorem ga_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (i : Fin d) {n : ℕ} (s : ComposableArrows C n)
    (p q : Fin (n + 1)) (h : p ≤ q) : ga E σ i s p q h ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
  have : E.a σ i (s.map (homOfLE h)) ∈ (Fil 1).S _ := by
    rw [hF.one]; exact E.mem i _ _
  exact (Fil _).map_mem _ (by simpa using this)

theorem prod_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {T : C} {j : ℕ} (f : Fin j → Φ.A.obj T)
    (hf : ∀ k, f k ∈ (Fil ((1 : ℕ) : ℤ)).S T) {q : ℕ} {x : Φ.A.obj T} (hx : x ∈ (Fil (q : ℤ)).S T) :
    (∏ k, f k) * x ∈ (Fil ((j + q : ℕ) : ℤ)).S T := by
  induction j with
  | zero =>
    simpa using hx
  | succ j ih =>
    rw [Fin.prod_univ_succ, mul_assoc]
    have := hF.mul 1 (j + q) T (hf 0) (ih (fun k => f k.succ) (fun k => hf k.succ))
    have e : 1 + (j + q) = j + 1 + q := by omega
    rwa [e] at this

theorem map_map {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (y : Φ.A.obj X) :
    (Φ.A.map f).hom ((Φ.A.map g).hom y) = (Φ.A.map (g ≫ f)).hom y := by
  simp

theorem face_form {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (∏ k : Fin j, ga E σ (I k) s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_lt_succ (i := k)).le)) *
      (Φ.A.map (toLast i s)).hom ((Φ.A.map (σ _)).hom x) := by
  unfold Frame.form
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold ga
  rw [map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e]
  rfl

theorem sa_val {n : ℕ} (i : Fin (n + 1)) (m : Fin n) :
    ((i.succAbove m : Fin (n + 1)) : ℕ) = if (m : ℕ) < i then (m : ℕ) else m + 1 := by
  unfold Fin.succAbove
  split_ifs <;> simp_all [Fin.lt_def]

theorem ga_congr (i : Fin d) {n : ℕ} (s : ComposableArrows C n) {p q p' q' : Fin (n + 1)} (h : p ≤ q) (h' : p' ≤ q')
    (hp : (p : ℕ) = p') (hq : (q : ℕ) = q') : ga E σ i s p q h = ga E σ i s p' q' h' := by
  obtain rfl := Fin.ext hp
  obtain rfl := Fin.ext hq
  rfl

theorem sec_last {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) (hp : p = Fin.last n) :
    σ (s.obj p) ≫ s.map (homOfLE (Fin.le_last p)) = σ (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, s.map_id, Category.comp_id]

theorem d_form_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (j q : ℕ)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) ∈
      (Fil (((j : ℤ) + q) + 1)).S _ := by
  classical
  set u : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp) with hu
  set v : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.succ.castSucc k.succ.succ (by rw [Fin.le_def]; simp) with hv
  set P : ℕ → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, ga E σ (I k) s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_lt_succ (i := k)).le) with hT
  set W : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    (Φ.A.map (toLast i s)).hom ((Φ.A.map (σ _)).hom x) with hW
  set Y := (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x with hY
  have hT0 : T 0 = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => ga E σ (I k) s (i.succ.castSucc.succAbove k.castSucc)
        (i.succ.castSucc.succAbove k.succ) ((Fin.strictMono_succAbove _).monotone (Fin.castSucc_lt_succ (i := k)).le)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · rw [hu, hv]
        dsimp only
        rw [← ga_add]
        refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp only [sa_val, Fin.val_castSucc, Fin.val_succ] <;> split_ifs <;> omega
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp only [sa_val, Fin.val_castSucc, Fin.val_succ] <;> split_ifs <;> omega
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp only [sa_val, Fin.val_castSucc, Fin.val_succ] <;> split_ifs <;> omega
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  have hWY : ∀ i : Fin (j + 2), i ≠ Fin.last (j + 1) → W i = Y := by
    intro i hi
    have hi' : i.succAbove (Fin.last j) = Fin.last (j + 1) := by
      have h1 : (i : ℕ) ≠ j + 1 := fun h => hi (Fin.ext h)
      have h2 := i.2
      apply Fin.ext
      rw [sa_val]
      simp only [Fin.val_last]
      split_ifs <;> omega
    calc W i = (Φ.A.map (σ _ ≫ toLast i s)).hom x := map_map _ _ _
      _ = Y := by rw [show σ _ ≫ toLast i s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hi']
  have hYW : Y - W (Fin.last (j + 1)) ∈ (Fil ((q : ℤ) + 1)).S _ := by
    have h := hc q (σ (s.obj (Fin.last (j + 1)))) (σ _ ≫ toLast (Fin.last (j + 1)) s) hx
    rwa [show W (Fin.last (j + 1)) = (Φ.A.map (σ _ ≫ toLast (Fin.last (j + 1)) s)).hom x from map_map _ _ _]
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (-1) ^ j * (P j * (Y - W (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
        (-1) ^ (i : ℕ) * (T i * W i) := by
      intro i
      rw [face_form, zsmul_eq_mul]
      push_cast
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    have h0 : T (Fin.castSucc 0) = P 0 := hT0
    have hne0 : Fin.castSucc (0 : Fin (j + 1)) ≠ Fin.last (j + 1) := (Fin.castSucc_lt_last _).ne
    have hint : ∑ i : Fin j, (-1) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * (T i.succ.castSucc * W i.succ.castSucc) =
        (∑ m ∈ Finset.range j, (-1) ^ (m + 1) * (P (m + 1) + P m)) * Y := by
      rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun m => (-1) ^ (m + 1) * (P (m + 1) + P m) * Y) j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hTi, hWY _ (Fin.castSucc_lt_last _).ne]
      simp only [Fin.val_castSucc, Fin.val_succ]
      ring
    rw [hint, h0, hWY _ hne0, hTl]
    simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
    linear_combination Y * tele P j
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have h := prod_mem hF (fun k : Fin j => if (k : ℕ) < j then u k else v k)
    (fun k => by
      split_ifs
      · exact ga_mem E σ hF _ s _ _ _
      · exact ga_mem E σ hF _ s _ _ _)
    (q := q + 1) (x := Y - W (Fin.last (j + 1))) (by push_cast; exact hYW)
  have e : ((j + (q + 1) : ℕ) : ℤ) = (j : ℤ) + q + 1 := by push_cast; ring
  rwa [e] at h

theorem rep_form {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) :
    ∃ c, Rep (Fil r) (Fil (r + 1)) (E.form σ I x) c := by
  subst hr
  have hmem : ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j : ℤ) + q)).S _ := by
    intro s
    have h := prod_mem hF _ (fun k => ga_mem E σ hF (I k) s k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).le)
      ((Fil q).map_mem (σ _) hx)
    rw [Nat.cast_add] at h
    exact h
  let f : CH.Cn (sq (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1))) j := fun s => sqMk _ _ (E.form σ I x s) (hmem s)
  have hd : CH.d _ j f = 0 := by
    funext s
    apply Subtype.ext
    have h := Ideal.Quotient.eq_zero_iff_mem.2 (d_form_mem E σ hF hc j q I x hx s)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    refine Eq.trans ?_ h
    change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1))).map (toLast i s)).hom (f (face i s)) :
      sqM (Fil ((j : ℤ) + q)) (Fil ((j : ℤ) + q + 1)) _) = _
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  exact ⟨_, f, hd, rfl, fun s => rfl⟩

end GlobalTheory.CompanionTheory.CocProd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

def colGe (d j : ℕ) (i l : Fin d) : Prop := i < l ∧ j ≤ (l : ℕ)

variable (K : Type) [Field K]

def colGeE (d j : ℕ) (i l : Fin d) : K := if (l : ℕ) = i + 1 ∧ j ≤ (l : ℕ) then 1 else 0

def colGeR (d j : ℕ) (r : Fin j → K) (i l : Fin d) : K :=
  colGeE K d (j + 1) i l + if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0

def blkEmb (d j : ℕ) (A : Matrix (Fin j) (Fin j) K) : Matrix (Fin d) (Fin d) K := fun i l =>
  if h : (i : ℕ) < j ∧ (l : ℕ) < j then A ⟨i, h.1⟩ ⟨l, h.2⟩ else if i = l then 1 else 0

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Mass.MeanV

variable {F : Type} [Field F] [NumberField F]

def IntOut (T : Finset (HeightOneSpectrum (𝓞 F))) : Set F :=
  {x | ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F}

def GoodFac (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ) : Prop :=
  ContinuousOn g {0}ᶜ ∧ (∀ s, s ∉ v.adicCompletionIntegers F → g s = 0) ∧
    (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧
    (∀ s : Fv F v, Valued.v s = 1 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ∧ ∫ s, g s ∂lam = 1

def truncSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0}, (IntOut T).indicator
    (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1

def fullSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0},
    G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProper
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProper
open MeasureTheory Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreUniq

theorem fibreFamily_eq_inter (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (W : Set V) (hW : IsOpen W)
    (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B' ∩ W) := (hB'.preimage hg).inter hW
  have hOU : g ⁻¹' B' ∩ W ⊆ g ⁻¹' B ∩ W := Set.inter_subset_inter_left _ (Set.preimage_mono hBB)
  have hbB : b ∈ B := hBB hb
  refine measure_eq_of_lintegral_eq (fib' b) (fib b) (g ⁻¹' B' ∩ W) hO ?_ ?_ ?_
  · refine measure_mono_null ?_ (h'.1 b)
    intro v hv hv'
    exact hv hv'.2
  · refine measure_mono_null ?_ (h.1 b)
    intro v hv hv'
    have hgv : g v = b := hι (by rw [← hf v]; exact hv'.1)
    exact hv ⟨show g v ∈ B' from hgv ▸ hb, hv'.2.2⟩
  · intro φ hφc hφs hφO hφnn
    have hφU : tsupport φ ⊆ g ⁻¹' B ∩ W := hφO.trans hOU
    obtain ⟨hint', hcont'⟩ := h'.2.2 φ hφc hφs hφO
    obtain ⟨hint, hcont⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨hint' b hb, ?_⟩
    have hψm : Measurable (fun v => ENNReal.ofReal (φ v)) := hφc.measurable.ennreal_ofReal
    have hψ0 : ∀ v, v ∉ g ⁻¹' B' ∩ W → ENNReal.ofReal (φ v) = 0 := by
      intro v hv
      have hz : φ v = 0 := by
        by_contra hne
        exact hv (hφO (subset_tsupport φ (Function.mem_support.mpr hne)))
      simp [hz]
    have hF : ∀ c ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = ENNReal.ofReal (∫ v, φ v ∂(fib c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint c hc) (ae_of_all _ hφnn)).symm
    have hF' : ∀ c ∈ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) =
        ENNReal.ofReal (∫ v, φ v ∂(fib' c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint' c hc) (ae_of_all _ hφnn)).symm
    have hset : ∀ S, MeasurableSet S →
        ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν =
          ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := by
      intro S hS
      have hS' : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
      have e1 := lintegral_preimage hι hg hf hO hOU h (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'
      have e2 := lintegral_preimage hι hg hf hO Set.Subset.rfl h' (fun v => ENNReal.ofReal (φ v))
        hψm hψ0 _ hS'
      exact e1.symm.trans e2
    have key : ∀ (k k' : X → ℝ≥0∞) (T : Set X), MeasurableSet T → (∀ c ∈ T, k c = k' c) →
        ∫⁻ c in T, k c ∂ν = ∫⁻ c in T, k' c ∂ν := fun k k' T hT hkk =>
      lintegral_congr_ae ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall hkk))
    have hae : (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib c))) =ᵐ[ν.restrict B']
        (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib' c))) := by
      refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ ?_ ?_ ?_
      · exact ((hcont.mono hBB).aemeasurable hB'.measurableSet).ennreal_ofReal
      · exact (hcont'.aemeasurable hB'.measurableSet).ennreal_ofReal
      · intro S hS _
        rw [Measure.restrict_restrict hS]
        have hT : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
        calc ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib c)) ∂ν
            = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν :=
              key _ _ _ hT (fun c hc => (hF c (hBB hc.2)).symm)
          _ = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := hset S hS
          _ = ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib' c)) ∂ν :=
              key _ _ _ hT (fun c hc => hF' c hc.2)
    have heq := Measure.eqOn_open_of_ae_eq hae hB'
      (ENNReal.continuous_ofReal.comp_continuousOn (hcont.mono hBB))
      (ENNReal.continuous_ofReal.comp_continuousOn hcont') hb
    rw [hF' b hb, hF b hbB]
    exact heq.symm

end GlobalTheory.CompanionTheory.SW.FibreUniq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_embedding_of_injective_proper : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (W : Set V), IsOpen W → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib' → ∀ b ∈ B', fib' b = fib b := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | exact GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | (intros; apply GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
open CategoryTheory ReciprocityTheory.Ty.Fin PI.GreenHCLabel

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

theorem nonempty_iso_iff_intertwiner {Γ : Type} [Group Γ] (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v) := by
  constructor
  · rintro ⟨i⟩
    refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
    rw [FDRep.Iso.conj_ρ i γ, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨e, he⟩
    have h1 : ∀ g, e.toLinearMap ∘ₗ τ.ρ g = σ.ρ g ∘ₗ e.toLinearMap :=
      fun g => LinearMap.ext fun v => he g v
    have h2 : ∀ g, e.symm.toLinearMap ∘ₗ σ.ρ g = τ.ρ g ∘ₗ e.symm.toLinearMap := by
      intro g
      refine LinearMap.ext fun v => ?_
      show e.symm (σ.ρ g v) = τ.ρ g (e.symm v)
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    refine ⟨{ hom := basicsMk e.toLinearMap h1
              inv := basicsMk e.symm.toLinearMap h2
              hom_inv_id := ?_
              inv_hom_id := ?_ }⟩
    · ext v
      simp [basicsMk]
    · ext v
      simp [basicsMk]

private theorem simple_iff_isIrr {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) :
    CategoryTheory.Simple τ ↔ ReciprocityTheory.Ty.Fin.IsIrr τ.ρ := by
  constructor
  · intro hs
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      apply Simple.not_isZero τ
      rw [Limits.IsZero.iff_id_eq_zero]
      apply basics_hom_ext
      rw [basics_lin_id, basics_lin_zero]
      refine LinearMap.ext fun v => ?_
      exact @Subsingleton.elim _ hnt _ _
    · haveI hmono : Mono (basicsIncl τ W hW) :=
        basics_mono_of_inj _ (fun x y hxy => Subtype.ext hxy)
      rcases eq_or_ne (basicsIncl τ W hW) 0 with h0 | h0
      · left
        rw [Submodule.eq_bot_iff]
        intro w hw
        have h1 : basicsLin (basicsIncl τ W hW) (⟨w, hw⟩ : W) = w := rfl
        have h2 := congrArg (fun f => basicsLin f (⟨w, hw⟩ : W)) h0
        simp only [basics_lin_zero, LinearMap.zero_apply] at h2
        rw [← h1]
        exact h2
      · right
        haveI hiso : IsIso (basicsIncl τ W hW) :=
          (Simple.mono_isIso_iff_nonzero (basicsIncl τ W hW)).mpr h0
        rw [eq_top_iff]
        intro v _
        have h3 : basicsLin (inv (basicsIncl τ W hW) ≫ basicsIncl τ W hW) v = v := by
          rw [IsIso.inv_hom_id, basics_lin_id]
          rfl
        rw [basics_lin_comp] at h3
        rw [← h3]
        exact (basicsLin (inv (basicsIncl τ W hW)) v).2
  · rintro ⟨hnt, hirr⟩
    refine ⟨fun {Y} f hf => ⟨fun hiso h0 => ?_, fun h0 => ?_⟩⟩
    · subst h0
      have h1 : 𝟙 τ = 0 := by
        rw [← IsIso.inv_hom_id (0 : Y ⟶ τ), Limits.comp_zero]
      have h2 : basicsLin (𝟙 τ) = 0 := by
        rw [h1, basics_lin_zero]
      rw [basics_lin_id] at h2
      obtain ⟨⟨x, y, hxy⟩⟩ := hnt
      apply hxy
      have hx := LinearMap.congr_fun h2 x
      have hy := LinearMap.congr_fun h2 y
      simp only [LinearMap.id_apply, LinearMap.zero_apply] at hx hy
      rw [hx, hy]
    · have hinj := basics_inj_of_mono f
      have hinv : ∀ g : Γ, ∀ v ∈ LinearMap.range (basicsLin f),
          τ.ρ g v ∈ LinearMap.range (basicsLin f) := by
        rintro g v ⟨y, rfl⟩
        refine ⟨Y.ρ g y, ?_⟩
        exact LinearMap.congr_fun (basics_lin_comm f g) y
      rcases hirr _ hinv with hbot | htop
      · exfalso
        apply h0
        apply basics_hom_ext
        rw [basics_lin_zero]
        exact LinearMap.range_eq_bot.mp hbot
      · have hsurj : Function.Surjective (basicsLin f) := LinearMap.range_eq_top.mp htop
        let e := LinearEquiv.ofBijective (basicsLin f) ⟨hinj, hsurj⟩
        have hcomm : ∀ g : Γ, e.symm.toLinearMap ∘ₗ τ.ρ g = Y.ρ g ∘ₗ e.symm.toLinearMap := by
          intro g
          refine LinearMap.ext fun v => ?_
          show e.symm (τ.ρ g v) = Y.ρ g (e.symm v)
          apply e.injective
          rw [LinearEquiv.apply_symm_apply]
          show τ.ρ g v = basicsLin f (Y.ρ g (e.symm v))
          rw [← LinearMap.comp_apply (basicsLin f), basics_lin_comm f g, LinearMap.comp_apply]
          congr 1
          exact (e.apply_symm_apply v).symm
        refine ⟨⟨basicsMk e.symm.toLinearMap hcomm, ?_, ?_⟩⟩
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          refine LinearMap.ext fun y => ?_
          exact e.symm_apply_apply y
        · apply basics_hom_ext
          rw [basics_lin_comp, basics_lin_id]
          refine LinearMap.ext fun v => ?_
          exact e.apply_symm_apply v

theorem simpleIffIrr : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  unfold ReciprocityTheory.Ty.Fin.St.SimpleIffIrr
  exact ⟨fun Γ _ _ τ => simple_iff_isIrr τ, fun Γ _ _ τ σ => nonempty_iso_iff_intertwiner τ σ⟩

end GlobalTheory.CompanionTheory.TyFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_iff_irreducible : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | exact GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | (intros; apply GlobalTheory.CompanionTheory.TyFin.simpleIffIrr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

variable {F : Type} [Field F] [NumberField F]

def LocMem (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (z : F) : Prop :=
  ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ y ∈ I, (s : F) * z = (y : F)

def cosetOff {ι : Type} (S : Finset (HeightOneSpectrum (𝓞 F))) (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ v, v ∉ S → ∀ i, LocMem I v (x i - x0 i)}

def latCoset {ι : Type} (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ i, ∃ y ∈ I, (y : F) = x i - x0 i}

def ballV (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Set (Fv F v) :=
  {z | Valued.v z ≤ WithZero.exp (-(k : ℤ))}

def boxInd {ι : Type} (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c y : ι → Fv F v) : ℝ :=
  if ∀ i, y i - c i ∈ ballV v k then 1 else 0

def term {ι : Type} (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) : ℝ :=
  φ (fun i => θ ε * algebraMap F (Ainf F) (x i)) * ∏ v ∈ S, ψ v fun i => algebraMap F (Fv F v) (x i)

end GlobalTheory.CompanionTheory.Equi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HkMemFixed
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeFix

theorem hk_mem_fixed : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K e v ∈ fixed ρ K ∧ ∀ g : GL ι F, (∀ q : GL ι F ⧸ K, e (g * q.out) = e q.out) → True := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ ρ v hv
  refine ⟨?_, fun _ _ => trivial⟩
  have hfix : ∀ c ∈ K, ρ c v = v := by
    intro c hc
    have := hv ⟨c, hc⟩
    simpa using this
  have hbi := hE.2.2.2
  intro h
  have hk' : (h : GL ι F) ∈ K := h.2
  set k : GL ι F := (h : GL ι F) with hkdef
  have hinj : Function.Injective (ρ k : V →ₗ[ℂ] V) := by
    intro x y hxy
    have h1 : ∀ z, ρ k⁻¹ (ρ k z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1 x, ← h1 y, hxy]
  have hstep : ∀ q : GL ι F ⧸ K, ρ k (e q.out • ρ q.out v) =
      e (k • q).out • ρ (k • q).out v := by
    intro q
    have hq : k • q = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (k * q.out)
    rw [hq, hc, hbi k hk' c c.2 q.out, map_smul, map_mul, Module.End.mul_apply, map_mul,
      Module.End.mul_apply, hfix c c.2]
  have hsum : ρ k (hk ρ K e v) = hk ρ K e v := by
    unfold hk
    have h1 := AddMonoidHom.map_finsum_of_injective (ρ k : V →ₗ[ℂ] V).toAddMonoidHom hinj
      (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1]
    simp only [hstep]
    exact finsum_comp_equiv (f := fun q : GL ι F ⧸ K => e q.out • ρ q.out v) (MulAction.toPerm k)
  simpa using hsum

end GlobalTheory.CompanionTheory.HeckeFix
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DetMonotone

private theorem exists_unitary_diagonal_eigenvalues_of_isHermitian {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix κ κ ℂ, U * star U = 1 ∧ star U * U = 1 ∧
      A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
  refine ⟨(hA.eigenvectorUnitary : Matrix κ κ ℂ), Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem detMono : DetMono := by
  open ComplexOrder in (
    have one_le_re_det_lemma_2 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] {Q : Matrix κ κ ℂ},
        Q.PosSemidef → 1 ≤ ((1 + Q).det).re := by
      intro κ _ _ Q hQ
      obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hQ.1
      have hsum : 1 + Q = U * diagonal (fun i => 1 + (hQ.1.eigenvalues i : ℂ)) * star U := by
        conv_lhs => rw [hU]
        rw [← diagonal_add, diagonal_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
      have hdet : (1 + Q).det = ∏ i, (1 + (hQ.1.eigenvalues i : ℂ)) := by
        rw [hsum, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, h2, det_one, one_mul]
      rw [hdet, show (∏ i, (1 + (hQ.1.eigenvalues i : ℂ))) = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) by
        push_cast; rfl, Complex.ofReal_re]
      calc (1 : ℝ) = ∏ _i : κ, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
          Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => le_add_of_nonneg_right (hQ.eigenvalues_nonneg i)
    intro κ _ _ X Y hX hP
    have hY : Y = X + (Y - X) := by abel
    by_cases h0 : X.det = 0
    · rw [h0, Complex.zero_re]
      have hnn := (hX.add hP).det_nonneg
      rw [← hY] at hnn
      exact (Complex.le_def.1 hnn).1
    · obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hX.1
      have hpos : ∀ i, 0 < hX.1.eigenvalues i := by
        intro i
        refine lt_of_le_of_ne (hX.eigenvalues_nonneg i) fun h => h0 ?_
        rw [hX.1.det_eq_prod_eigenvalues]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← h]; simp)
      set s : κ → ℂ := fun i => ((Real.sqrt (hX.1.eigenvalues i) : ℝ) : ℂ) with hs
      have hs0 : ∀ i, s i ≠ 0 := fun i => by
        simp only [hs, ne_eq, Complex.ofReal_eq_zero]
        exact (Real.sqrt_pos.2 (hpos i)).ne'
      have hss : ∀ i, s i * s i = (hX.1.eigenvalues i : ℂ) := fun i => by
        simp only [hs]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
      have hstar : ∀ i, star (s i) = s i := fun i => by simp [hs]
      set B : Matrix κ κ ℂ := diagonal s * star U with hB
      set C : Matrix κ κ ℂ := U * diagonal (fun i => (s i)⁻¹) with hC
      have hCB : C * B = 1 := by
        rw [hB, hC, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal,
          show (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) from funext fun i => inv_mul_cancel₀ (hs0 i),
          diagonal_one, Matrix.one_mul, h1]
      have hXB : X = Bᴴ * B := by
        rw [hB, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose,
          show star s = s from funext hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s),
          diagonal_mul_diagonal, show (fun i => s i * s i) = fun i => (hX.1.eigenvalues i : ℂ) from funext hss,
          ← Matrix.mul_assoc, ← star_eq_conjTranspose]
        exact hU
      have hsplit : Y = Bᴴ * (1 + Cᴴ * (Y - X) * C) * B := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hXB, Matrix.mul_assoc, Matrix.mul_assoc, hCB,
          Matrix.mul_one, ← Matrix.mul_assoc, ← conjTranspose_mul, hCB, conjTranspose_one, Matrix.one_mul]
        abel
      have hQ : (Cᴴ * (Y - X) * C).PosSemidef := hP.conjTranspose_mul_mul_same C
      have hdX : X.det = Bᴴ.det * B.det := by rw [hXB, det_mul]
      clear_value B C
      have hdY : Y.det = (1 + Cᴴ * (Y - X) * C).det * X.det := by
        conv_lhs => rw [hsplit]
        rw [det_mul, det_mul, hdX]
        ring
      have hXnn := Complex.le_def.1 hX.det_nonneg
      have hQnn := Complex.le_def.1 (PosSemidef.one.add hQ).det_nonneg
      rw [hdY, Complex.mul_re, ← hXnn.2, ← hQnn.2]
      simp only [Complex.zero_im, mul_zero, sub_zero]
      have ha : 0 ≤ X.det.re := by simpa using hXnn.1
      exact le_mul_of_one_le_left ha (one_le_re_det_lemma_2 hQ))

end GlobalTheory.CompanionTheory.DetMonotone
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicityStatement
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_monotonicity : DetMono := by
  first | exact @GlobalTheory.CompanionTheory.DetMonotone.detMono | exact GlobalTheory.CompanionTheory.DetMonotone.detMono | (intros; apply GlobalTheory.CompanionTheory.DetMonotone.detMono <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.PatGrp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}

def Supp (Φ : ι → ι → Prop) (N : Matrix ι ι K) : Prop := ∀ i j, N i j ≠ 0 → Φ i j

theorem mem_patSet_iff (h : IsPat Φ) (u : GL ι K) :
    u ∈ patSet (K := K) Φ ↔ Supp Φ ((u : Matrix ι ι K) - 1) := by
  unfold patSet
  rw [Set.mem_setOf_eq]
  constructor
  · intro hu i j hN
    by_contra hΦ
    apply hN
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.sub_apply, Matrix.one_apply_eq, (hu i i).1 rfl, sub_self]
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, (hu i j).2 hij hΦ, sub_zero]
  · intro hS i j
    refine ⟨fun hij => ?_, fun hij hΦ => ?_⟩
    · subst hij
      have h0 : ((u : Matrix ι ι K) - 1) i i = 0 := by
        by_contra hne
        exact h.1 i (hS i i hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0
    · have h0 : ((u : Matrix ι ι K) - 1) i j = 0 := by
        by_contra hne
        exact hΦ (hS i j hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at h0

theorem Supp.mul (h : IsPat Φ) {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) :
    Supp Φ (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact h.2 i k j (hA i k (left_ne_zero_of_mul hk)) (hB k j (right_ne_zero_of_mul hk))

theorem Supp.add {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) : Supp Φ (A + B) := by
  intro i j hij
  by_cases ha : A i j = 0
  · apply hB
    intro hb
    apply hij
    rw [Matrix.add_apply, ha, hb, add_zero]
  · exact hA i j ha

theorem det_one_add (h : IsPat Φ) {N : Matrix ι ι K} (hN : Supp Φ N) : (1 + N).det = 1 := by
  classical
  let b : ι → ℕ := fun i => (Finset.univ.filter fun k => Φ k i).card
  have hb : ∀ i j, Φ i j → b i < b j := by
    intro i j hij
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact h.2 k i j hk hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.1 i
  have hN0 : ∀ i j, b j ≤ b i → N i j = 0 := by
    intro i j hle
    by_contra hne
    exact absurd (hb i j (hN i j hne)) (not_lt.2 hle)
  have hT : (1 + N).BlockTriangular b := by
    intro i j hlt
    have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, hN0 i j hlt.le, add_zero]
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have hblk : (1 + N).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show (1 + N) i j = (1 : Matrix {a' // b a' = a} {a' // b a' = a} K) ⟨i, hi⟩ ⟨j, hj⟩
    have hNij : N i j = 0 := hN0 i j (by rw [hi, hj])
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.add_apply, hNij, add_zero, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij, hNij, add_zero,
        Matrix.one_apply_ne (fun e => hij (congrArg Subtype.val e))]
  rw [hblk, Matrix.det_one]

def patSubgroup (h : IsPat Φ) : Subgroup (GL ι K) :=
  let M : Submonoid (GL ι K) :=
    { carrier := patSet (K := K) Φ
      mul_mem' := by
        intro u v hu hv
        have hu' := (mem_patSet_iff h u).1 hu
        have hv' := (mem_patSet_iff h v).1 hv
        refine (mem_patSet_iff h _).2 ?_
        have e : ((u * v : GL ι K) : Matrix ι ι K) - 1 =
            ((u : Matrix ι ι K) - 1) + ((v : Matrix ι ι K) - 1) +
              ((u : Matrix ι ι K) - 1) * ((v : Matrix ι ι K) - 1) := by
          rw [Units.val_mul]
          noncomm_ring
        rw [e]
        exact (hu'.add hv').add (hu'.mul h hv')
      one_mem' := by
        refine (mem_patSet_iff h _).2 ?_
        intro i j hij
        simp at hij }
  { M with
    inv_mem' := by
      intro u hu
      have hn : orderOf u ≠ 0 := (orderOf_pos u).ne'
      have : u⁻¹ = u ^ (orderOf u - 1) :=
        inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, pow_orderOf_eq_one])
      rw [this]
      exact M.pow_mem hu _ }


open Classical in
noncomputable def fill (Φ : ι → ι → Prop) (f : {p : ι × ι // Φ p.1 p.2} → K) : Matrix ι ι K := by
  classical
  exact fun i j => if h : Φ i j then f ⟨(i, j), h⟩ else 0

theorem supp_fill (f : {p : ι × ι // Φ p.1 p.2} → K) : Supp Φ (fill Φ f) := by
  intro i j hij
  by_contra hΦ
  apply hij
  simp [fill, hΦ]

theorem card_patSet (h : IsPat Φ) :
    (patSet (K := K) Φ).ncard = Fintype.card K ^ Nat.card {p : ι × ι // Φ p.1 p.2} := by
  classical
  have hunit : ∀ f : {p : ι × ι // Φ p.1 p.2} → K, IsUnit (1 + fill Φ f).det := fun f => by
    rw [det_one_add h (supp_fill f)]
    exact isUnit_one
  let e : patSet (K := K) Φ ≃ ({p : ι × ι // Φ p.1 p.2} → K) :=
    { toFun := fun u p => (u.1 : Matrix ι ι K) p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.nonsingInvUnit (1 + fill Φ f) (hunit f), by
        refine (mem_patSet_iff h _).2 ?_
        show Supp Φ ((1 + fill Φ f) - 1)
        rw [add_sub_cancel_left]
        exact supp_fill f⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        show 1 + fill Φ (fun p => (u.1 : Matrix ι ι K) p.1.1 p.1.2) = (u.1 : Matrix ι ι K)
        ext i j
        have hu := (show ∀ i j, (i = j → (u.1 : Matrix ι ι K) i j = 1) ∧
          (i ≠ j → ¬Φ i j → (u.1 : Matrix ι ι K) i j = 0) from u.2) i j
        rw [Matrix.add_apply]
        simp only [fill]
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, dite_eq_right (h.1 i), add_zero, hu.1 rfl]
        · rw [Matrix.one_apply_ne hij, zero_add]
          by_cases hΦ : Φ i j
          · rw [dite_eq_left hΦ]
          · rw [dite_eq_right hΦ, hu.2 hij hΦ]
      right_inv := fun f => by
        funext p
        show (1 + fill Φ f) p.1.1 p.1.2 = f p
        have hne : p.1.1 ≠ p.1.2 := fun e => h.1 p.1.2 (by have hp := p.2; rw [e] at hp; exact hp)
        rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
        simp only [fill]
        rw [dite_eq_left p.2] }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]

end GlobalTheory.CompanionTheory.PatGrp
end
end
