module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibres
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Tors

theorem torsion_exhaust_geometric : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → IsUnit (N : R) → ∀ (C : Type) (b : C → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c := by
  intro hL R _ _ _ P N hN1 hNu C b hb hgen K _ _ x p hp
  have hNu' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hNu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨hfin, -, -, het, hcard⟩ := hL.mulN (Spec (CommRingCat.of R)) P N hN1
  have : Etale (mulA P.A N).left := het hNu'
  have : IsSeparated (mulA P.A N).left := inferInstance
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ≫ mulA P.A N = y ^ N := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of R))}, (1 : Z ⟶ P.A).left = Z.hom ≫ η[P.A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let Kk : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.snd (mulA P.A N).left η[P.A].left)
  have hη : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  let i : Kk ⟶ P.A := Over.homMk (pullback.fst (mulA P.A N).left η[P.A].left) (by
    change pullback.fst (mulA P.A N).left η[P.A].left ≫ P.A.hom = pullback.snd (mulA P.A N).left η[P.A].left
    rw [← Over.w (mulA P.A N), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hlift : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ^ N = 1 → ∃ l : Z ⟶ Kk, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA P.A N).left = Z.hom ≫ η[P.A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over (Spec (CommRingCat.of R))} (l l' : Z ⟶ Kk), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  have : Etale Kk.hom := inferInstanceAs (Etale (pullback.snd (mulA P.A N).left η[P.A].left))
  have : IsSeparated Kk.hom := inferInstanceAs (IsSeparated (pullback.snd (mulA P.A N).left η[P.A].left))

  have inj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R))
      (σ τ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A), σ ^ N = 1 → τ ^ N = 1 →
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ τ → σ = τ := by
    intro F _ y σ τ hσ hτ e
    obtain ⟨ls, rfl⟩ := hlift σ hσ
    obtain ⟨lt, rfl⟩ := hlift τ hτ
    have e' : toUnit (Over.mk y) ≫ ls = toUnit (Over.mk y) ≫ lt := hmono _ _ (by simpa using e)
    have hu : (toUnit (Over.mk y)).left = y := by
      simpa using Over.w (toUnit (Over.mk y))
    have : ConnectedSpace (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of R)))
    have key : ls.left = lt.left := by
      refine GlobalTheory.eq_of_connected_of_unramified_of_point Kk.hom
        ((Over.w ls).trans (Over.w lt).symm) y ?_
      have h2 := congr(($e').left)
      rw [Over.comp_left, Over.comp_left, hu] at h2
      exact h2
    rw [Over.OverMorphism.ext key]
  have natK : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), (N : F) ≠ 0 :=
    fun y => by simpa using (hNu.map (Spec.preimage y).hom).ne_zero
  let T0 := {σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A // σ ∈ Set.range b}
  have tor : ∀ σ : T0, σ.1 ^ N = 1 := fun σ => by obtain ⟨c, hc⟩ := σ.2; rw [← hc]; exact hb c
  let res : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      T0 → {q : Over.mk y ⟶ P.A // q ^ N = 1} := fun y σ =>
    ⟨toUnit _ ≫ σ.1, by rw [← MonObj.comp_pow, tor σ, MonObj.comp_one]⟩
  have resInj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      Function.Injective (res y) := fun y σ τ e =>
    Subtype.ext (inj y σ.1 τ.1 (tor σ) (tor τ) (congrArg Subtype.val e))
  let Ω := AlgebraicClosure (FractionRing R)
  have c0 := hcard Ω (TF (R := R) Ω).hom (natK (TF (R := R) Ω).hom)
  have cx := hcard K x (natK x)
  have hpos : N ^ (2 * P.g) ≠ 0 := pow_ne_zero _ (by omega)
  have : Finite {q : Over.mk (TF (R := R) Ω).hom ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (c0 ▸ hpos)
  have : Finite {q : Over.mk x ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (cx ▸ hpos)
  have bij0 : Function.Bijective (res (TF (R := R) Ω).hom) := by
    refine ⟨resInj _, fun q => ?_⟩
    obtain ⟨c, hc⟩ := hgen q.1 q.2
    exact ⟨⟨b c, c, rfl⟩, Subtype.ext hc.symm⟩
  have cT : Nat.card T0 = N ^ (2 * P.g) := (Nat.card_eq_of_bijective _ bij0).trans c0
  have bijx := (Nat.bijective_iff_injective_and_card (res x)).2 ⟨resInj x, cT.trans cx.symm⟩
  obtain ⟨⟨σ, c, rfl⟩, hσ⟩ := bijx.2 ⟨p, hp⟩
  exact ⟨c, (congrArg Subtype.val hσ).symm⟩

end GlobalTheory.Poinc.Tors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibresStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.torsion_sections_exhaust_geometric_fibres : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → IsUnit (N : R) → ∀ (C : Type) (b : C → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c := by
  first | exact @GlobalTheory.Poinc.Tors.torsion_exhaust_geometric | exact GlobalTheory.Poinc.Tors.torsion_exhaust_geometric | (intros; apply GlobalTheory.Poinc.Tors.torsion_exhaust_geometric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorIndicatorMemHecke
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZpowMemOfValOne
noncomputable section

namespace GlobalTheory.DoubleCosetDivisors

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem zpow_mem_of_val_one {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (k : ℤ) : u ^ k ∈ O := by
  apply hO
  rw [map_zpow₀, hu, _root_.one_zpow]

theorem diag_mem {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O)
    {u : L} (hu : (Valued.v : L → WithZero (Multiplicative ℤ)) u = 1) (e : Fin n → ℤ) :
    ∃ U ∈ Formalism.UG.GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => u ^ e i) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  let Uo : GL (Fin n) O :=
    { val := Matrix.diagonal (fun i => ⟨u ^ e i, zpow_mem_of_val_one hO hu (e i)⟩)
      inv := Matrix.diagonal (fun i => ⟨u ^ (-e i), zpow_mem_of_val_one hO hu (-e i)⟩)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [mul_inv_cancel₀ (zpow_ne_zero _ hu0)]
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; apply Subtype.ext
        simp [inv_mul_cancel₀ (zpow_ne_zero _ hu0)] }
  refine ⟨Formalism.UG.bc (n := Fin n) O.subtype Uo, ⟨Uo, rfl⟩, ?_⟩
  ext i j
  simp [Formalism.UG.bc, Uo, Matrix.diagonal_apply]

theorem sameDiv_doubleCoset {n : ℕ} {O : Subring L}
    (hO : ∀ x : L, (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ 1 → x ∈ O) {d : List ℤ} {g s : GL (Fin n) L}
    (hg : GlobalTheory.SphPar.HasDiv O d g) (hs : GlobalTheory.SphPar.HasDiv O d s) :
    ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)),
      g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) := by
  obtain ⟨ϖ, hϖ, a1, ha1, b1, hb1, hg⟩ := hg
  obtain ⟨ϖ', hϖ', a2, ha2, b2, hb2, hs⟩ := hs
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  have h0' : ϖ' ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact hne hϖ'.symm
  have hu : (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ / ϖ') = 1 := by
    rw [map_div₀, hϖ, hϖ', div_self hne]
  obtain ⟨U, hU, hUe⟩ := diag_mem hO hu (fun i : Fin n => d.getD i 0)
  have hD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) =
      (U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) := by
    rw [hUe, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← mul_zpow, div_mul_cancel₀ _ h0']
  refine ⟨⟨a1 * U * a2⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha1 hU) (Subgroup.inv_mem _ ha2)⟩,
    ⟨b2⁻¹ * b1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hb2) hb1⟩, ?_⟩
  apply Units.ext
  have e1 : ((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul a2
  have e2 : (b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv b2
  simp only [Units.val_mul]
  rw [hg, hs, hD]
  calc (a1 : Matrix (Fin n) (Fin n) L) * ((U : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0)) * (b1 : Matrix (Fin n) (Fin n) L)
      = (a1 : Matrix (Fin n) (Fin n) L) * (U : Matrix (Fin n) (Fin n) L) * (((a2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (a2 : Matrix (Fin n) (Fin n) L))
          * Matrix.diagonal (fun i : Fin n => ϖ' ^ d.getD i 0) * ((b2 : Matrix (Fin n) (Fin n) L) * ((b2⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * (b1 : Matrix (Fin n) (Fin n) L) := by
        rw [e1, e2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {O : Subring L}, (∀ (x : L), (Valued.v : L → WithZero (Multiplicative ℤ)) x ≤ (1 : WithZero (Multiplicative ℤ)) → x ∈ O) → ∀ {d : List ℤ} {g s : GL (Fin n) L}, GlobalTheory.SphPar.HasDiv O d g → GlobalTheory.SphPar.HasDiv O d s → ∃ (a : ↥(Formalism.UG.GLint (Fin n) O)) (b : ↥(Formalism.UG.GLint (Fin n) O)), g = (↑a : GL (Fin n) L) * s * (↑b : GL (Fin n) L) :=
  fun hO _ _ _ hg hs => sameDiv_doubleCoset hO hg hs

end GlobalTheory.DoubleCosetDivisors
end
end

noncomputable section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem hasDiv_mul_mul {O : Subring L} {d : List ℤ} {g : GL (Fin n) L} (h : HasDiv O d g) {a b : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) O) (hb : b ∈ GLint (Fin n) O) : HasDiv O d (a * g * b) := by
  obtain ⟨ϖ, hϖ, a', ha', b', hb', e⟩ := h
  refine ⟨ϖ, hϖ, a * a', mul_mem ha ha', b' * b, mul_mem hb' hb, ?_⟩
  simp only [Units.val_mul, e, Matrix.mul_assoc]

theorem HasDiv.exists_eq_mul_mul {O : Subring L} (hO : ∀ x : L, Valued.v x ≤ 1 → x ∈ O) {d : List ℤ}
    {g s : GL (Fin n) L} (hg : HasDiv O d g) (hs : HasDiv O d s) :
    ∃ a b : GLint (Fin n) O, g = a * s * b := by
  first
  | exact @_root_.GlobalTheory.DoubleCosetDivisors.main
  | exact _root_.GlobalTheory.DoubleCosetDivisors.main
  | (apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DoubleCosetDivisors.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DoubleCosetDivisors.main ..)

end Local

end GlobalTheory.SphGal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerne
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.WhitAlg

open GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_psiNeg :
    Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

theorem whit_eq (F : GA E a → ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit F g = ∫ X in vecDomain E (Pos a),
      F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := rfl

theorem integrableOn_whit {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) :
    IntegrableOn (fun X => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hF.comp (continuous_uGL.mul continuous_const)).mul continuous_psiNeg
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add_mul {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (c : ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g := by
  rw [whit_eq, whit_eq, whit_eq, ← integral_const_mul,
    ← integral_add (integrableOn_whit hF g) ((integrableOn_whit hG g).const_mul c)]
  congr 1
  funext X
  ring

theorem whit_kerInf {F : GA E a → ℂ} (hF : Continuous F)
    (hgr : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N)
    {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : GlobalTheory.JSW.IsRapidInf ν k γ) (g : GA E a) :
    GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  let ψ : (Pos a → Ad E) → ℂ := fun Y => (GroundTheory.Global.adelicChar E (-supSum 0 Y) : ℂ)
  let f : (Pos a → Ad E) → X → ℂ := fun Y x => k x * F (uGL Y * g * infGL E a (γ x)) * ψ Y
  have hmeas : Measurable (Function.uncurry f) := by
    haveI : BorelSpace ((Pos a → Ad E) × Lie E a) := Prod.borelSpace
    have hc : ContinuousOn (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) :=
      (GlobalTheory.ConstTermSmooth.continuousOn_chart hF).comp
        (((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
        fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hφ : Measurable fun p : (Pos a → Ad E) × X => ((p.1, toL (γ p.2).val) : (Pos a → Ad E) × Lie E a) :=
      measurable_fst.prodMk (hk.2.1.comp measurable_snd)
    have h1 : Measurable fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val) := by
      have e : (fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val)) =
          (Set.univ ×ˢ invSet E a).restrict (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2) ∘
            fun p => (⟨(p.1, toL (γ p.2).val), Set.mem_univ _, val_mem_invSet _⟩ :
              (Set.univ ×ˢ invSet E a : Set ((Pos a → Ad E) × Lie E a))) := rfl
      rw [e]
      exact hc.restrict.measurable.comp hφ.subtype_mk
    have e2 : Function.uncurry f = fun p => k p.2 * chart F (uGL p.1 * g) (toL (γ p.2).val) * ψ p.1 := by
      funext p
      exact congrArg (fun z => k p.2 * z * ψ p.1) (chart_val F _ _).symm
    rw [e2]
    exact ((hk.1.comp measurable_snd).mul h1).mul (continuous_psiNeg.measurable.comp measurable_fst)
  obtain ⟨C, N, hC⟩ := hgr ((fun Y => uGL Y * g) '' closure (vecDomain E (Pos a)))
    (isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const))
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have hb : Integrable (fun p : (Pos a → Ad E) × X => (1 : ℝ) * (C * (‖k p.2‖ * height (γ p.2) ^ N))) (μ.prod ν) :=
      (integrable_const (1 : ℝ)).mul_prod ((hk.2.2 N).const_mul C)
    have hae : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ vecDomain E (Pos a) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_vecDomain)
    refine hb.mono' hmeas.aestronglyMeasurable (hae.mono fun p hp => ?_)
    have hb1 := hC (uGL p.1 * g) ⟨p.1, subset_closure hp, rfl⟩ (γ p.2)
    change ‖k p.2 * F (uGL p.1 * g * infGL E a (γ p.2)) * (GroundTheory.Global.adelicChar E (-supSum 0 p.1) : ℂ)‖ ≤ _
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    calc ‖k p.2‖ * ‖F (uGL p.1 * g * infGL E a (γ p.2))‖ ≤ ‖k p.2‖ * (C * height (γ p.2) ^ N) :=
          mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
      _ = 1 * (C * (‖k p.2‖ * height (γ p.2) ^ N)) := by ring
  have hin : ∀ Y, GlobalTheory.JSW.kerInf ν k γ F (uGL Y * g) * ψ Y = ∫ x, f Y x ∂ν := fun Y => by
    simp only [f, GlobalTheory.JSW.kerInf]
    rw [integral_mul_const]
  calc GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ Y, ∫ x, f Y x ∂ν ∂μ := by
        rw [whit_eq]
        congr 1
        funext Y
        exact hin Y
    _ = ∫ x, ∫ Y, f Y x ∂μ ∂ν := integral_integral_swap hint
    _ = _ := by
        congr 1
        funext x
        rw [whit_eq, ← integral_const_mul]
        congr 1
        funext Y
        simp only [f, ψ, mul_assoc]

theorem whit_linear_kerInf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ),
    Continuous F → Continuous G →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧
      ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
        GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g =
          ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  intro E _ _ _ a F G hF hG hFg _
  exact ⟨fun c g => whit_add_mul hF hG c g, fun X _ ν _ k γ hk g => whit_kerInf hF hFg ν hk g⟩

end GlobalTheory.JSW.WhitAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerneStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ), Continuous F → Continuous G → (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) → (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) → (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧ ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  first | exact @GlobalTheory.JSW.WhitAlg.whit_linear_kerInf | exact GlobalTheory.JSW.WhitAlg.whit_linear_kerInf | (intros; apply GlobalTheory.JSW.WhitAlg.whit_linear_kerInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjData
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.PointSumConj

theorem exists_conj_iff {G : Type} [Group G] (K : Subgroup G) (a m : G) :
    (∃ k ∈ K, a * k * a⁻¹ = m) ↔ a⁻¹ * m * a ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : a⁻¹ * (a * k * a⁻¹) * a = k := by group
    rw [this]; exact hk
  · intro h
    exact ⟨a⁻¹ * m * a, h, by group⟩

theorem mem_stab {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) (z : Γ) :
    z ∈ stab ι₁ ι₂ K₁ K₂ x ↔ x.1⁻¹ * ι₁ z * x.1 ∈ K₁ ∧ x.2⁻¹ * ι₂ z * x.2 ∈ K₂ := by
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, exists_conj_iff]

theorem finsum_dc_translate {G : Type} [Group G] (H H' K : Subgroup G) (a : G)
    (hH : ∀ h ∈ H, a * h * a⁻¹ ∈ H') (hH' : ∀ h ∈ H', a⁻¹ * h * a ∈ H) (F F' : G → ℂ)
    (hF : ∀ h ∈ H, ∀ k ∈ K, ∀ x, F (h * x * k) = F x) (hF' : ∀ x, F' (a * x) = F x) :
    ∑ᶠ q : DoubleCoset.Quotient (H' : Set G) (K : Set G), F' (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G), F (Quotient.out q) := by
  have key : ∀ x, F' (Quotient.out (DoubleCoset.mk H' K (a * x))) = F x := by
    intro x
    obtain ⟨h', hh', k, hk, he⟩ := (@DoubleCoset.eq _ _ H' K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk H' K (a * x))).symm
    rw [he]
    have : h' * (a * x) * k = a * ((a⁻¹ * h' * a) * x * k) := by group
    rw [this, hF', hF _ (hH' _ hh') _ hk]
  refine (finsum_eq_of_bijective (fun q : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    DoubleCoset.mk H' K (a * Quotient.out q)) ⟨?_, ?_⟩ (fun q => (key _).symm)).symm
  · intro q₁ q₂ h
    obtain ⟨h', hh', k, hk, he⟩ := (@DoubleCoset.eq _ _ H' K _ _).1 h
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
    refine (@DoubleCoset.eq _ _ H K _ _).2 ⟨a⁻¹ * h' * a, hH' _ hh', k, hk, ?_⟩
    have : Quotient.out q₂ = a⁻¹ * (a * Quotient.out q₂) := by group
    rw [this, he]; group
  · intro q'
    refine ⟨DoubleCoset.mk H K (a⁻¹ * Quotient.out q'), ?_⟩
    obtain ⟨h, hh, k, hk, he⟩ := (@DoubleCoset.eq _ _ H K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk H K (a⁻¹ * Quotient.out q'))).symm
    simp only
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' q']
    exact (@DoubleCoset.eq _ _ H' K _ _).2 ⟨(a * h * a⁻¹)⁻¹, H'.inv_mem (hH _ hh), k⁻¹, K.inv_mem hk, by group⟩

end GlobalTheory.PointSumConj

namespace GlobalTheory.PointSumConj

theorem conj_mem_iff {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) (m : G) :
    k⁻¹ * m * k ∈ K ↔ m ∈ K := by
  rw [Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk)]

theorem card_stab_translate {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (y : Γ) (x k : G₁ × G₂) (hk : k ∈ K₁.prod K₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ ((ι₁ y, ι₂ y) * x * k)) = Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
  rw [Subgroup.mem_prod] at hk
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj y).toEquiv fun z => ?_)).symm
  simp only [SetLike.mem_coe, mem_stab, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply,
    Prod.fst_mul, Prod.snd_mul, map_mul, map_inv]
  have e1 : (ι₁ y * x.1 * k.1)⁻¹ * (ι₁ y * ι₁ z * (ι₁ y)⁻¹) * (ι₁ y * x.1 * k.1) =
      k.1⁻¹ * (x.1⁻¹ * ι₁ z * x.1) * k.1 := by group
  have e2 : (ι₂ y * x.2 * k.2)⁻¹ * (ι₂ y * ι₂ z * (ι₂ y)⁻¹) * (ι₂ y * x.2 * k.2) =
      k.2⁻¹ * (x.2⁻¹ * ι₂ z * x.2) * k.2 := by group
  rw [e1, e2, conj_mem_iff K₁ hk.1, conj_mem_iff K₂ hk.2]

theorem stab_conj {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (g₁ : G₁) (g₂ : G₂) (x : G₁ × G₂) :
    stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) K₁ K₂
      ((g₁⁻¹, g₂⁻¹) * x) = stab ι₁ ι₂ K₁ K₂ x := by
  ext z
  simp only [mem_stab, Prod.fst_mul, Prod.snd_mul, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (g₁⁻¹ * x.1)⁻¹ * (g₁⁻¹ * ι₁ z * g₁⁻¹⁻¹) * (g₁⁻¹ * x.1) = x.1⁻¹ * ι₁ z * x.1 := by group
  have e2 : (g₂⁻¹ * x.2)⁻¹ * (g₂⁻¹ * ι₂ z * g₂⁻¹⁻¹) * (g₂⁻¹ * x.2) = x.2⁻¹ * ι₂ z * x.2 := by group
  rw [e1, e2]

theorem pointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ G₁ G₂ _ _ _ ι₁ ι₂ θ K₁ K₂ γ g₁ δ g₂ f φ hf hφ hγ hδ
  unfold pointSum
  refine finsum_dc_translate (ι₁.prod ι₂).range
    (((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁).prod ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)).range
    (K₁.prod K₂) (g₁⁻¹, g₂⁻¹) ?_ ?_
    (fun x => ((Nat.card (stab ι₁ ι₂ K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2)))
    (fun x => ((Nat.card (stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)
      K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * (g₁⁻¹ * γ * g₁) * x.1) * φ (x.2⁻¹ * (g₂⁻¹ * δ * θ g₂) * θ x.2))) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply]
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply] <;> group
  · rintro _ ⟨y, rfl⟩ k hk x
    have hk' := (Subgroup.mem_prod).1 hk
    simp only [MonoidHom.prod_apply] at *
    rw [card_stab_translate ι₁ ι₂ K₁ K₂ y x k hk]
    congr 2
    · have e : ((ι₁ y, ι₂ y) * x * k).1⁻¹ * γ * ((ι₁ y, ι₂ y) * x * k).1 =
          k.1⁻¹ * (x.1⁻¹ * ((ι₁ y)⁻¹ * γ * ι₁ y) * x.1) * k.1 := by simp only [Prod.fst_mul]; group
      have e' : (ι₁ y)⁻¹ * γ * ι₁ y = γ := by rw [mul_assoc, ← hγ y]; group
      rw [e, e', hf _ hk'.1]
    · have e : ((ι₁ y, ι₂ y) * x * k).2⁻¹ * δ * θ ((ι₁ y, ι₂ y) * x * k).2 =
          k.2⁻¹ * (x.2⁻¹ * ((ι₂ y)⁻¹ * δ * θ (ι₂ y)) * θ x.2) * θ k.2 := by
        simp only [Prod.snd_mul, map_mul]; group
      have e' : (ι₂ y)⁻¹ * δ * θ (ι₂ y) = δ := by rw [mul_assoc, ← hδ y]; group
      rw [e, e', hφ _ hk'.2]
  · intro x
    rw [stab_conj]
    congr 2
    · congr 1; simp only [Prod.fst_mul]; group
    · congr 1; simp only [Prod.snd_mul, map_mul, map_inv]; group

end GlobalTheory.PointSumConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjDataStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.PointSumConj.pointSum_conj_data) | (exact GlobalTheory.PointSumConj.pointSum_conj_data) | (intros; apply GlobalTheory.PointSumConj.pointSum_conj_data  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

abbrev FM (P : Pair G) : Type := AdjoinRoot P.pol

def jM (P : Pair G) : FM P →ₐ[G.F] G.C :=
  Ideal.Quotient.liftₐ _ (aeval (P.γ : G.C)) fun f hf => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 hf
    rw [map_mul, Pair.pol, minpoly.aeval, zero_mul]

theorem jM_mk (P : Pair G) (f : G.F[X]) : jM P (AdjoinRoot.mk P.pol f) = aeval (P.γ : G.C) f := rfl

theorem jM_root (P : Pair G) : jM P (AdjoinRoot.root P.pol) = P.γ := by
  rw [← AdjoinRoot.mk_X, jM_mk, aeval_X]

theorem jM_injective (P : Pair G) : Function.Injective (jM P) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk] at ha
  exact AdjoinRoot.mk_eq_zero.2 (minpoly.dvd G.F _ ha)

theorem jM_algQ (P : Pair G) (q : ℚ) : jM P (algebraMap ℚ (FM P) q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F (FM P), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem jM_comm (P : Pair G) (a : FM P) : jM P a * P.γ = P.γ * jM P a := by
  rw [← jM_root, ← map_mul, ← map_mul, mul_comm]

theorem exists_jM (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : ∃ a, jM P a = u := by
  have hc : u ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact hu.symm
  rw [GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC _ P.reg.2 P.reg.1,
    Algebra.adjoin_singleton_eq_range_aeval] at hc
  obtain ⟨f, rfl⟩ := hc
  exact ⟨AdjoinRoot.mk _ f, rfl⟩

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh, map_mul]

theorem sh_one : sh G (1 : G.C) = 1 := by simp [sh]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by simp [sh, map_add (f := _)]

theorem sh_zero : sh G (0 : G.C) = 0 := by simp [sh]

theorem sh_sh (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_algF (a : G.F) : sh G (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) :=
  G.star_F a

def iC (P : Pair G) (x : G.C) : G.C := (P.β : G.C) * sh G x * ((P.β⁻¹ : G.Cˣ) : G.C)

theorem iC_mul (P : Pair G) (x y : G.C) : iC P (x * y) = iC P y * iC P x := by
  simp only [iC, sh_mul, mul_assoc, Units.inv_mul_cancel_left]

theorem iC_one (P : Pair G) : iC P 1 = 1 := by simp [iC, sh_one]

theorem iC_add (P : Pair G) (x y : G.C) : iC P (x + y) = iC P x + iC P y := by
  simp [iC, sh_add, mul_add, add_mul]

theorem iC_zero (P : Pair G) : iC P 0 = 0 := by simp [iC, sh_zero]

theorem iC_algF (P : Pair G) (a : G.F) :
    iC P (algebraMap G.F G.C a) = algebraMap G.F G.C (IsCMField.complexConj G.F a) := by
  rw [iC, sh_algF, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

theorem iC_algQ (P : Pair G) (q : ℚ) : iC P (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, iC_algF]
  congr 1
  simp

theorem iC_gamma_mul (P : Pair G) : iC P P.γ * P.γ = algebraMap ℚ G.C P.c := by
  have h := P.sim
  have h2 : (P.β : G.C) * sh G P.γ = ((P.γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C P.c * P.β) := by
    rw [← h]; simp only [← mul_assoc, Units.inv_mul, one_mul]
  calc iC P P.γ * P.γ = ((P.β : G.C) * sh G P.γ) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := rfl
    _ = ((P.γ⁻¹ : G.Cˣ) : G.C) * algebraMap ℚ G.C P.c * P.γ := by
        rw [h2]; simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [mul_assoc, Algebra.commutes, ← mul_assoc, Units.inv_mul, one_mul]

theorem iC_comm (P : Pair G) (u : G.C) (hu : u * P.γ = P.γ * u) : iC P u * P.γ = P.γ * iC P u := by
  have h1 : iC P u * iC P P.γ = iC P P.γ * iC P u := by rw [← iC_mul, ← iC_mul, hu]
  have hg : iC P P.γ = algebraMap ℚ G.C P.c * ((P.γ⁻¹ : G.Cˣ) : G.C) := by
    rw [← iC_gamma_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [hg, ← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc] at h1
  have hc : IsUnit (algebraMap ℚ G.C P.c) := (P.c.isUnit).map _
  have h2 := hc.mul_left_cancel h1
  calc iC P u * P.γ = P.γ * (((P.γ⁻¹ : G.Cˣ) : G.C) * iC P u) * P.γ := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = P.γ * (iC P u * ((P.γ⁻¹ : G.Cˣ) : G.C)) * P.γ := by rw [h2]
    _ = _ := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem iC_iC (P : Pair G) (x : G.C) : iC P (iC P x) = x := by
  have hb : sh G (P.β : G.C) = P.β := P.sym
  have hbi : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have e : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β = 1 := by
      rw [← hb, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C) = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e, one_mul]
  simp only [iC, sh_mul, hb, hbi, sh_sh, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

def iMf (P : Pair G) (a : FM P) : FM P := (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose

theorem jM_iMf (P : Pair G) (a : FM P) : jM P (iMf P a) = iC P (jM P a) :=
  (exists_jM P (iC P (jM P a)) (iC_comm P _ (jM_comm P a))).choose_spec

def iM (P : Pair G) : FM P →ₐ[ℚ] FM P where
  toFun := iMf P
  map_one' := jM_injective P (by rw [jM_iMf, map_one, iC_one])
  map_mul' a b := jM_injective P (by
    rw [mul_comm (iMf P a), jM_iMf, map_mul, map_mul, jM_iMf, jM_iMf, iC_mul])
  map_zero' := jM_injective P (by rw [jM_iMf, map_zero, iC_zero])
  map_add' a b := jM_injective P (by rw [jM_iMf, map_add (f := _), map_add (f := _), jM_iMf, jM_iMf, iC_add])
  commutes' q := jM_injective P (by rw [jM_iMf, jM_algQ, iC_algQ])

theorem jM_iM (P : Pair G) (a : FM P) : jM P (iM P a) = iC P (jM P a) := jM_iMf P a

theorem iM_algF (P : Pair G) (a : G.F) :
    iM P (algebraMap G.F (FM P) a) = algebraMap G.F (FM P) (IsCMField.complexConj G.F a) :=
  jM_injective P (by rw [jM_iM, AlgHom.commutes, AlgHom.commutes, iC_algF])

theorem iM_root_mul (P : Pair G) :
    iM P (AdjoinRoot.root P.pol) * AdjoinRoot.root P.pol = algebraMap ℚ (FM P) P.c :=
  jM_injective P (by rw [map_mul, jM_iM, jM_root, jM_algQ, iC_gamma_mul])

theorem iM_iM (P : Pair G) (a : FM P) : iM P (iM P a) = a :=
  jM_injective P (by rw [jM_iM, jM_iM, iC_iC])

theorem mul_iM_of_cent (P : Pair G) (w : P.cent) (a : FM P) (ha : jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C)) :
    a * iM P a = algebraMap ℚ (FM P) ((w : G.Cˣ × ℚˣ).2 : ℚ) :=
  jM_injective P (by
    rw [map_mul, jM_iM, jM_algQ, ha, iC, ← mul_assoc, ← mul_assoc, w.2.2, mul_assoc, Units.mul_inv, mul_one])

theorem exists_pow_mem_conj {H : Type} [Group H] (K K₀ : Subgroup H) (g y : H) (hK : K.Commensurable K₀)
    (hy : y ∈ K.map (MulAut.conj g).toMonoidHom) :
    ∃ m : ℕ, 0 < m ∧ y ^ m ∈ K₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨k, hk, rfl⟩ := hy
  obtain ⟨m, hm0, -, hm⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := K₀.subgroupOf K) hK.2.relIndex_ne_zero (⟨k, hk⟩ : K)
  refine ⟨m, hm0, k ^ m, ?_, by simp [map_pow]⟩
  simpa [Subgroup.mem_subgroupOf] using hm

end GlobalTheory.StabFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultiple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Renorm

theorem alg_renorm {M : Type} [CommGroup M] {q q₀ a p p₀ g g₀ x y : M} (h₀ : q = y * x⁻¹ * q₀)
    (h₁ : a = g₀ * (q₀ * p₀)⁻¹) (h₂ : p = x * p₀) (h₃ : g = y * g₀) : q * (a * p) = g := by
  rw [h₀, h₁, h₂, h₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section Norm
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_unit_normW (w₀ : W0 U) (hw : w₀.IsGen) (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) :
    ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, NormW U w₀ (GlobalTheory.UU.scaleGen a ρ) := by
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨JA₀, hA₀⟩ := exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := exists_good' U.LG.isLB z₀
  let eK : Spec (CommRingCat.of (FractionRing R)) ⟶ ((Over.pullback (jK R)).obj G).left :=
    eSec ((Over.pullback (jK R)).obj G)
  have h₁ : eK ≫ U.gen.hom.left = eSec A.A := EvalZero.eK_gen U
  have h₂ : eK ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := EvalZero.eK_fst
  have hsurj : ∀ u : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z₀)ˣ,
      ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, gm (𝟙 _) z₀ ⊤ a = u := by
    intro u
    obtain ⟨V, hV, s, hs⟩ := (Spec (CommRingCat.of (FractionRing R))).presheaf.exists_germ_eq u.val
    obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ =>
      (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y) ▸ hV
    have hu : IsUnit s := (Spec (CommRingCat.of (FractionRing R))).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain rfl : z₀ = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y
      exact (congrArg IsUnit hs).mpr u.isUnit
    exact ⟨hu.unit, Units.ext ((gm_val _ z₀ ⊤ trivial _).trans hs)⟩
  obtain ⟨a, ha⟩ := hsurj (val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (jK R) z₀ JG₀ *
    (pw w₀ eK z₀ (JA₀ (eSec A.A)) (JG₀ (jK R ≫ eSec G)) *
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) (Z := Spec (CommRingCat.of (FractionRing R)))
        ρ (𝟙 _) z₀ JA₀)⁻¹)
  refine ⟨a, hw, GlobalTheory.UU.scaleGen_isGen a hρ, fun z JA JG hA hG => ?_⟩
  obtain rfl : z₀ = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ z
  have mA : ∀ J, Good A.L z₀ J → U.gen.hom.left (eK z₀) ∈ A.L.U (J (eSec A.A)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ A.L.U (J (eSec A.A))) h₁).mpr (hJ _)
  have mG : ∀ J, Good U.LG.L z₀ J → pullback.fst G.hom (jK R) (eK z₀) ∈ U.LG.L.U (J (jK R ≫ eSec G)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ U.LG.L.U (J (jK R ≫ eSec G))) h₂).mpr (hJ _)
  have b₀ : gw w₀ eK z₀ (JG (jK R ≫ eSec G)) (fun _ => JA (eSec A.A)) =
      pw w₀ eK z₀ (JA (eSec A.A)) (JG (jK R ≫ eSec G)) := rfl
  have b₁ := pw_trans hw eK z₀ (mA _ hA) (mA _ hA₀) (mG _ hG) (mG _ hG₀)
  have b₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1)
    (Z := Spec (CommRingCat.of (FractionRing R))) hρ (𝟙 _) hA hA₀
  have b₃ := val_tr (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rigGen (jK R) hG hG₀
  have b₄ := GlobalTheory.UU.val_scaleGen (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) a ρ (𝟙 _) hA
  rw [h₁, h₂] at b₁
  rw [Fintype.prod_unique, zpow_one] at b₂ b₃
  rw [Category.id_comp] at b₂
  rw [b₀, b₄]
  exact alg_renorm b₁ ha b₂ b₃

end Norm

theorem alg_rig {M : Type} [CommGroup M] (g v : M) (k : ℤ) :
    g ^ (k - 1) * (v ^ k * v⁻¹) = (g * v) ^ k * (g * v)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem alg_frame {M : Type} [CommGroup M] {g t α r : M} {k : ℤ} (h : t ^ k = α * r ^ (1 : ℤ)) :
    (g * t) ^ k = g ^ (k - 1) * α * (g * r) ^ (1 : ℤ) := by
  apply Additive.ofMul.injective
  replace h := congrArg Additive.ofMul h
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at h ⊢
  linear_combination (norm := module) h

section Tors
variable {S : Scheme.{0}} {P : PolAV S}

theorem isTorsFrame_scale (rig : LB.Gen (P.L.pull (eSec P.A))) (a : Γ(S, ⊤)ˣ) {n : ℕ} {T : Over S} {x : T ⟶ P.A}
    {τ τ' : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x τ) (hτ' : τ'.IsGen)
    (ht : ∀ z J, Good P.L z J → val τ' (𝟙 _) z J = gm T.hom z ⊤ a * val τ (𝟙 _) z J) :
    IsTorsFrame P (GlobalTheory.UU.scaleGen a rig) n x τ' := by
  obtain ⟨hn, -, α, hα, hN, hc⟩ := H
  let u : Γ(P.A.left, ⊤)ˣ := pullU P.A.hom ⊤ a ^ ((n : ℤ) ^ 2 - 1)
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z),
      gm r z ⊤ u = gm (r ≫ P.A.hom) z ⊤ a ^ ((n : ℤ) ^ 2 - 1) := fun Z r z =>
    (map_zpow _ _ _).trans (congrArg (· ^ _) (gm_pull r P.A.hom z ⊤ trivial a))
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) J, Good P.L z J →
      FrameMove.rval (GlobalTheory.UU.scaleGen a rig) r z J = gm r z ⊤ a * FrameMove.rval rig r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) a rig r hJ
  have hα' : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) J, Good P.L z J →
      val (GlobalTheory.UU.scaleGen u α) r z J = gm r z ⊤ u * val α r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen u α r hJ
  have he : eSec P.A ≫ P.A.hom = 𝟙 S := Over.w η[P.A]
  refine ⟨hn, hτ', GlobalTheory.UU.scaleGen u α, GlobalTheory.UU.scaleGen_isGen u hα, corr_of_val P.isLB fun y J hJ => ?_,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  · have e0 : val α (𝟙 _ ≫ eSec P.A) y J =
        FrameMove.rval rig (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (FrameMove.rval rig (𝟙 _) y J)⁻¹ :=
      (val_pull hJ α (eSec P.A) (𝟙 _)).symm.trans ((val_corr hJ hN (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))
    have e1 : val (rigPow P.A P.L (GlobalTheory.UU.scaleGen a rig) ((n : ℤ) ^ 2)) (𝟙 _) y J =
        FrameMove.rval (GlobalTheory.UU.scaleGen a rig) (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_pull hJ, hα' _ _ _ _ hJ, hu, e0, val_mul hJ, e1, val_inv, hr _ _ _ _ hJ, Category.assoc, he,
      Category.id_comp]
    rw [show val (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) (GlobalTheory.UU.scaleGen a rig) (𝟙 (𝟙_ (Over S)).left) y J = _ from hr _ _ _ _ hJ]
    exact alg_rig (M := (S.presheaf.stalk y)ˣ) _ _ _
  · have a1 : val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α (𝟙 _ ≫ x.left) y J * FrameMove.rval rig (𝟙 _ ≫ T.hom) y J ^ (1 : ℤ) :=
      (map_zpow _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (FrameMove.val_rigT _ _ _ hJ))))
    rw [FrameMove.val_powFrame, val_mul hJ, val_pull hJ, FrameMove.val_rigT _ _ _ hJ, hα' _ _ _ _ hJ, hu,
      hr _ _ _ _ hJ, ht y J hJ, Category.assoc, Over.w x]
    simp only [Category.id_comp] at a1 ⊢
    exact alg_frame a1

end Tors

theorem cst_gm {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ) (z : (TFK (R := R) F).left) :
    (gm (jFK (R := R) F) z ⊤ a).val = cst (R := R) F z (algebraMap (FractionRing R) F
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val)) := by
  rw [← gs_unit _ z ⊤ trivial]
  have e : a.val = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val) := by simp
  conv_lhs => rw [e]
  exact FrameMove.gs_spMap (algebraMap (FractionRing R) F) z _

theorem exists_renorm : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ (ρ' : LB.Gen (A.L.pull (eSec A.A))) (c : FractionRing R), c ≠ 0 ∧ NormW U w₀ ρ' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (x : TFK (R := R) F ⟶ A.A) (fr fr' : FrAt x), IsTorsFrame A ρ N x fr → fr'.IsGen → (∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (algebraMap (FractionRing R) F c)) * (val fr (𝟙 _) z J).val) → IsTorsFrame A ρ' N x fr' := by
  intro R _ _ I D A G _ _ U w₀ hw ρ hρ
  obtain ⟨a, ha⟩ := exists_unit_normW U w₀ hw ρ hρ
  refine ⟨GlobalTheory.UU.scaleGen a ρ, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val, ?_, ha,
    fun F _ _ N x fr fr' H hfr' hv => ?_⟩
  · exact (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  · refine isTorsFrame_scale ρ a H hfr' fun z J hJ => Units.ext ?_
    rw [Units.val_mul, hv z J hJ]
    exact congrArg (· * _) (cst_gm F a z).symm

end GlobalTheory.Poinc.Renorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultipleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.exists_renormalization_rigidification_multiple : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ (ρ' : LB.Gen (A.L.pull (eSec A.A))) (c : FractionRing R), c ≠ 0 ∧ NormW U w₀ ρ' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (x : TFK (R := R) F ⟶ A.A) (fr fr' : FrAt x), IsTorsFrame A ρ N x fr → fr'.IsGen → (∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (algebraMap (FractionRing R) F c)) * (val fr (𝟙 _) z J).val) → IsTorsFrame A ρ' N x fr' := by
  first | exact @GlobalTheory.Poinc.Renorm.exists_renorm | exact GlobalTheory.Poinc.Renorm.exists_renorm | (intros; apply GlobalTheory.Poinc.Renorm.exists_renorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivJacobson

theorem exists_specializes {R : Type} [CommRing R] {J : Ideal R} (hJ : J ≤ Ideal.jacobson ⊥)
    (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum (R ⧸ J), p ⤳ PrimeSpectrum.comap (Ideal.Quotient.mk J) q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : J ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem kTriv_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (J : Ideal R), J ≤ Ideal.jacobson ⊥ → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → RelAmple B M → ∀ (Y₀ : Over (Spec (CommRingCat.of (R ⧸ J)))) [GrpObj Y₀] (b : Y₀.left ⟶ B.left), IsGrpPullback Y₀ B (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) b → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → KTriv Y₀ N₀ → KTriv B M := by
  intro R _ _ J hJ B _ hB M hM hA Y₀ _ b hb N₀ hN₀ e hK
  have key : ∀ p : Spec (CommRingCat.of R), ∃ U : (Spec (CommRingCat.of R)).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj B) (M.pull (pullback.fst B.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL := fun p => LB.isLB_pull hM (pullback.fst B.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U B _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback B (U p).ι) _ _ hM hL (fun p => GlobalTheory.lbIso_refl (hL p)) hB
    (fun p => GlobalTheory.isAbelianScheme_pullback_obj (U p).ι B hB) hK

end GlobalTheory.KTrivJacobson
end
