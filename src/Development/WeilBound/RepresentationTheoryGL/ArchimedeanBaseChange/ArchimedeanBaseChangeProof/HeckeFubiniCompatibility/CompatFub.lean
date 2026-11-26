module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH HeckeM heckeAct Repro)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

def CompatEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure], ∃ ν : Measure (Hf E a b), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant ∧
    Compat D μa μb ν

def CompatFub : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure], Compat D μa μb ν →
  ∀ F : H E a b → ℂ, Continuous F → HasCompactSupport F →
    ∫ g, F g ∂D.μ = ∫ ya : InfinitePlace E → G a, ∫ yb : InfinitePlace E → G b, ∫ h : Hf E a b,
      F (infGL E a (Units.map (Matrix.piRingEquiv (n := Fin a) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
            (MulEquiv.piUnits.symm ya)) * finGL E a h.1,
          infGL E b (Units.map (Matrix.piRingEquiv (n := Fin b) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
            (MulEquiv.piUnits.symm yb)) * finGL E b h.2) ∂ν ∂(Measure.pi fun _ => μb) ∂(Measure.pi fun _ => μa)

def TensTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  (μa : Measure (G a)) [μa.IsHaarMeasure] (μb : Measure (G b)) [μb.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)), IsMults μa ka va T → IsMults μb kb vb T →
  IsFinM ψ → IsTestM (tens ka kb ψ) ∧ adjM (tens ka kb ψ) = tens (adjK ka) (adjK kb) (adjF ψ)

def TensMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka ka' : Kers Ma) (kb kb' : Kers Mb) va va' vb vb' (T T' : ℝ) (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)), Compat D μa μb ν →
  IsMults μa ka va T → IsMults μb kb vb T → IsMults μa ka' va' T' → IsMults μb kb' vb' T' → IsFinM ψ → IsFinM ψ' →
  IsFinM (mulF ν ψ ψ') ∧
    mulM D.μ (tens ka kb ψ) (tens ka' kb' ψ') = tens (convK μa ka ka') (convK μb kb kb') (mulF ν ψ ψ')

def TensTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b)
  (κ : Type) [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) (Ta : Ops Ma) (Tb : Ops Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
  (N : Matrix κ κ ℂ) (g : H E a b), F.trM (tens ka kb ψ) (opM Ta Tb N) g =
    (∏ v, phiOf (Ma v) (Ta v) (ka v) (gInf v g.1)) * (∏ v, phiOf (Mb v) (Tb v) (kb v) (gInf v g.2)) *
      ∑ x, ∑ y, ψ x y (hFin g) * N y x

def VCBridge : Prop := ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) (M : KMod n)
  (Tθ : M.V →L[ℂ] M.V) (k : Mat n → (M.V →L[ℂ] M.V)) val (T : ℝ), (∀ u, Tθ * M.ρ u = M.ρ u * Tθ) → IsMult μ M k val T →
  VCClause (phiOf M Tθ k) → VeryCusp (phiOf M Tθ k)

def Repr {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (D : Dom E a b) {Ma : Mods E a} {Mb : Mods E b}
    {κ : Type} [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) : Prop :=
  (∀ i, Continuous (f i)) ∧ ∃ c : ℂ, c ≠ 0 ∧ PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f

def TypeOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
    ∀ (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] (μa : Measure (G a)) (μb : Measure (G b))
      (κ : Type) [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ))
      (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (f : Io Ma Mb κ → H E a b → ℂ),
      IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
      (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) → Repr D ka kb ψ f → ∀ i, TypeH K₁ K₂ W₁ W₂ (f i)

def SmoothOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  (μa : Measure (G a)) [μa.IsHaarMeasure] (μb : Measure (G b)) [μb.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ] (D : Dom E a b)
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (U : Subgroup (Hf E a b))
  (f : Io Ma Mb κ → H E a b → ℂ), IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ → IsOpen (U : Set (Hf E a b)) →
  (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (u * h) = ψ x y h) → Repr D ka kb ψ f →
  (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)

def GrowthOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type)
  [Fintype ι] (Φ : Matrix ι ι (H E a b → ℂ)) (M : ℕ) (f : ι → H E a b → ℂ) (c : ℂ), IsTestM Φ → (∀ i, Continuous (f i)) →
  LeftInv f → WL2 D M f → c ≠ 0 → PositivityTheory.Rg.BcB.E.conv D.μ Φ f = c • f →
  ∃ C N : ℝ, ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))

def EigAll {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} (χa : InfinitePlace E → Inf a)
    (χb : InfinitePlace E → Inf b) (f : ι → H E a b → ℂ) : Prop :=
  (∀ i v g m₂, IsEig (χa v) (along v g fun x => f i (x, m₂))) ∧ ∀ i v g m₁, IsEig (χb v) (along v g fun x => f i (m₁, x))

def InfEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Sm E n)) (v : InfinitePlace E)
  (t : Bool → ℕ → ℂ), (∃ φ ∈ S, φ ≠ 0) →
  (∀ φ ∈ S, ∀ g s m, ∀ x ∈ GLs n, gel s m (along v g φ.1) x = t s m • along v g φ.1 x) →
  ∃ χ : Inf n, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = t s m

def GelOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (c c' : ℂ)
  (v : InfinitePlace E) (g : ℝ → ℝ) (s : Bool) (m : ℕ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T →
  IsFinM ψ → IsBump g T →
  ((∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  (∀ i, Continuous (f i)) → c ≠ 0 → PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
  (∀ k', IsKer μa (Ma v) [] g (ka v) → IsKer μa (Ma v) [(s, m)] g k' →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v k') kb ψ) f = c' • f →
    ∀ i y m₂, ∀ x ∈ GLs a, gel s m (along v y fun z => f i (z, m₂)) x = (c' / c) • along v y (fun z => f i (z, m₂)) x) ∧
  ∀ k', IsKer μb (Mb v) [] g (kb v) → IsKer μb (Mb v) [(s, m)] g k' →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v k') ψ) f = c' • f →
    ∀ i y m₁, ∀ x ∈ GLs b, gel s m (along v y fun z => f i (m₁, z)) x = (c' / c) • along v y (fun z => f i (m₁, z)) x

def ActVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka ka' : Kers Ma) (kb kb' : Kers Mb) va va' vb vb' (T T' : ℝ) (ψ ψ' : Matrix κ κ (Hf E a b → ℂ))
  (f : Io Ma Mb κ → H E a b → ℂ) χa χb, Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
  Repr D ka kb ψ f →
  ((∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  EigAll χa χb f → IsMults μa ka' va' T' → IsMults μb kb' vb' T' → IsFinM ψ' →
  PositivityTheory.Rg.BcB.E.conv D.μ (tens ka' kb' ψ') f = (valA va' χa * valA vb' χb) • convF ν ψ' f

def FinHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (A κ : Type)
  [Fintype A] [Fintype κ] (ψ : Matrix κ κ (Hf E a b → ℂ)) (U : Subgroup (Hf E a b)), IsFinM ψ →
  IsOpen (U : Set (Hf E a b)) → IsCompact (U : Set (Hf E a b)) → (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (h * u) = ψ x y h) →
  ∃ h : HeckeM E a b (A × κ), (∀ i j, i.1 ≠ j.1 → h i j = 0) ∧ (∀ p q x y, h (p, x) (p, y) = h (q, x) (q, y)) ∧
    ∀ f : A × κ → H E a b → ℂ, (∀ i, ∀ u ∈ U, ∀ x, f i (x * finH u) = f i x) → convF ν ψ f = heckeAct h f

def AutOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) (f : ι → H E a b → ℂ)
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ))
  (W₂ : Submodule ℂ (Kinf E b → ℂ)) χa χb (C N : ℝ), IsOpen (K₁ : Set (GL (Fin a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin b) (Af E))) → FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → LeftInv f →
  (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) → (∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))) → EigAll χa χb f →
  (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
    (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
    ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

def InfConv : Prop := ∀ (n : ℕ) (x : ℕ → Fin n → ℂ) (y : Fin n → ℂ),
  (∀ m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (x k) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal y m))) → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ k in atTop, Multiset.Rel (fun p q => ‖p - q‖ ≤ ε) (Multiset.map (x k) Finset.univ.val) (Multiset.map y Finset.univ.val)

def ReproEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) (R : ℝ), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → Repro ν K W R

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E
open PositivityTheory.RgTw (G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

namespace PositivityTheory.Rg.BcB.CG

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def infP (n : ℕ) (y : InfinitePlace E → G n) : GA E n :=
  infGL E n (Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm y))

theorem infinitePart_mul (n : ℕ) (y y' : InfinitePlace E → G n) : infP n (y * y') = infP n y * infP n y' := by
  simp only [infP, map_mul]

theorem gInf_infGL (n : ℕ) (v : InfinitePlace E) (x : GL (Fin n) (Cinf E)) (i j : Fin n) :
    (gInf v (infGL E n x)).val i j = x.val i j v :=
  congrArg (fun y : GL (Fin n) (Cinf E) => y.val i j v) (pInf_infGL (E := E) (a := n) x)

theorem gInf_infP (n : ℕ) (y : InfinitePlace E → G n) (v : InfinitePlace E) : gInf v (infP n y) = y v := by
  ext i j
  exact gInf_infGL n v _ i j

theorem gFin_infP (n : ℕ) (y : InfinitePlace E → G n) : gFin (infP n y) = 1 :=
  pFin_infGL _

theorem gInf_finGL (n : ℕ) (v : InfinitePlace E) (k : GL (Fin n) (Af E)) : gInf v (finGL E n k) = 1 := by
  ext i j
  have h2 : (GeneralLinearGroup.map (pInf E) (finGL E n k)).val i j = (1 : GL (Fin n) (Cinf E)).val i j :=
    congrArg (fun y : GL (Fin n) (Cinf E) => y.val i j) (pInf_finGL (E := E) (a := n) k)
  change (GeneralLinearGroup.map (pInf E) (finGL E n k)).val i j v = _
  rw [h2]
  by_cases h : i = j <;> simp [h]

omit [IsCMField E] in
theorem gFin_finGL (n : ℕ) (k : GL (Fin n) (Af E)) : gFin (finGL E n k) = k :=
  pFin_finGL k

theorem infinitePart_gInf (n : ℕ) (g : GA E n) : infP n (fun v => gInf v g) = infGL E n (GeneralLinearGroup.map (pInf E) g) := by
  rfl

theorem infinitePart_mul_finGL (n : ℕ) (g : GA E n) : infP n (fun v => gInf v g) * finGL E n (gFin g) = g := by
  rw [infinitePart_gInf]; exact infGL_mul_finGL g

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_gInf (n : ℕ) (v : InfinitePlace E) : Continuous (gInf (n := n) v : GA E n → G n) :=
  Continuous.units_map _ (continuous_id.matrix_map ((continuous_apply v).comp continuous_pInf'))

omit [IsCMField E] in
theorem continuous_gFin (n : ℕ) : Continuous (gFin : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)

theorem continuous_infGL' (n : ℕ) : Continuous (infGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

omit [IsCMField E] in
theorem continuous_finGL' (n : ℕ) : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_infP (n : ℕ) : Continuous (infP (E := E) n) := by
  refine (continuous_infGL' n).comp ?_
  refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
    Matrix (Fin n) (Fin n) ℂ)).symm.continuous
  exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j

def splitGA (n : ℕ) : (InfinitePlace E → G n) × GL (Fin n) (Af E) ≃ₜ* GA E n where
  toFun p := infP n p.1 * finGL E n p.2
  invFun g := (fun v => gInf v g, gFin g)
  left_inv p := by
    ext1
    · funext v; simp [gInf_infP, gInf_finGL]
    · simp [gFin_infP, gFin_finGL]
  right_inv g := infinitePart_mul_finGL n g
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, infinitePart_mul, map_mul]
    have h : finGL E n p.2 * infP n q.1 = infP n q.1 * finGL E n p.2 := (infGL_comm _ _).symm
    rw [show infP n p.1 * finGL E n p.2 * (infP n q.1 * finGL E n q.2) =
      infP n p.1 * ((finGL E n p.2 * infP n q.1) * finGL E n q.2) by simp only [mul_assoc], h]
    simp only [mul_assoc]
  continuous_toFun := ((continuous_infP n).comp continuous_fst).mul ((continuous_finGL' n).comp continuous_snd)
  continuous_invFun := (continuous_pi fun v => continuous_gInf n v).prodMk (continuous_gFin n)

theorem splitGA_apply (n : ℕ) (p : (InfinitePlace E → G n) × GL (Fin n) (Af E)) :
    splitGA n p = infP n p.1 * finGL E n p.2 := rfl

theorem gInf_splitGA (n : ℕ) (p : (InfinitePlace E → G n) × GL (Fin n) (Af E)) (v : InfinitePlace E) :
    gInf v (splitGA n p) = p.1 v := by
  simp [splitGA_apply, gInf_infP, gInf_finGL]

theorem gFin_splitGA (n : ℕ) (p : (InfinitePlace E → G n) × GL (Fin n) (Af E)) : gFin (splitGA n p) = p.2 := by
  simp [splitGA_apply, gFin_infP, gFin_finGL]

def splitH (a b : ℕ) : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b) ≃ₜ* H E a b where
  toFun z := (splitGA a (z.1, z.2.2.1), splitGA b (z.2.1, z.2.2.2))
  invFun g := (((splitGA a).symm g.1).1, ((splitGA b).symm g.2).1, ((splitGA a).symm g.1).2, ((splitGA b).symm g.2).2)
  left_inv z := by simp
  right_inv g := by simp
  map_mul' z w := by
    simp only [Prod.fst_mul, Prod.snd_mul, ← map_mul, Prod.mk_mul_mk]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem splitH_apply (a b : ℕ) (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    splitH a b z = (infP a z.1 * finGL E a z.2.2.1, infP b z.2.1 * finGL E b z.2.2.2) := rfl

theorem gInf_splitH₁ {a b : ℕ} (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) (v : InfinitePlace E) :
    gInf v (splitH a b z).1 = z.1 v := gInf_splitGA a _ v

theorem gInf_splitH₂ {a b : ℕ} (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) (v : InfinitePlace E) :
    gInf v (splitH a b z).2 = z.2.1 v := gInf_splitGA b _ v

theorem hFin_splitH {a b : ℕ} (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    hFin (splitH a b z) = z.2.2 := Prod.ext (gFin_splitGA a _) (gFin_splitGA b _)

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
noncomputable section

open MeasureTheory Matrix
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG

variable {n : ℕ}

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isUnit_det_unitary (u : Matrix.unitaryGroup (Fin n) ℂ) : IsUnit (u.1.det) :=
  Matrix.isUnit_det_of_left_inverse (Unitary.star_mul_self_of_mem u.2)

theorem mul_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ) :
    u₁.1 * y * u₂.1 ∈ GLs n := by
  show (u₁.1 * y * u₂.1).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (isUnit_det_unitary u₁).ne_zero hy) (isUnit_det_unitary u₂).ne_zero

section Mult

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
  {val : Inf n → ℂ} {T : ℝ}

theorem mult_continuous (h : IsMult μ M k val T) : Continuous fun y : G n => k y.val := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  have e : (fun y : G n => k y.val) = fun y => ∑ i, c i • ks i y.val :=
    funext fun y => hk _ (val_mem_GLs y)
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((hks i).2.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs).const_smul (c i)

theorem mult_exists_lg (h : IsMult μ M k val T) : ∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → k y = 0 := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  choose R hR using fun i => (hks i).2.2.1
  refine ⟨∑ i, |R i|, fun y hy hlt => ?_⟩
  rw [hk _ hy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hR i y hy (lt_of_le_of_lt ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i))) hlt), smul_zero]

theorem mult_hasCompactSupport (h : IsMult μ M k val T) : HasCompactSupport fun y : G n => k y.val := by
  obtain ⟨R, hR⟩ := mult_exists_lg h
  exact HasCompactSupport.intro ((GlobalTheory.T.length_continuous_proper_sublevel n).2 R) fun y hy => hR _ (val_mem_GLs y) (not_le.1 hy)

theorem mult_equivariant (h : IsMult μ M k val T) : ∀ y ∈ GLs n, ∀ u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ,
    k (u₁.1 * y * u₂.1) = M.ρ u₁ * k y * M.ρ u₂ := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  intro y hy u₁ u₂
  rw [hk _ (mul_mem_GLs hy u₁ u₂), hk _ hy, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hks i).2.2.2.1 y hy u₁ u₂]
  simp only [mul_smul_comm, smul_mul_assoc]

theorem mult_equivariant_val (h : IsMult μ M k val T) (y : G n) (u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ) :
    k (u₁.1 * y.val * u₂.1) = M.ρ u₁ * k y.val * M.ρ u₂ :=
  mult_equivariant h _ (val_mem_GLs y) u₁ u₂

end Mult

section Ent

variable {M : KMod n}

theorem continuous_ent {X : Type} [TopologicalSpace X] {f : X → (M.V →L[ℂ] M.V)} (hf : Continuous f) (i j : Ix M) :
    Continuous fun x => ent M (f x) i j :=
  continuous_const.inner (hf.clm_apply continuous_const)

theorem hasCompactSupport_ent {X : Type} [TopologicalSpace X] {f : X → (M.V →L[ℂ] M.V)} (hf : HasCompactSupport f)
    (i j : Ix M) : HasCompactSupport fun x => ent M (f x) i j :=
  hf.comp_left (g := fun A => ent M A i j) (ent_zero M i j)

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {k : Mat n → (M.V →L[ℂ] M.V)} {val : Inf n → ℂ} {T : ℝ}

theorem mult_ent (h : IsMult μ M k val T) (i j : Ix M) :
    Continuous (fun y : G n => ent M (k y.val) i j) ∧ HasCompactSupport (fun y : G n => ent M (k y.val) i j) :=
  ⟨continuous_ent (mult_continuous h) i j, hasCompactSupport_ent (mult_hasCompactSupport h) i j⟩

end Ent

end PositivityTheory.Rg.BcB.CG

end
end
