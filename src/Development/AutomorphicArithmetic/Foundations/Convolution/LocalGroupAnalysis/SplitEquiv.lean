module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
noncomputable section

open MeasureTheory Topology Filter UpperTheory.ConvolutionTheory.G
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.T4

section
variable {V G Gi : Type} {Gv : V → Type} [Group G] [Group Gi] [∀ v, Group (Gv v)]

def US (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)) (S : Finset V) : Subgroup G where
  carrier := {g | ∀ v ∉ S, p v g ∈ K v}
  one_mem' v _ := by rw [map_one]; exact one_mem _
  mul_mem' {a b} ha hb v hv := by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
  inv_mem' {a} ha v hv := by rw [map_inv]; exact inv_mem (ha v hv)

theorem mem_US {p : ∀ v, G →* Gv v} {K : ∀ v, Subgroup (Gv v)} {S : Finset V} {g : G} :
    g ∈ US p K S ↔ ∀ v ∉ S, p v g ∈ K v := Iff.rfl

def prS (q : G →* Gi) (p : ∀ v, G →* Gv v) (S : Finset V) : G →* Gi × ∀ v : S, Gv v :=
  q.prod (Pi.monoidHom fun v : S => p v)

theorem prS_apply (q : G →* Gi) (p : ∀ v, G →* Gv v) (S : Finset V) (g : G) :
    prS q p S g = (q g, fun v : S => p v g) := rfl

structure RP [TopologicalSpace G] [TopologicalSpace Gi] [∀ v, TopologicalSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)) : Prop where
  cq : Continuous q
  cp : ∀ v, Continuous (p v)
  opn : ∀ v, IsOpen (K v : Set (Gv v))
  cpt : ∀ v, IsCompact (K v : Set (Gv v))
  ae : ∀ g, ∀ᶠ v in cofinite, p v g ∈ K v
  opnU : ∀ S : Finset V, IsOpen (US p K S : Set G)
  ext : ∀ g g', q g = q g' → (∀ v, p v g = p v g') → g = g'
  surj : ∀ (gi : Gi) (gv : ∀ v, Gv v), (∀ᶠ v in cofinite, gv v ∈ K v) → ∃ g, q g = gi ∧ ∀ v, p v g = gv v
  prop : ∀ (Ci : Set Gi) (C : ∀ v, Set (Gv v)), IsCompact Ci → (∀ v, IsCompact (C v)) →
    (∀ᶠ v in cofinite, C v ⊆ K v) → IsCompact {g | q g ∈ Ci ∧ ∀ v, p v g ∈ C v}

def Eul [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)) (μ : Measure G) (μi : Measure Gi)
    (m : ∀ v, Measure (Gv v)) (a : NNReal) (S : Finset V) : Prop :=
  (μ.restrict (US p K S : Set G)).map (prS q p S) = a • μi.prod (Measure.pi fun v : S => m v)

def cen (f : G →* Gi) (g : G) : Subgroup.centralizer {g} →* Subgroup.centralizer {f g} where
  toFun t := ⟨f t, by
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_singleton_iff.mp t.2).map f)⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' s t := Subtype.ext (map_mul f _ _)

end

def QPush : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (T' : Type) [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T']
    (μ : Measure G) (j : T →* G) (ν : Measure T) (μ' : Measure H) (j' : T' →* H) (ν' : Measure T'), Pair μ j ν → Pair μ' j' ν' →
    ∀ U : Subgroup G, IsOpen (U : Set G) → ∀ (π : G →* H) (πT : T →* T'), Continuous π → Continuous πT →
    (∀ t, π (j t) = j' (πT t)) → (μ.restrict (U : Set G)).map π = μ' → (ν.restrict (j ⁻¹' (U : Set G))).map πT = ν' →
    ∀ (F : G → ℂ) (F' : H → ℂ), Measurable F → (∀ t g, F (j t * g) = F g) → Measurable F' → (∀ t g, F' (j' t * g) = F' g) →
      (∀ g, F g ≠ 0 → g ∈ Set.range j * (U : Set G)) → (∀ u ∈ U, F u = F' (π u)) → qI μ j ν F = qI μ' j' ν' F'

def SplitEquiv : Prop :=
  ∀ (G₁ R G : Type) [Group G₁] [TopologicalSpace G₁] [Group R] [TopologicalSpace R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (i : G₁ →* G) (d : G →* R) (c : R →* G), IsEmbedding i → Continuous d → Continuous c → (∀ s, d (c s) = s) →
    (∀ s g, c s * g = g * c s) → (∀ g, d g = 1 ↔ g ∈ Set.range i) →
    ∃ e : G₁ × R ≃ₜ* G, ∀ x, e x = i x.1 * c x.2

def SplitQ : Prop :=
  ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (T₁ : Type) [Group T₁] [TopologicalSpace T₁] [IsTopologicalGroup T₁] [LocallyCompactSpace T₁] [T2Space T₁]
    [SecondCountableTopology T₁] [MeasurableSpace T₁] [BorelSpace T₁]
    (R : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G₁) (j₁ : T₁ →* G₁) (ν : Measure T₁) (l : Measure R), Pair μ j₁ ν → Uni l →
    ∀ (e : G₁ × R ≃ₜ* G) (eT : T₁ × R ≃ₜ* T) (j : T →* G), (∀ x, j (eT x) = e (j₁ x.1, x.2)) →
      Pair ((μ.prod l).map e) j ((ν.prod l).map eT) ∧ ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) →
        qI μ j₁ ν (fun x => F (e (x, 1))) = qI ((μ.prod l).map e) j ((ν.prod l).map eT) F

def UniOf : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure →
    (μ.IsMulRightInvariant → Uni μ) ∧ ((∀ s t : G, s * t = t * s) → Uni μ)

def HaarEx : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)), μ.IsHaarMeasure → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) →
    ∀ S : Finset V, ∃ a : NNReal, a ≠ 0 ∧ Eul q p K μ μi m a S

def HaarConst : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)), μ.IsHaarMeasure → μi.IsHaarMeasure →
    (∀ v, (m v).IsHaarMeasure ∧ m v (K v) = 1) → ∃ a : NNReal, a ≠ 0 ∧ ∀ S : Finset V, Eul q p K μ μi m a S

def UniLoc : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)), Uni μ → μi.IsHaarMeasure → (∀ v, (m v).IsHaarMeasure) →
    Uni μi ∧ ∀ v, Uni (m v)

def RPCen : Prop :=
  ∀ (V G Gi : Type) (Gv : V → Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [T2Space Gi]
    [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] [∀ v, T2Space (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v)), RP q p K → ∀ g : G,
    RP (cen q g) (fun v => cen (p v) g) (fun v => (K v).comap (Subgroup.centralizer {p v g}).subtype)

def EulerSupp : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v))
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Ti : Type) [Group Ti] [TopologicalSpace Ti] [IsTopologicalGroup Ti] [LocallyCompactSpace Ti] [T2Space Ti]
    [SecondCountableTopology Ti] [MeasurableSpace Ti] [BorelSpace Ti]
    (Tv : V → Type) [∀ v, Group (Tv v)] [∀ v, TopologicalSpace (Tv v)] [∀ v, IsTopologicalGroup (Tv v)]
    [∀ v, LocallyCompactSpace (Tv v)] [∀ v, T2Space (Tv v)] [∀ v, SecondCountableTopology (Tv v)] [∀ v, MeasurableSpace (Tv v)]
    [∀ v, BorelSpace (Tv v)]
    (qT : T →* Ti) (pT : ∀ v, T →* Tv v) (KT : ∀ v, Subgroup (Tv v)), RP q p K → RP qT pT KT →
    ∀ (j : T →* G) (ji : Ti →* Gi) (jv : ∀ v, Tv v →* Gv v), (∀ t, q (j t) = ji (qT t)) → (∀ v t, p v (j t) = jv v (pT v t)) →
    (∀ v t, t ∈ KT v ↔ jv v t ∈ K v) →
    ∀ S : Finset V, ∀ (Fi : Gi → ℂ) (Fv : ∀ v, Gv v → ℂ), Measurable Fi → (∀ t g, Fi (ji t * g) = Fi g) →
    (∀ v, Measurable (Fv v) ∧ ∀ t g, Fv v (jv v t * g) = Fv v g) →
    (∀ v ∉ S, ∀ x, ((∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 1) ∧ ((¬ ∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 0)) →
    Measurable (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) ∧
    (∀ g, Fi (q g) * ∏ᶠ v, Fv v (p v g) ≠ 0 → g ∈ Set.range j * (US p K S : Set G)) ∧
    ∀ u ∈ US p K S, Fi (q u) * ∏ᶠ v, Fv v (p v u) = Fi (q u) * ∏ v : S, Fv v (p v u)

def Euler : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v))
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Ti : Type) [Group Ti] [TopologicalSpace Ti] [IsTopologicalGroup Ti] [LocallyCompactSpace Ti] [T2Space Ti]
    [SecondCountableTopology Ti] [MeasurableSpace Ti] [BorelSpace Ti]
    (Tv : V → Type) [∀ v, Group (Tv v)] [∀ v, TopologicalSpace (Tv v)] [∀ v, IsTopologicalGroup (Tv v)]
    [∀ v, LocallyCompactSpace (Tv v)] [∀ v, T2Space (Tv v)] [∀ v, SecondCountableTopology (Tv v)] [∀ v, MeasurableSpace (Tv v)]
    [∀ v, BorelSpace (Tv v)]
    (qT : T →* Ti) (pT : ∀ v, T →* Tv v) (KT : ∀ v, Subgroup (Tv v)), RP q p K → RP qT pT KT →
    ∀ (j : T →* G) (ji : Ti →* Gi) (jv : ∀ v, Tv v →* Gv v), (∀ t, q (j t) = ji (qT t)) → (∀ v t, p v (j t) = jv v (pT v t)) →
    (∀ v t, t ∈ KT v ↔ jv v t ∈ K v) →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)) (ν : Measure T) (νi : Measure Ti) (nv : ∀ v, Measure (Tv v)),
    Pair μ j ν → Pair μi ji νi → (∀ v, Pair (m v) (jv v) (nv v)) → ∀ (S : Finset V) (a b : NNReal), a ≠ 0 → b ≠ 0 →
    Eul q p K μ μi m a S → Eul qT pT KT ν νi nv b S →
    ∀ (Fi : Gi → ℂ) (Fv : ∀ v, Gv v → ℂ), Measurable Fi → (∀ t g, Fi (ji t * g) = Fi g) →
    (∀ v, Measurable (Fv v) ∧ ∀ t g, Fv v (jv v t * g) = Fv v g) →
    (∀ v ∉ S, ∀ x, ((∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 1) ∧ ((¬ ∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 0)) →
    Measurable (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) ∧
    qI μ j ν (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) =
      ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * qI μi ji νi Fi * ∏ v ∈ S, qI (m v) (jv v) (nv v) (Fv v)

def Fub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν → ∀ (θ : G →* G) (δ : G) (z : ℝ → G), Continuous θ → Continuous z →
    (∀ t, (j t)⁻¹ * δ * θ (j t) = δ) →
    (∀ D : Set G, IsCompact D → ∃ C : Set G, IsCompact C ∧ ∀ x, x⁻¹ * δ * θ x ∈ D → ∃ t, ∃ y ∈ C, x = j t * y) →
    (∀ D : Set G, IsCompact D → ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, z s * (x⁻¹ * δ * θ x) ∈ D → s ∈ B) →
    ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      Measurable (fun x => ∫ s, φ (z s * (x⁻¹ * δ * θ x))) ∧
      qI μ j ν (fun x => ∫ s, φ (z s * (x⁻¹ * δ * θ x))) = ∫ s, qI μ j ν (fun x => φ (z s * (x⁻¹ * δ * θ x)))

def SideAbs : Prop :=
  ∀ (V : Type) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Gi : Type) [Group Gi] [TopologicalSpace Gi] [IsTopologicalGroup Gi] [LocallyCompactSpace Gi] [T2Space Gi]
    [SecondCountableTopology Gi] [MeasurableSpace Gi] [BorelSpace Gi]
    (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)]
    [∀ v, LocallyCompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, SecondCountableTopology (Gv v)] [∀ v, MeasurableSpace (Gv v)]
    [∀ v, BorelSpace (Gv v)]
    (q : G →* Gi) (p : ∀ v, G →* Gv v) (K : ∀ v, Subgroup (Gv v))
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (Ti : Type) [Group Ti] [TopologicalSpace Ti] [IsTopologicalGroup Ti] [LocallyCompactSpace Ti] [T2Space Ti]
    [SecondCountableTopology Ti] [MeasurableSpace Ti] [BorelSpace Ti]
    (Tv : V → Type) [∀ v, Group (Tv v)] [∀ v, TopologicalSpace (Tv v)] [∀ v, IsTopologicalGroup (Tv v)]
    [∀ v, LocallyCompactSpace (Tv v)] [∀ v, T2Space (Tv v)] [∀ v, SecondCountableTopology (Tv v)] [∀ v, MeasurableSpace (Tv v)]
    [∀ v, BorelSpace (Tv v)]
    (qT : T →* Ti) (pT : ∀ v, T →* Tv v) (KT : ∀ v, Subgroup (Tv v)), RP q p K → RP qT pT KT →
    ∀ (j : T →* G) (ji : Ti →* Gi) (jv : ∀ v, Tv v →* Gv v), (∀ t, q (j t) = ji (qT t)) → (∀ v t, p v (j t) = jv v (pT v t)) →
    (∀ v t, t ∈ KT v ↔ jv v t ∈ K v) →
    ∀ (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v)) (ν : Measure T) (νi : Measure Ti) (nv : ∀ v, Measure (Tv v)),
    Pair μ j ν → Pair μi ji νi → (∀ v, Pair (m v) (jv v) (nv v)) → ∀ (S : Finset V) (a b : NNReal), a ≠ 0 → b ≠ 0 →
    Eul q p K μ μi m a S → Eul qT pT KT ν νi nv b S →
    ∀ (θ : G →* G) (θi : Gi →* Gi) (θv : ∀ v, Gv v →* Gv v), (∀ g, q (θ g) = θi (q g)) → (∀ v g, p v (θ g) = θv v (p v g)) →
    Continuous θi → (∀ v, Continuous (θv v)) → ∀ (δ : G) (z : ℝ → G), Continuous z → (∀ v s, p v (z s) = 1) →
    (∀ t, (j t)⁻¹ * δ * θ (j t) = δ) →
    (∀ D : Set Gi, IsCompact D → ∃ C : Set Gi, IsCompact C ∧ ∀ x, x⁻¹ * q δ * θi x ∈ D → ∃ t, ∃ y ∈ C, x = ji t * y) →
    (∀ D : Set Gi, IsCompact D → ∃ B : Set ℝ, IsCompact B ∧ ∀ s x, q (z s) * (x⁻¹ * q δ * θi x) ∈ D → s ∈ B) →
    ∀ (φi : Gi → ℂ) (φ : ∀ v, Gv v → ℂ), Continuous φi → HasCompactSupport φi → (∀ v, Continuous (φ v)) →
    (∀ v ∉ S, φ v = (K v : Set (Gv v)).indicator 1 ∧
      ∀ x, x⁻¹ * p v δ * θv v x ∈ K v ↔ ∃ t, ∃ y ∈ K v, x = jv v t * y) →
    Measurable (fun x => ∫ s, φi (q (z s * (x⁻¹ * δ * θ x))) * ∏ᶠ v, φ v (p v (z s * (x⁻¹ * δ * θ x)))) ∧
    qI μ j ν (fun x => ∫ s, φi (q (z s * (x⁻¹ * δ * θ x))) * ∏ᶠ v, φ v (p v (z s * (x⁻¹ * δ * θ x)))) =
      ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * (∫ s, qI μi ji νi fun x => φi (q (z s) * (x⁻¹ * q δ * θi x))) *
        ∏ v ∈ S, qI (m v) (jv v) (nv v) fun x => φ v (x⁻¹ * p v δ * θv v x)

def SepSc : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (r : Rˣ) (M : Matrix (Fin n) (Fin n) R), M.charpoly.Separable → ((r : R) • M).charpoly.Separable

def CentComm : Prop :=
  ∀ (F R : Type) [Field F] [CharZero F] [CommRing R] (f : F →+* R) (n : ℕ) (γ : Matrix (Fin n) (Fin n) F), γ.charpoly.Separable →
    ∀ s t : Matrix (Fin n) (Fin n) R, s * γ.map f = γ.map f * s → t * γ.map f = γ.map f * t → s * t = t * s

end UpperTheory.ConvolutionTheory.T4
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
open MeasureTheory Topology
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {T : Type} [Group T] [TopologicalSpace T]
    [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] {μ : Measure G} {j : T →* G} {ν : Measure T}

private theorem lint_eq (hp : Pair μ j ν) {Φ : G → ℝ≥0∞} (hΦ : Measurable Φ) (hi : ∀ t g, Φ (j t * g) = Φ g)
    {ρ ρ' : G → ℝ≥0∞} (h : IsNrm j ν ρ) (h' : IsNrm j ν ρ') :
    ∫⁻ x, Φ x * ρ x ∂μ = ∫⁻ x, Φ x * ρ' x ∂μ := by
  obtain ⟨⟨hμ, -⟩, hj, hν, hν'⟩ := hp
  have hjm : Measurable j := hj.continuous.measurable
  have hm := h.1
  have hm' := h'.1
  calc ∫⁻ x, Φ x * ρ x ∂μ = ∫⁻ x, ∫⁻ t, Φ x * ρ x * ρ' (j t * x) ∂ν ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ (by fun_prop), h'.2, mul_one]
    _ = ∫⁻ t, ∫⁻ x, Φ x * ρ x * ρ' (j t * x) ∂μ ∂ν :=
        lintegral_lintegral_swap (Measurable.aemeasurable (by unfold Function.uncurry; fun_prop))
    _ = ∫⁻ t, ∫⁻ x, Φ x * ρ' x * ρ (j t⁻¹ * x) ∂μ ∂ν := by
        refine lintegral_congr fun t => ?_
        rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => Φ x * ρ x * ρ' (j t * x)) (j t⁻¹)]
        refine lintegral_congr fun x => ?_
        rw [hi, ← mul_assoc (j t), ← map_mul, mul_inv_cancel, map_one, one_mul, mul_right_comm]
    _ = ∫⁻ x, ∫⁻ t, Φ x * ρ' x * ρ (j t⁻¹ * x) ∂ν ∂μ :=
        (lintegral_lintegral_swap (Measurable.aemeasurable (by unfold Function.uncurry; fun_prop))).symm
    _ = ∫⁻ x, Φ x * ρ' x ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_eq_self (μ := ν) (fun t => ρ (j t * x)), h.2,
          mul_one]

private theorem ae_lt_top_nrm (hp : Pair μ j ν) {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) : ∀ᵐ x ∂μ, ρ x < ⊤ := by
  obtain ⟨⟨hμ, -⟩, hj, hν, hν'⟩ := hp
  have hjm : Measurable j := hj.continuous.measurable
  have hm := h.1
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ t ∂ν, ρ (j t * x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ae_lt_top (by fun_prop) (by rw [h.2]; exact ENNReal.one_ne_top)
  have hs : MeasurableSet {p : G × T | ρ (j p.2 * p.1) < ⊤} :=
    measurableSet_lt (by fun_prop) measurable_const
  have h2 : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ρ (j t * x) < ⊤ := (Measure.ae_ae_comm hs).1 h1
  obtain ⟨t, ht⟩ := h2.exists
  have := (measurePreserving_mul_left μ (j t)⁻¹).quasiMeasurePreserving.ae ht
  simpa using this

private theorem map_eq (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F) (hi : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (h : IsNrm j ν ρ) (h' : IsNrm j ν ρ') :
    (μ.withDensity ρ).map F = (μ.withDensity ρ').map F := by
  ext s hs
  have key := lint_eq hp (Φ := fun x => s.indicator 1 (F x)) ((measurable_one.indicator hs).comp hF)
    (fun t g => by rw [hi]) h h'
  have e : ∀ r : G → ℝ≥0∞, (μ.withDensity r).map F s = ∫⁻ x, s.indicator 1 (F x) * r x ∂μ := fun r => by
    rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), ← lintegral_indicator (hF hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : F x ∈ s <;> simp [Set.indicator, hx]
  rw [e, e, key]

private theorem int_eq (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F)
    {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) :
    ∫ x, F x * ((ρ x).toReal : ℂ) ∂μ = ∫ z, z ∂((μ.withDensity ρ).map F) := by
  rw [integral_map hF.aemeasurable (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul h.1 (ae_lt_top_nrm hp h)]
  simp only [Complex.real_smul, mul_comm]

private theorem integrable_iff (hp : Pair μ j ν) {F : G → ℂ} (hF : Measurable F)
    {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ) :
    Integrable (fun x => F x * ((ρ x).toReal : ℂ)) μ ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤ := by
  have hm := h.1
  have e : ∫⁻ x, ‖F x * ((ρ x).toReal : ℂ)‖ₑ ∂μ = ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_nrm hp h] with x hx
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((ρ x).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [← e, ← lt_top_iff_ne_top]
  exact ⟨fun h => h.2, fun h => ⟨Measurable.aestronglyMeasurable (by fun_prop), h⟩⟩

end

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.quotEq :
    UpperTheory.ConvolutionTheory.G.QuotEq := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hp F hF hi ρ h
  have h2 : QInt μ j ν F ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤ := by
    refine ⟨fun hq => (integrable_iff hp hF h).1 (hq.2.2 ρ h), fun hq => ⟨hF, hi, fun ρ' h' => ?_⟩⟩
    rw [integrable_iff hp hF h', lint_eq hp (Φ := fun x => ‖F x‖ₑ) hF.enorm (fun t g => by rw [hi]) h' h]
    exact hq
  refine ⟨h2.trans (integrable_iff hp hF h).symm, h2, ?_⟩
  have hex : ∃ ρ, IsNrm j ν ρ := ⟨ρ, h⟩
  rw [qI, dite_eq_left hex, int_eq hp hF hex.choose_spec, int_eq hp hF h, map_eq hp hF hi hex.choose_spec h]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

private theorem exists_bump {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] (H : Set G)
    (hH : IsClosed H) (h1 : (1 : G) ∈ H) (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) :
    ∃ f : G → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, ∃ h ∈ H, 0 < f (h * x)) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ ∀ g ∈ H * C, f g ≠ 0 → g ∈ D := by
  classical
  let L : CompactExhaustion G := (CompactExhaustion.choice G).shiftr
  have L0 : L 0 = ∅ := rfl
  let A : ℕ → Set G := fun n => H * L n
  let O : ℕ → Set G := fun n => H * interior (L n)
  have hA : ∀ n, IsClosed (A n) := fun n => hH.mul_right_of_isCompact (L.isCompact n)
  have hO : ∀ n, IsOpen (O n) := fun n => isOpen_interior.mul_left
  have hOA : ∀ n, O n ⊆ A n := fun n => mul_subset_mul_left interior_subset
  have hAO : ∀ n, A n ⊆ O (n + 1) := fun n => mul_subset_mul_left (L.subset_interior_succ n)
  have hAm : Monotone A := fun a b h => mul_subset_mul_left (L.subset h)
  have hA0 : A 0 = ∅ := by simp [A, L0]
  have hLA : ∀ n, (L n : Set G) ⊆ A n := fun n x hx => ⟨1, h1, x, hx, one_mul x⟩
  have hdisj : ∀ n, Disjoint ((L (n + 1) : Set G) \ O n) (A (n - 1)) := by
    intro n
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ hxA
    cases n with
    | zero => simp [hA0] at hxA
    | succ n => exact hx (hAO n hxA)
  have hex : ∀ n, ∃ φ : C(G, ℝ), EqOn φ 1 ((L (n + 1) : Set G) \ O n) ∧ EqOn φ 0 (A (n - 1)) ∧
      HasCompactSupport φ ∧ ∀ x, φ x ∈ Icc (0 : ℝ) 1 := fun n =>
    exists_continuous_one_zero_of_isCompact ((L.isCompact (n + 1)).diff (hO n)) (hA (n - 1))
      (hdisj n)
  choose φ hφ1 hφ0 hφc hφI using hex
  have hvan : ∀ n k x, k < n → x ∈ A k → φ n x = 0 := fun n k x hkn hx =>
    hφ0 n (hAm (Nat.le_sub_one_of_lt hkn) hx)
  have hlf : LocallyFinite fun n => Function.support (φ n) := by
    intro x
    obtain ⟨k, hk⟩ := L.exists_mem_nhds x
    refine ⟨_, hk, (Set.finite_Iic k).subset ?_⟩
    rintro n ⟨y, hy, hyk⟩
    by_contra hn
    exact hy (hvan n k y (not_le.mp hn) (hLA k hyk))
  refine ⟨fun x => ∑ᶠ n, φ n x, continuous_finsum (fun n => (φ n).continuous) hlf,
    fun x => finsum_nonneg fun n => (hφI n x).1, ?_, ?_⟩
  · intro x
    have hexA : ∃ m, x ∈ A m := by
      obtain ⟨k, hk⟩ := L.exists_mem_nhds x
      exact ⟨k, hLA k (mem_of_mem_nhds hk)⟩
    have hm0 : Nat.find hexA ≠ 0 := by
      intro h0
      have := Nat.find_spec hexA
      rw [h0, hA0] at this
      exact this
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hxn : x ∉ A n := Nat.find_min hexA (by omega)
    have hxs : x ∈ A (n + 1) := by
      have := Nat.find_spec hexA
      rwa [hn] at this
    obtain ⟨h, hh, y, hy, rfl⟩ := hxs
    have hyO : y ∉ O n := by
      intro hyO
      obtain ⟨h', hh', z, hz, rfl⟩ := hyO
      exact hxn (hOA n ⟨h * h', hmul _ hh _ hh', z, hz, by simp [mul_assoc]⟩)
    refine ⟨h⁻¹, hinv h hh, ?_⟩
    have hy1 : φ n y = 1 := hφ1 n ⟨hy, hyO⟩
    have hfin : (Function.support fun m => φ m y).Finite := hlf.point_finite y
    have hle := single_le_finsum (f := fun m => φ m y) n hfin (fun m => (hφI m y).1)
    simp only [inv_mul_cancel_left]
    have : (1 : ℝ) ≤ ∑ᶠ m, φ m y := by simpa [hy1] using hle
    linarith
  · intro C hC
    obtain ⟨k, hk⟩ := L.exists_superset_of_isCompact hC
    refine ⟨⋃ n ∈ Finset.range (k + 1), tsupport (φ n),
      (Finset.range (k + 1)).isCompact_biUnion fun n _ => hφc n, ?_⟩
    intro g hg hfg
    have hgA : g ∈ A k := mul_subset_mul_left hk hg
    obtain ⟨n, hn⟩ : ∃ n, φ n g ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hfg (by simp [hcon])
    have hnk : n ≤ k := by
      by_contra hnk
      exact hn (hvan n k g (not_le.mp hnk) hgA)
    exact mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
      (subset_tsupport _ hn)

private theorem exists_nrm {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [MeasurableSpace T] [BorelSpace T]
    (j : T →* G) (hj : IsClosedEmbedding j) (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] (f : G → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hpos : ∀ x, ∃ h ∈ Set.range j, 0 < f (h * x))
    (hsupp : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ g ∈ Set.range j * C, f g ≠ 0 → g ∈ D) :
    ∃ ρ : G → NNReal, Continuous ρ ∧ IsNrm j ν (fun g => ρ g) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
        ∀ g ∈ Set.range j * C, ρ g ≠ 0 → g ∈ D := by
  have hcont2 : Continuous fun p : G × T => f (j p.2 * p.1) :=
    hf.comp ((hj.continuous.comp continuous_snd).mul continuous_fst)
  have hk : ∀ N : Set G, IsCompact N → ∃ k : Set T, IsCompact k ∧
      ∀ x ∈ N, ∀ t, t ∉ k → f (j t * x) = 0 := by
    intro N hN
    obtain ⟨D, hD, hDs⟩ := hsupp N hN
    refine ⟨j ⁻¹' (D * N⁻¹), hj.isCompact_preimage (hD.mul hN.inv), ?_⟩
    intro x hx t ht
    by_contra hne
    apply ht
    have hmem := hDs (j t * x) ⟨j t, mem_range_self t, x, hx, rfl⟩ hne
    exact ⟨j t * x, hmem, x⁻¹, Set.inv_mem_inv.mpr hx, by simp⟩
  have hcs : ∀ x, HasCompactSupport fun t => f (j t * x) := by
    intro x
    obtain ⟨k, hkc, hks⟩ := hk {x} isCompact_singleton
    exact HasCompactSupport.intro hkc fun t ht => hks x rfl t ht
  have hc1 : ∀ x, Continuous fun t => f (j t * x) := fun x =>
    hcont2.comp (Continuous.prodMk continuous_const continuous_id)
  have hint : ∀ x, Integrable (fun t => f (j t * x)) ν := fun x =>
    (hc1 x).integrable_of_hasCompactSupport (hcs x)
  let I : G → ℝ := fun x => ∫ t, f (j t * x) ∂ν
  have hIc : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨N, hNc, hNx⟩ := exists_compact_mem_nhds x
    obtain ⟨k, hkc, hks⟩ := hk N hNc
    have : ContinuousOn I N :=
      continuousOn_integral_of_compact_support (f := fun x t => f (j t * x)) hkc
        hcont2.continuousOn fun p t hp ht => hks p hp t ht
    exact this.continuousAt hNx
  have hIpos : ∀ x, 0 < I x := by
    intro x
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hpos x
    exact (hc1 x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun s => hf0 _) ht.ne'
  have hIinv : ∀ s x, I (j s * x) = I x := by
    intro s x
    have := integral_mul_right_eq_self (μ := ν) (fun t => f (j t * x)) s
    simpa [I, mul_assoc] using this
  refine ⟨fun g => Real.toNNReal (f g / I g),
    continuous_real_toNNReal.comp (hf.div hIc fun x => (hIpos x).ne'), ⟨?_, ?_⟩, ?_⟩
  · exact measurable_coe_nnreal_ennreal.comp
      (continuous_real_toNNReal.comp (hf.div hIc fun x => (hIpos x).ne')).measurable
  · intro x
    have hrw : ∀ t, ((Real.toNNReal (f (j t * x) / I (j t * x)) : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal (f (j t * x) / I x) := fun t => by rw [hIinv]; rfl
    simp_rw [hrw]
    rw [← ofReal_integral_eq_lintegral_ofReal ((hint x).div_const _)
      (Filter.Eventually.of_forall fun t => div_nonneg (hf0 _) (hIpos x).le), integral_div]
    rw [div_self (hIpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨D, hD, hDs⟩ := hsupp C hC
    refine ⟨D, hD, fun g hg hne => hDs g hg ?_⟩
    intro h0
    apply hne
    simp [h0]

theorem normEx : NormEx := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hp
  obtain ⟨-, hj, hν⟩ := hp
  haveI := hν.1
  haveI := hν.2
  haveI : ν.IsMulRightInvariant := by
    have h : ν.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  obtain ⟨f, hf, hf0, hpos, hsupp⟩ := exists_bump (Set.range j) hj.isClosed_range
    ⟨1, map_one j⟩ (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul j a b⟩)
    (by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv j a⟩)
  exact exists_nrm j hj ν f hf hf0 hpos hsupp

end UpperTheory.ConvolutionTheory.G
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotProd
open MeasureTheory Topology
open scoped ENNReal

private theorem UpperTheory.ConvolutionTheory.G.uni_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [LocallyCompactSpace G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G']
    {μ : Measure G} {μ' : Measure G'} (h : UpperTheory.ConvolutionTheory.G.Uni μ) (h' : UpperTheory.ConvolutionTheory.G.Uni μ') :
    UpperTheory.ConvolutionTheory.G.Uni (μ.prod μ') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨inferInstance, ⟨?_⟩⟩
  have e : (Inv.inv : G × G' → G × G') = Prod.map Inv.inv Inv.inv := rfl
  rw [Measure.inv_def, e, ← Measure.map_prod_map _ _ measurable_inv measurable_inv,
    Measure.map_inv_eq_self, Measure.map_inv_eq_self]

theorem UpperTheory.ConvolutionTheory.G.quotProd_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotProd := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP'
  have hPP : UpperTheory.ConvolutionTheory.G.Pair (μ.prod μ') (j.prodMap j') (ν.prod ν') :=
    ⟨UpperTheory.ConvolutionTheory.G.uni_prod hP.1 hP'.1, hP.2.1.prodMap hP'.2.1, UpperTheory.ConvolutionTheory.G.uni_prod hP.2.2 hP'.2.2⟩
  refine ⟨hPP, fun F F' hF hFi hF' hFi' => ?_⟩
  obtain ⟨ρ, hc, hρ, -⟩ := hN G T μ j ν hP
  obtain ⟨ρ', hc', hρ', -⟩ := hN G' T' μ' j' ν' hP'
  haveI := hP.1.1
  haveI := hP'.1.1
  haveI := hP.2.2.1
  haveI := hP'.2.2.1
  have hj : Measurable j := hP.2.1.continuous.measurable
  have hj' : Measurable j' := hP'.2.1.continuous.measurable
  have hρρ : UpperTheory.ConvolutionTheory.G.IsNrm (j.prodMap j') (ν.prod ν')
      (fun g : G × G' => (ρ g.1 : ℝ≥0∞) * (ρ' g.2 : ℝ≥0∞)) := by
    refine ⟨(hρ.1.comp measurable_fst).mul (hρ'.1.comp measurable_snd), fun x => ?_⟩
    have := lintegral_prod_mul (μ := ν) (ν := ν') (f := fun t => (ρ (j t * x.1) : ℝ≥0∞))
      (g := fun t => (ρ' (j' t * x.2) : ℝ≥0∞))
      (hρ.1.comp (hj.mul_const _)).aemeasurable (hρ'.1.comp (hj'.mul_const _)).aemeasurable
    rw [hρ.2 x.1, hρ'.2 x.2, mul_one] at this
    exact this
  have hm : Measurable (fun g : G × G' => F g.1 * F' g.2) :=
    (hF.comp measurable_fst).mul (hF'.comp measurable_snd)
  have hi : ∀ (t : T × T') (g : G × G'),
      (fun g : G × G' => F g.1 * F' g.2) (j.prodMap j' t * g) = (fun g : G × G' => F g.1 * F' g.2) g := by
    intro t g
    show F (j t.1 * g.1) * F' (j' t.2 * g.2) = _
    rw [hFi, hFi']
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP F hF hFi _ hρ
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F' hF' hFi' _ hρ'
  obtain ⟨c1, -, c3⟩ := hE (G × G') (T × T') _ _ _ hPP _ hm hi _ hρρ
  have key : (fun x : G × G' => F x.1 * F' x.2 * ((((ρ x.1 : ℝ≥0∞) * (ρ' x.2 : ℝ≥0∞)).toReal : ℝ) : ℂ)) =
      fun x : G × G' => (F x.1 * (((ρ x.1 : ℝ≥0∞).toReal : ℝ) : ℂ)) * (F' x.2 * (((ρ' x.2 : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    rw [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  refine ⟨fun h h' => ?_, ?_⟩
  · rw [c1, key]
    exact (a1.1 h).mul_prod (b1.1 h')
  · rw [c3, key, a3, b3]
    exact integral_prod_mul (fun x => F x * (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ))
      (fun x => F' x * (((ρ' x : ℝ≥0∞).toReal : ℝ) : ℂ))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotLin
open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section

variable {G T : Type} [Group G] [MeasurableSpace G] [Group T] [MeasurableSpace T]

private theorem smul_coe (a : NNReal) (μ : Measure G) : a • μ = (a : ℝ≥0∞) • μ := rfl

private theorem uni_smul [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G}
    (h : Uni μ) {a : NNReal} (ha : a ≠ 0) : Uni (a • μ) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨Measure.IsHaarMeasure.nnreal_smul μ ha,
    ⟨by
      rw [Measure.inv, Measure.map_smul, Measure.map_inv_eq_self]
      exact continuous_inv.measurable.aemeasurable⟩⟩

private theorem isNrm_div {j : T →* G} {ν : Measure T} {ρ : G → ℝ≥0∞} (h : IsNrm j ν ρ)
    {b : NNReal} (hb : b ≠ 0) : IsNrm j (b • ν) (fun x => (b : ℝ≥0∞)⁻¹ * ρ x) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by simpa using hb
  refine ⟨h.1.const_mul _, fun x => ?_⟩
  rw [smul_coe, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hb0), h.2 x,
    mul_one, smul_eq_mul, ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top]

private theorem isNrm_mul {j : T →* G} {ν : Measure T} {ρ : G → ℝ≥0∞} {b : NNReal}
    (h : IsNrm j (b • ν) ρ) : IsNrm j ν (fun x => (b : ℝ≥0∞) * ρ x) := by
  refine ⟨h.1.const_mul _, fun x => ?_⟩
  have := h.2 x
  rw [smul_coe, lintegral_smul_measure, smul_eq_mul] at this
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, this]

private theorem mul_toReal (z : ℂ) (b : NNReal) (r : ℝ≥0∞) :
    z * ((((b : ℝ≥0∞)⁻¹ * r).toReal : ℝ) : ℂ) = (((b : ℝ) : ℂ))⁻¹ * (z * ((r.toReal : ℝ) : ℂ)) := by
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]
  push_cast
  ring

private theorem int_iff {μ : Measure G} {F : G → ℂ} {ρ : G → ℝ≥0∞} {a b : NNReal} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Integrable (fun x => F x * ((((b : ℝ≥0∞)⁻¹ * ρ x).toReal : ℝ) : ℂ)) (a • μ) ↔
      Integrable (fun x => F x * (((ρ x).toReal : ℝ) : ℂ)) μ := by
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by simpa using ha
  have hc : ((b : ℝ) : ℂ) ≠ 0 := by simpa using hb
  rw [smul_coe, integrable_smul_measure ha0 ENNReal.coe_ne_top]
  simp only [mul_toReal]
  constructor
  · intro h
    have := h.const_mul (((b : ℝ) : ℂ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    exact mul_inv_cancel_left₀ hc _
  · exact fun h => h.const_mul _

private theorem qInt_iff {μ : Measure G} {j : T →* G} {ν : Measure T} {F : G → ℂ} {a b : NNReal}
    (ha : a ≠ 0) (hb : b ≠ 0) : QInt (a • μ) j (b • ν) F ↔ QInt μ j ν F := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by simpa using hb
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun ρ hρ => (int_iff ha hb).1 (h3 _ (isNrm_div hρ hb))⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun ρ hρ => ?_⟩
    have := (int_iff (μ := μ) (ρ := fun x => (b : ℝ≥0∞) * ρ x) (F := F) ha hb).2 (h3 _ (isNrm_mul hρ))
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hb0 ENNReal.coe_ne_top, one_mul] using this

end

end UpperTheory.ConvolutionTheory.G

open UpperTheory.ConvolutionTheory.G in
theorem UpperTheory.ConvolutionTheory.G.quotLin_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotLin := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP
  obtain ⟨ρ₀, -, hρ₀, -⟩ := hN G T μ j ν hP
  refine ⟨fun ι s c F hF => ?_, fun a b ha hb => ?_⟩
  · have hsum : QInt μ j ν (fun g => ∑ i ∈ s, c i * F i g) := by
      refine ⟨Finset.measurable_sum s fun i hi => measurable_const.mul (hF i hi).1,
        fun t g => Finset.sum_congr rfl fun i hi => by rw [(hF i hi).2.1], fun ρ hρ => ?_⟩
      have := integrable_finsetSum s (fun i hi => ((hF i hi).2.2 ρ hρ).const_mul (c i))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Finset.sum_mul, mul_assoc]
    refine ⟨hsum, ?_⟩
    rw [(hE G T μ j ν hP _ hsum.1 hsum.2.1 _ hρ₀).2.2,
      Finset.sum_congr rfl fun i hi => by
        rw [(hE G T μ j ν hP _ (hF i hi).1 (hF i hi).2.1 _ hρ₀).2.2]]
    simp only [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum s fun i hi => ((hF i hi).2.2 _ hρ₀).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · have hP' : Pair (a • μ) j (b • ν) := ⟨uni_smul hP.1 ha, hP.2.1, uni_smul hP.2.2 hb⟩
    refine ⟨hP', fun F hF hinv => ⟨qInt_iff ha hb, ?_⟩⟩
    have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using hb
    rw [(hE G T _ _ _ hP' F hF hinv _ (isNrm_div hρ₀ hb)).2.2, (hE G T μ j ν hP F hF hinv _ hρ₀).2.2,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    simp only [mul_toReal]
    rw [integral_const_mul]
    push_cast
    field_simp
end
