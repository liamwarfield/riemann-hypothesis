module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
public import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInOf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def nfE (D : D7) : ℕ := Fintype.card (InfinitePlace D.host.E)

def plE (D : D7) : Fin (nfE D) ≃ InfinitePlace D.host.E := (Fintype.equivFin _).symm

def tauE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Fin (nfE D) ≃ InfinitePlace X.B.I.F :=
  (plE D).trans (e.trans X.pl.symm)

def embE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) : D.host.E →+* ℂ :=
  (X.B.I.φ (tauE X e j)).comp X.ιE.symm.toRingHom

def PlaceTie (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Prop :=
  ∀ x : InfinitePlace D.host.E, InfinitePlace.mk ((X.B.I.φ (X.pl.symm (e x))).comp X.ιE.symm.toRingHom) = x

theorem hembE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (h : PlaceTie X e) (j : Fin (nfE D)) :
    InfinitePlace.mk (embE X e j) = plE D j := h (plE D j)

def castLoc (u : D.what₂.Word) {v w : InfinitePlace X.B.I.F} (h : v = w) : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u w := by
  subst h; exact LinearIsometryEquiv.refl ℂ _

theorem tauE_symm (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (v : InfinitePlace X.B.I.F) :
    X.pl.symm (e (plE D ((tauE X e).symm v))) = v := by
  simp [tauE]

def carrierInOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) :
    CarrierIn X u u' where
  Wp := fun x => X.Vloc u (X.pl.symm (e x))
  Wq := fun x => X.Vloc u' (X.pl.symm (e x))
  nf := nfE D
  pl := plE D
  emb := embE X e
  hemb := hembE X e he
  G := Formalism.L2.SG.SpectralTiesReal.gOf D e
  CA := CA
  de := de
  de' := de'
  l := l
  grid := grid
  grid1 := grid1
  hv := hv
  T := T
  hT := hT
  fc := fc
  χ := χ
  sg := sg
  ν' := ν'
  m₀ := m₀
  top := top
  A₀ := A₀
  τ := tauE X e
  Q := fun v => Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  Qi := fun v => Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  eP := fun v => castLoc X u (tauE_symm X e v)
  eQ := fun v => castLoc X u' (tauE_symm X e v)

end Formalism.L2.SG.Pf.Carrier
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KerSideCut
noncomputable section

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.ProjRows Formalism.L2.SG.KerJoinS Formalism.IndefR.Cx Formalism.L2.Indef

namespace Formalism.L2.SG.KerSideCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Chain

theorem chainOpM_add' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (f g : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (f + g) = Formalism.ThetaLiftIndependence.chainOpM w Km m f + Formalism.ThetaLiftIndependence.chainOpM w Km m g := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.sum_add_distrib, smul_add, map_add (f := _)]

theorem chainOpM_smul' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.smul_sum, map_smul, smul_smul, mul_comm]

def colL {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) :
    (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls R.m → C.Y R.m → ℂ) where
  toFun := C.col
  map_add' f g := chainOpM_add' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m f g
  map_smul' c f := chainOpM_smul' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m c f

def perColL (D : D7) (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] D.what₂.Amb D.what₂.mu0 →ₗ[ℂ] ℂ :=
  ((D.mem u).P.period ∘ₗ (D.mem u).P.lowerMap ∘ₗ (D.mem u).P.evz ∘ₗ colL (D.mem u).C ∘ₗ
    (D.mem u).A.Mram.subtype ∘ₗ (D.eMu u).toLinearMap).compl₂ (D.eMt u).symm.toLinearMap

theorem perColL_apply (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F : D.what₂.Amb D.what₂.mu0) :
    perColL D u φ F = D.what₂.perCol u D.what₂.mu0 φ F := by
  rw [D.perCol_base_eq_PtilCol]
  simp only [perColL, LinearMap.compl₂_apply, LinearMap.comp_apply, PeriodMap.PtilCol, PeriodMap.Ptil]
  rfl

end Chain

section Read

variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₗ[ℂ] P.EE)

def GoodPartHasComplexCoordinates : Prop := D.what₂.V0 D.what₂.mu0 ≤ LinearMap.range cF

end Read

end Formalism.L2.SG.KerSideCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CovolIdx
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Formalism.L2.SG.Pf.CovolIdx

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem fd_sub (μ : Measure G) (R : Set G) (hR : μ Rᶜ = 0) (A B : Subgroup G) [Countable A]
    (hinv : ∀ s ∈ A, μ.map (fun x => s * x) = μ) (hAR : ∀ s ∈ A, ∀ r ∈ R, s * r ∈ R)
    (KA : Set G) (hKA : MeasurableSet KA) (hKAu : ∀ r ∈ R, ∃! s, s ∈ A ∧ s * r ∈ KA)
    (hfin : B.relIndex A ≠ 0) :
    ∃ KC : Set G, MeasurableSet KC ∧ (∀ r ∈ R, ∃! s, s ∈ A ⊓ B ∧ s * r ∈ KC) ∧
      μ KC = (B.relIndex A : ℝ≥0∞) * μ KA := by
  classical
  haveI : Finite (A ⧸ B.subgroupOf A) :=
    Nat.finite_of_card_ne_zero (by rw [← Subgroup.index_eq_card]; exact hfin)
  letI : Fintype (A ⧸ B.subgroupOf A) := Fintype.ofFinite _
  have hmk : ∀ q : A ⧸ B.subgroupOf A, ((Quotient.out q : A) : A ⧸ B.subgroupOf A) = q :=
    fun q => QuotientGroup.out_eq' q
  refine ⟨⋃ q : A ⧸ B.subgroupOf A, (fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA,
    MeasurableSet.iUnion fun q => measurable_const_mul _ hKA, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, ⟨ha, har⟩, hau⟩ := hKAu r hr
    obtain ⟨q, hq⟩ : ∃ q : A ⧸ B.subgroupOf A, q = ((⟨a, ha⟩ : A) : A ⧸ B.subgroupOf A) := ⟨_, rfl⟩
    have hqB : ((Quotient.out q : A) : G)⁻¹ * a ∈ B := by
      have h1 := QuotientGroup.eq.mp ((hmk q).trans hq)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    refine ⟨((Quotient.out q : A) : G)⁻¹ * a, ⟨⟨A.mul_mem (A.inv_mem (Quotient.out q).2) ha, hqB⟩, ?_⟩, ?_⟩
    · refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      show ((Quotient.out q : A) : G) * (((Quotient.out q : A) : G)⁻¹ * a * r) ∈ KA
      rw [mul_assoc, mul_inv_cancel_left]
      exact har
    · rintro s' ⟨⟨hs'A, hs'B⟩, hs'K⟩
      obtain ⟨q', hq'⟩ := Set.mem_iUnion.mp hs'K
      have hq'' : ((Quotient.out q' : A) : G) * s' * r ∈ KA := by
        rw [mul_assoc]
        exact hq'
      have e1 : ((Quotient.out q' : A) : G) * s' = a :=
        hau _ ⟨A.mul_mem (Quotient.out q').2 hs'A, hq''⟩
      have e2 : q' = q := by
        rw [hq, ← hmk q']
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        have e3 : ((((Quotient.out q' : A))⁻¹ * ⟨a, ha⟩ : A) : G) = s' :=
          (eq_inv_mul_of_mul_eq e1).symm
        rw [e3]
        exact hs'B
      subst e2
      exact eq_inv_mul_of_mul_eq e1
  · have hdisj : Pairwise (fun q q' : A ⧸ B.subgroupOf A =>
        AEDisjoint μ ((fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA)
          ((fun x => ((Quotient.out q' : A) : G) * x) ⁻¹' KA)) := by
      intro q q' hne
      show μ (_ ∩ _) = 0
      refine measure_mono_null (?_ : _ ⊆ Rᶜ) hR
      intro x hx hxR
      apply hne
      have e := (hKAu x hxR).unique ⟨(Quotient.out q).2, hx.1⟩ ⟨(Quotient.out q').2, hx.2⟩
      have e' := congrArg (fun z : A => (z : A ⧸ B.subgroupOf A)) (Subtype.ext e : Quotient.out q = Quotient.out q')
      simp only [hmk] at e'
      exact e'
    have hmeas : ∀ q : A ⧸ B.subgroupOf A,
        μ ((fun x => ((Quotient.out q : A) : G) * x) ⁻¹' KA) = μ KA := by
      intro q
      rw [← Measure.map_apply (measurable_const_mul _) hKA, hinv _ (Quotient.out q).2]
    rw [measure_iUnion₀ hdisj (fun q => (measurable_const_mul _ hKA).nullMeasurableSet), tsum_fintype]
    simp only [hmeas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem covol_commens (μ : Measure G) (R : Set G) (hR : μ Rᶜ = 0) (A B : Subgroup G) [Countable A] [Countable B]
    (hinvA : ∀ s ∈ A, μ.map (fun x => s * x) = μ) (hinvB : ∀ s ∈ B, μ.map (fun x => s * x) = μ)
    (hAR : ∀ s ∈ A, ∀ r ∈ R, s * r ∈ R) (hBR : ∀ s ∈ B, ∀ r ∈ R, s * r ∈ R)
    (KA KB : Set G) (hKA : MeasurableSet KA) (hKB : MeasurableSet KB)
    (hKAu : ∀ r ∈ R, ∃! s, s ∈ A ∧ s * r ∈ KA) (hKBu : ∀ r ∈ R, ∃! s, s ∈ B ∧ s * r ∈ KB)
    (hfinA : B.relIndex A ≠ 0) (hfinB : A.relIndex B ≠ 0) :
    μ KA * (B.relIndex A : ℝ≥0∞) = μ KB * (A.relIndex B : ℝ≥0∞) := by
  classical
  obtain ⟨K1, hK1m, hK1u, hK1μ⟩ := fd_sub μ R hR A B hinvA hAR KA hKA hKAu hfinA
  obtain ⟨K2, hK2m, hK2u, hK2μ⟩ := fd_sub μ R hR B A hinvB hBR KB hKB hKBu hfinB
  rw [inf_comm] at hK2u
  haveI : Countable ↥(A ⊓ B) :=
    Function.Injective.countable (Subgroup.inclusion_injective (inf_le_left : A ⊓ B ≤ A))
  letI : MeasurableSpace ↥(A ⊓ B) := ⊤
  haveI : MeasurableSMul ↥(A ⊓ B) G :=
    { measurable_const_smul := fun c => measurable_const_mul (c : G)
      measurable_smul_const := fun _ => measurable_from_top }
  haveI : SMulInvariantMeasure ↥(A ⊓ B) G μ := ⟨fun c s hs => by
    show μ ((fun x => (c : G) * x) ⁻¹' s) = μ s
    rw [← Measure.map_apply (measurable_const_mul _) hs, hinvA _ c.2.1]⟩
  have hRa : ∀ᵐ x ∂μ, x ∈ R := ae_iff.mpr hR
  have mkfd : ∀ K : Set G, MeasurableSet K → (∀ r ∈ R, ∃! s, s ∈ A ⊓ B ∧ s * r ∈ K) →
      IsFundamentalDomain ↥(A ⊓ B) K μ := by
    intro K hK hu
    refine ⟨hK.nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hRa] with x hx
      obtain ⟨s, ⟨hs, hsK⟩, -⟩ := hu x hx
      exact ⟨⟨s, hs⟩, hsK⟩
    · intro g h hgh
      show μ (((fun x => g • x) '' K) ∩ ((fun x => h • x) '' K)) = 0
      refine measure_mono_null (?_ : _ ⊆ Rᶜ) hR
      intro y hy hyR
      apply hgh
      obtain ⟨x1, hx1, e1⟩ := hy.1
      obtain ⟨x2, hx2, e2⟩ := hy.2
      have k1 : (g : G)⁻¹ * y ∈ K := by
        rw [← e1]
        show (g : G)⁻¹ * ((g : G) * x1) ∈ K
        rw [inv_mul_cancel_left]
        exact hx1
      have k2 : (h : G)⁻¹ * y ∈ K := by
        rw [← e2]
        show (h : G)⁻¹ * ((h : G) * x2) ∈ K
        rw [inv_mul_cancel_left]
        exact hx2
      have e := (hu y hyR).unique ⟨(A ⊓ B).inv_mem g.2, k1⟩ ⟨(A ⊓ B).inv_mem h.2, k2⟩
      exact Subtype.ext (inv_injective e)
  have key : μ K1 = μ K2 := (mkfd K1 hK1m hK1u).measure_eq (mkfd K2 hK2m hK2u)
  rw [mul_comm, ← hK1μ, key, hK2μ, mul_comm]

end Formalism.L2.SG.Pf.CovolIdx
end
end
