module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.HarmLattice

theorem fg_span_comap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (O : Subring ℂ)
    (H : Submodule ℂ V) (f : V →ₗ[ℂ] W) (hinj : ∀ P ∈ H, f P = 0 → P = 0) (L : Submodule O W) (hfg : L.FG)
    (hsp : Submodule.span ℂ (L : Set W) = H.map f) :
    (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).FG ∧
      Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = H := by
  have him : f '' ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have : y ∈ H.map f := hsp ▸ Submodule.subset_span hy
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  constructor
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (f.restrictScalars O) ?_ ?_
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).map (f.restrictScalars O) = L :=
        SetLike.coe_injective him
      rw [this]
      exact hfg
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)) ⊓ LinearMap.ker (f.restrictScalars O) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hinj x hx.1.1 hx.2
      rw [this]
      exact Submodule.fg_bot
  · have hle : Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) ≤ H :=
      Submodule.span_le.2 fun x hx => hx.1
    refine le_antisymm hle fun x hx => ?_
    have : f x ∈ (Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V)).map f := by
      rw [Submodule.map_span, him, hsp]
      exact Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, e⟩ := this
    have h0 : x - y = 0 := hinj _ (sub_mem hx (hle hy)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero.1 h0]
    exact hy

variable {D : D7} {n : ℕ}

def cf (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)
  map_add' F G := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add (f := _), Pi.add_apply, mul_add]
  map_smul' c F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

theorem coefFn_eq {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : VV K lam) :
    coefFn σ lam (F : Pol K D.what₂.Tau n) = cf lam (GlobalTheory.CoefModel.mapVV σ lam F) := by
  funext x
  change _ = coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F.1) x
  simp only [coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

private theorem nabAtr_full (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    Submodule.IsFullLattice K (nabAtr emb lam M) := by
  classical
  refine nb_lattice (nb_comm_nab lam) _ fun τ => ?_
  obtain ⟨m, x, ξ, hx, hξ, h⟩ := GlobalTheory.TauLat.exists_dual_family M hM
  let e (z : Fin n → D.host.E) (a : Fin n) : K := emb τ (z a)
  have hx' (i : Fin m) : e (x i) ∈ tauLat emb τ M :=
    Submodule.subset_span ⟨x i, hx i, rfl⟩
  have hξ' (i : Fin m) : e (ξ i) ∈ dualFr (tauLat emb τ M) := by
    intro y hy
    change y ∈ Submodule.span (𝓞 K) (e '' (M : Set (Fin n → D.host.E))) at hy
    induction hy using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      change (fun a => emb τ (ξ i a)) ⬝ᵥ (fun a => emb τ (z a)) ∈ _
      rw [← GlobalTheory.TauLat.map_dot]
      exact du_map_mem_one _ ((GlobalTheory.TauLat.mem_one_iff _).2 (hξ i z hz))
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add _ _ _ _ hy hz => rw [dotProduct_add]; exact add_mem hy hz
    | smul c _ _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ c hy
  have hexpand (y : Fin n → K) :
      y = ∑ i, (y ⬝ᵥ e (x i)) • e (ξ i) := by
    simpa only [dotProduct_comm y, e] using GlobalTheory.TauLat.expand_left (emb τ) h y
  refine { toIsLattice := Submodule.IsLattice.of_fg K ?_, span_eq_top := ?_ }
  · refine ⟨Finset.univ.image (fun i => e (ξ i)), le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Submodule.span_le, Set.range_subset_iff]
      exact hξ'
    · intro y hy
      rw [hexpand y]
      exact Submodule.sum_mem _ fun i _ =>
        du_smul_of_mem_one _ (hy _ (hx' i)) (Submodule.subset_span (by simp))
  · rw [eq_top_iff]
    intro y _
    rw [hexpand y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hξ' i))

theorem coefLatFn_fg (hc : IsCoefRing σ emb O) (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    (coefLatFn σ emb O lam M).FG := by
  obtain ⟨s, hs, e⟩ := Submodule.fg_def.1 (nabAtr_full (emb := emb) lam hM).fg
  refine Submodule.fg_def.2 ⟨(fun F => cf lam (GlobalTheory.CoefModel.mapVV σ lam F)) '' s, hs.image _, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, e ▸ Submodule.subset_span hF, (coefFn_eq σ lam F).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    rw [coefFn_eq, SetLike.mem_coe]
    rw [← e] at hF
    induction hF using Submodule.span_induction with
    | mem F h => exact Submodule.subset_span ⟨F, h, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hc.int a⟩ : O) h1

theorem span_coefLatFn (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    Submodule.span ℂ (coefLatFn σ emb O lam M : Set (GLR D n → ℂ)) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ lam, φ = coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)} := by
  rw [coefLatFn, Submodule.span_span_of_tower]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨F, -, rfl⟩
    exact ⟨_, coefFn_eq σ lam F⟩
  · rintro _ ⟨F, rfl⟩
    have key : ∀ G : VV K lam, cf lam (GlobalTheory.CoefModel.mapVV σ lam G) ∈
        Submodule.span ℂ {φ | ∃ F ∈ nabAtr emb lam M, φ = coefFn σ lam (F : VV K lam)} := by
      intro G
      have hG : G ∈ Submodule.span K (nabAtr emb lam M : Set (VV K lam)) := by
        rw [(nabAtr_full (emb := emb) lam hM).span_eq_top]
        exact Submodule.mem_top
      induction hG using Submodule.span_induction with
      | mem F h => exact Submodule.subset_span ⟨F, h, (coefFn_eq σ lam F).symm⟩
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
      | smul a F _ h1 =>
        rw [LinearMap.map_smulₛₗ, map_smul]
        exact Submodule.smul_mem _ _ h1
    have hF : F ∈ Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.mapVV σ lam (bVV K lam i)) := by
      rw [GlobalTheory.CoefModel.span_mapVV]; trivial
    change cf lam F ∈ _
    have := Submodule.mem_map_of_mem (f := cf lam) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact key _

theorem harmLat_fg_span : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsFullLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  exact fg_span_comap O (harm m w B) (harmFn m w B) (GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D m n w B hw hm) _ (coefLatFn_fg hc w.lam hM)
    ((span_coefLatFn w.lam hM).trans (GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D m n w B hw hm).symm)

end GlobalTheory.ExportSeries.HarmLattice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsFullLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  letI := hM
  exact GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D m n w B K σ emb O M hw hm hc
    (by infer_instance)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExportSeries.TupleChars

variable {D : D7}

open GlobalTheory.StepLaw (ResAt UnrOff)

theorem idemSum_mul_idemAt {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) : (idem Q + cA D (idem Q)) * idemAt PP = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_eq_zero fun i hi => h.mul_eq_zero (hQ hi) hPP (by rintro rfl; exact hn hi),
    Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact h.mul_conj hPP (hQ hi), add_zero]

theorem idemSum_mul_of_off {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) {e : AE D} (he : IsIdemAt e PP) {x : AE D} (hx : e * (x - 1) = x - 1) :
    (idem Q + cA D (idem Q)) * x = idem Q + cA D (idem Q) := by
  have k := idemSum_mul_idemAt h hQ hPP hn
  rw [idemAt_eq he] at k
  linear_combination (-(idem Q + cA D (idem Q))) * hx + (x - 1) * k

theorem resAt_of_isResAt {χ : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {c : (kP PP)ˣ →* Circle} (h : IsResAt χ PP c) :
    ResAt χ PP (Circle.toUnits.comp c) := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  rw [h x (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm]
  rfl

theorem resAt_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet P)
    (hQ : Q ⊆ P) {PP : Pl D.host.E} (hPP : PP ∈ P) (hn : PP ∉ Q) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2 (idemSum_mul_of_off h hQ hPP hn he hx)]
  simp

theorem resAt_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (PP : Pl D.host.E) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2]
  simp

theorem resAt_twist {t : Twist D Circle} (ht : t.Good) {P : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : t.Q ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) : ResAt t.chi PP (t.locC PP) := by
  by_cases hq : PP ∈ t.Q
  · have e : t.locC PP = t.resC PP := by simp only [Twist.locC, if_pos hq]
    rw [e]
    exact resAt_of_isResAt (ht.res PP hq)
  · have e : t.locC PP = 1 := by simp only [Twist.locC, if_neg hq]
    rw [e]
    exact resAt_of_unram ht.unram h hQ hPP hq

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  simp [infPart, Algebra.TensorProduct.algebraMap_apply]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem infPart_eq_one {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x : AE D}
    (h : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  have k := congrArg (infPart D) h
  rw [map_mul, map_sub, map_one, infPart_placeIdem hε, zero_mul] at k
  linear_combination -k

theorem unrOff_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet Q)
    (hQ : Q ⊆ P) : UnrOff χ P := by
  intro v ε hε hv x h1 h2 h3
  refine hχ x (infPart_eq_one hε h1) h2 h3 ?_
  have k : (idem Q + cA D (idem Q)) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v', ε', hε', he⟩ := (h.isIdemAt hPP).1
    have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v' ε' (h.isIdemAt hPP) hε' he
    rw [he, ← map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε fun e => hv PP (hQ hPP) (hu.trans e), map_zero]
  linear_combination (-(idem Q + cA D (idem Q))) * h1 + ((x : AE D) - 1) * k

theorem unrOff_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (P : Finset (Pl D.host.E)) :
    UnrOff χ P := fun _ _ hε _ x h1 h2 h3 => hχ x (infPart_eq_one hε h1) h2 h3

theorem tuple_chars : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q →
    (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧
      GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧
    GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  intro D S T B hB ν hν hA
  classical
  obtain ⟨P, hPg, hQP, hP⟩ := hA.1.split
  have hsub : allP B ν.Q ⊆ P := Finset.union_subset hPg hQP
  have hdeP : B.de.Q ⊆ P := fun x hx => hQP (Finset.mem_union_left _ hx)
  have hνP : ν.Q ⊆ P := fun x hx => hQP (Finset.mem_union_right _ hx)
  have hη : UnramEverywhere D B.eta := hB.eta.2.1
  have key : ∀ PP ∈ allP B ν.Q, ResAt (B.mu * ν.chi) PP (resP B ν PP) := by
    intro PP hPP
    have hPPP := hsub hPP
    have hνr := resAt_twist hν hP hνP hPPP
    by_cases hg : PP ∈ B.G.Pg
    · have hde : PP ∉ B.de.Q := fun h => Finset.disjoint_left.1 hA.1.disj hg (Finset.mem_union_left _ h)
      have hdl : B.de.locC PP = 1 := by simp only [Twist.locC, if_neg hde]
      rw [resP, if_pos hg, hdl, mul_one]
      exact ResAt.mul (resAt_of_isResAt (hB.tame PP hg)) hνr
    · rw [resP, if_neg hg]
      exact ResAt.mul (ResAt.mul (resAt_of_unram hB.unram hP hPg hPPP hg) (resAt_twist hB.de hP hdeP hPPP)) hνr
  have u1 : UnrOff (B.mu * ν.chi) (allP B ν.Q) :=
    UnrOff.mul (UnrOff.mul (unrOff_of_unram hB.unram (hP.mono hPg) (by intro x hx; simp [allP, hx]))
      (unrOff_of_unram hB.de.unram hB.de.split (by intro x hx; simp [allP, hx])))
      (unrOff_of_unram hν.unram hν.split (by intro x hx; simp [allP, hx]))
  refine ⟨fun PP hPP => ⟨key PP hPP, ?_⟩, u1, u1.mul (unrOff_of_unramEverywhere hη _).inv⟩
  have := (key PP hPP).mul (resAt_of_unramEverywhere hη PP).inv
  rwa [inv_one, mul_one] at this

end GlobalTheory.ExportSeries.TupleChars

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualType_residueChars_unramified_tuple : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q → (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧ GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  first | exact @GlobalTheory.ExportSeries.TupleChars.tuple_chars | exact GlobalTheory.ExportSeries.TupleChars.tuple_chars | (intros; apply GlobalTheory.ExportSeries.TupleChars.tuple_chars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open Classical
namespace GlobalTheory.ExportSeries
open GlobalTheory.PlaceModel

variable {D : D7}

theorem isPlaceModel_restrictHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := GlobalTheory.T.isPlaceModel_comp_restrictToHalfLatticeIndicator ha hb hab hΛ hT

theorem toEAf_mem_intAf_of_idem {e : AE D} (he : e * e = e) : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.T.finiteAdeleCM_mem_integral_of_idempotent he

theorem isIntM_of_mem_lat_half {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    {x : WO S T} (hx : IsHalf (idem R) x) (hl : x ∈ F.lat) :
    IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) :=
  GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hR hx hl

theorem mem_lat_of_isIntM_half {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    {x : WO S T} (hx : IsHalf (idem R) x) (hi : IsIntM (frMapO S T F.βS F.βT x)) : x ∈ F.lat := GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hR hx hi

theorem redM_halfIdem_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Qa Qb : Finset (Pl D.host.E)} (hP : PlacesOK Pg Qa) (hQ : Qb ⊆ Qa) {x : WO S T}
    (hx : IsHalf (halfIdem Pg Qa) x) (h1 : IsIntM (frMapAdj S T βS βT x)) (h2 : IsIntM (frMapO S T βS βT x)) :
    (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧
    (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) :=
  GlobalTheory.T.frameMatrixReduction_eq_of_halfIdempotent_subset βS βT hP hQ hx h1 h2

end GlobalTheory.ExportSeries

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open Classical
namespace GlobalTheory.ExportSeries
open GlobalTheory.PlaceModel GlobalTheory.AdelicLatMove

variable {D : D7}

theorem halfIdem_eq_add {Pg Qa Qb : Finset (Pl D.host.E)} (hQ : Qb ⊆ Qa) :
    halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
  unfold halfIdem idem
  rw [← Finset.sum_sdiff hQ]
  ring

theorem PlacesOK.empty_sdiff {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa) : PlacesOK ∅ (Qa \ Qb) :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, Finset.sdiff_subset.trans hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (Finset.sdiff_subset (hPP.resolve_left (Finset.notMem_empty PP))))⟩

theorem idem_mul_self_of {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

theorem halfIdem_mul_idem {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa) (hQ : Qb ⊆ Qa) :
    halfIdem Pg Qb * idem (Qa \ Qb) = 0 := by
  have h1 := h.isOrthSum.1.idem
  have h2 := (h.mono hQ).isOrthSum.1.idem
  have h3 := idem_mul_self_of (h.empty_sdiff (Qb := Qb))
  rw [halfIdem_eq_add hQ] at h1
  refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
  push_cast
  linear_combination h1 - h2 - h3

theorem frMapO_add' {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((e • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D e) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isIntM_smul {b a : ℕ} {e : AE D} (he : e * e = e) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    IsIntM (toEAf D e • N) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem (toEAf_mem_intAf_of_idem he) (hN i j)

theorem isIntM_smul_cA {b a : ℕ} {e : AE D} (he : e * e = e) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    IsIntM (toEAf D (cA D e) • N) := isIntM_smul (by rw [← map_mul, he]) hN

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

theorem isInt_iff {S T : HSp D} {F : Frame S T} (hF : F.Good) {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa)
    (hQ : Qb ⊆ Qa) {x : WO S T} (hx : IsHalf (halfIdem Pg Qa) x) :
    (IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) ↔
      (IsIntM (frMapAdj S T F.βS F.βT (halfIdem Pg Qb • x)) ∧ IsIntM (frMapO S T F.βS F.βT (halfIdem Pg Qb • x)) ∧
        idem (Qa \ Qb) • x ∈ F.lat) := by
  have hR := h.empty_sdiff (Qb := Qb)
  have ha' := (h.mono hQ).isOrthSum.1.idem
  have hb := idem_mul_self_of hR
  have hxe : x = halfIdem Pg Qb • x + idem (Qa \ Qb) • x := by
    rw [← add_smul, ← halfIdem_eq_add hQ]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, mem_lat_of_isIntM_half hF hR (isHalf_smul hb x) ?_⟩
    · rw [frMapAdj_smul]; exact isIntM_smul_cA ha' h1
    · rw [frMapO_smul]; exact isIntM_smul ha' h2
    · rw [frMapO_smul]; exact isIntM_smul hb h2
  · rintro ⟨k1, k2, k3⟩
    obtain ⟨o, d⟩ := isIntM_of_mem_lat_half hF hR (isHalf_smul hb x) k3
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add']
    exact ⟨fun i j => add_mem (k1 i j) (d i j), fun i j => add_mem (k2 i j) (o i j)⟩

theorem datumFn_eq_restrict {S T : HSp D} {F : Frame S T} (hF : F.Good) {G : TypeDat D T.rank}
    {Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK G.Pg Qa) (hQ : Qb ⊆ Qa) {ω : Reds D T.rank S.rank → ℂ}
    (hω : ∀ y y', (∀ PP ∈ Qb, y PP = y' PP) → ω y = ω y') :
    F.datumFn G Qa ω = restrictHalf (halfIdem G.Pg Qb) (idem (Qa \ Qb)) F.lat (F.datumFn G Qb ω) := by
  funext x
  have ha' := (h.mono hQ).isOrthSum.1.idem
  have hb := idem_mul_self_of (h.empty_sdiff (Qb := Qb))
  rw [restrictHalf_apply, ← halfIdem_eq_add hQ]
  by_cases hx : IsHalf (halfIdem G.Pg Qa) x
  swap
  · rw [if_neg hx, mul_zero]
    simp only [Frame.datumFn]
    rw [if_neg fun h => hx h.1, zero_mul]
  rw [if_pos hx, mul_one]
  have ha'x := isHalf_smul ha' x
  have hbx := isHalf_smul hb x
  by_cases hint : IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)
  · obtain ⟨k1, k2, k3⟩ := (isInt_iff hF h hQ hx).1 hint
    obtain ⟨r1, r2⟩ := redM_halfIdem_smul F.βS F.βT h hQ hx hint.1 hint.2
    simp only [Frame.datumFn, halfInd]
    rw [if_pos ⟨hx, hint.1⟩, if_pos ⟨hx, hint.2⟩, if_pos ⟨ha'x, k1⟩, if_pos ⟨ha'x, k2⟩, if_pos ⟨k3, hbx⟩, mul_one]
    congr 1
    · exact GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP => r1 PP hPP
    · exact hω _ _ fun PP hPP => r2 PP hPP
  · have hL : F.datumFn G Qa ω x = 0 := by
      rcases not_and_or.1 hint with h1 | h1
      · simp [Frame.datumFn, h1]
      · simp [Frame.datumFn, h1]
    rw [hL]
    have hr := mt (isInt_iff hF h hQ hx).2 hint
    rcases not_and_or.1 hr with h1 | h1
    · simp [Frame.datumFn, h1]
    rcases not_and_or.1 h1 with h1 | h1
    · simp [Frame.datumFn, h1]
    · simp [halfInd, h1]

theorem vecAt_drop : ∀ (D : D7) (S T : HSp D) (B : Base S T) (Q Q' : Finset (Pl D.host.E)) [DecidablePred (· ∈ Q')]
    (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ), B.Good → B.admitted Q → Q' ⊆ Q →
    B.vecAt Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.vecAt Q' fun PP => φ PP.1 := by
  intro D S T B Q Q' _ φ hB hQ hQ'
  classical
  have hL : B.locFn Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.locFn Q' (fun PP => φ PP.1) := by
    funext y
    unfold Base.locFn
    congr 1
    beta_reduce
    rw [Finset.prod_coe_sort Q (fun P => if P ∈ Q' then φ P (y P) else 1),
      ← Finset.prod_subset hQ' (fun P _ hn => if_neg hn), Finset.prod_coe_sort Q' (fun P => φ P (y P))]
    exact Finset.prod_congr rfl fun P hP => if_pos hP
  have hQb : B.de.Q ∪ Q' ⊆ B.de.Q ∪ Q := Finset.union_subset_union (subset_refl _) hQ'
  have hω : ∀ y y' : Reds D T.rank S.rank, (∀ PP ∈ B.de.Q ∪ Q', y PP = y' PP) →
      B.locFn Q' (fun PP => φ PP.1) y = B.locFn Q' (fun PP => φ PP.1) y' := fun y y' hy => by
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  have hP := hQ.1
  have hPb := hP.mono hQb
  unfold Base.vecAt Frame.vec
  rw [hL, datumFn_eq_restrict hB.frame hP hQb hω]
  have hmodel := Frame.isPlaceModel_placeMap hB.frame hP
  rw [halfIdem_eq_add hQb] at hmodel ⊢
  have hm' := isPlaceModel_restrictHalf hPb.isOrthSum.1.idem (idem_mul_self_of (hP.empty_sdiff (Qb := B.de.Q ∪ Q')))
    (halfIdem_mul_idem hP hQb) (fun e he u hu => GlobalTheory.PlaceModelSum.idem_smul_latO he hu) hmodel
  exact GlobalTheory.PlaceVec.placeModel_unique hB.frame.vac.1 hB.frame.sdS hB.frame.sdT hPb.isOrthSum.1.idem
    hPb.isOrthSum.1.infPart_eq hm' (Frame.isPlaceModel_placeMap hB.frame hPb) (Frame.isSBHalf_datumFn hB.frame hPb hω)

end GlobalTheory.ExportSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumVector_drop_auxiliary_places : ∀ (D : D7) (S T : HSp D) (B : Base S T) (Q Q' : Finset (Pl D.host.E)) [DecidablePred (· ∈ Q')] (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ), B.Good → B.admitted Q → Q' ⊆ Q → B.vecAt Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.vecAt Q' fun PP => φ PP.1 := by
  first | exact @GlobalTheory.ExportSeries.vecAt_drop | exact GlobalTheory.ExportSeries.vecAt_drop | (intros; apply GlobalTheory.ExportSeries.vecAt_drop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitSep

open GlobalTheory.SplitScalar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_nsmul_left (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = k • symplO S T x y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, symplO_zero_left]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.LatVac.symplO_add_left, ih]

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [symplO_nsmul_left, symplO_skew S T (k • y) x, symplO_nsmul_left, symplO_skew S T x y, neg_nsmul, neg_neg]

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_sub_left S T 0 x y
  rwa [zero_sub, symplO_zero_left, zero_sub] at h

theorem nsmul_smul_comm (k : ℕ) (a : AE D) (v : WO S T) : k • (a • v) = a • (k • v) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

theorem isHalf_neg' {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := by
  rw [isHalf_iff] at *
  rw [smul_neg, hu]

theorem smul_eq_zero_of_half_conj {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf (cA D a) u) :
    a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, ha.2.1, zero_smul]

theorem conj_smul_eq_zero_of_half {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf a u) :
    cA D a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, mul_comm, ha.2.1, zero_smul]

theorem exists_nsmul_subgroup (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ K : AddSubgroup (WO S T), ∀ d, d ∈ K ↔ ∃ v ∈ Λ, d = k • v := by
  refine ⟨{ carrier := {d | ∃ v ∈ Λ, d = k • v}
            add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun d => Iff.rfl⟩
  · rintro u w ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
    exact ⟨v + v', add_mem hv hv', by rw [nsmul_add]⟩
  · exact ⟨0, zero_mem _, by rw [nsmul_zero]⟩
  · rintro u ⟨v, hv, rfl⟩
    exact ⟨-v, neg_mem hv, by rw [neg_nsmul]⟩

theorem exists_mixed_subgroup {a : AE D} (ha : IsSplitIdem D a) (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ Λ' : AddSubgroup (WO S T), (∀ u, IsHalf a u → (u ∈ Λ' ↔ ∃ v ∈ Λ, u = k • v)) ∧
      ∀ u, IsHalf (cA D a) u → (u ∈ Λ' ↔ k • u ∈ Λ) := by
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : AddSubgroup (WO S T),
      ∀ u, u ∈ Λ' ↔ (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ := by
    refine ⟨{ carrier := {u | (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ}
              add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun u => Iff.rfl⟩
    · rintro u w ⟨⟨v, hv, huv⟩, hu⟩ ⟨⟨v', hv', hwv⟩, hw⟩
      refine ⟨⟨v + v', add_mem hv hv', by rw [smul_add, huv, hwv, nsmul_add]⟩, ?_⟩
      rw [smul_add, nsmul_add]
      exact add_mem hu hw
    · refine ⟨⟨0, zero_mem _, by rw [smul_zero, nsmul_zero]⟩, ?_⟩
      rw [smul_zero, nsmul_zero]
      exact zero_mem _
    · rintro u ⟨⟨v, hv, huv⟩, hu⟩
      refine ⟨⟨-v, neg_mem hv, by rw [smul_neg, huv, neg_nsmul]⟩, ?_⟩
      rw [smul_neg, neg_nsmul]
      exact neg_mem hu
  refine ⟨Λ', fun u hu => ?_, fun u hu => ?_⟩
  · rw [hΛ', (isHalf_iff _ _).1 hu, conj_smul_eq_zero_of_half ha hu, nsmul_zero]
    exact ⟨fun h => h.1, fun h => ⟨h, zero_mem _⟩⟩
  · have h0 : a • u = 0 := smul_eq_zero_of_half_conj ha hu
    have h1 : cA D a • u = u := (isHalf_iff _ _).1 hu
    rw [hΛ']
    constructor
    · rintro ⟨-, h⟩
      rwa [h1] at h
    · intro h
      exact ⟨⟨0, zero_mem _, by rw [h0, nsmul_zero]⟩, by rwa [h1]⟩

theorem rep_half {e : AE D} (he : e * e = e) {Λ : AddSubgroup (WO S T)} (hstab : ∀ u ∈ Λ, e • u ∈ Λ) {k : ℕ}
    {d : WO S T} (hd : IsHalf e d) (h : ∃ v ∈ Λ, d = k • v) : ∃ v ∈ Λ, IsHalf e v ∧ d = k • v := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨e • v, hstab v hv, isHalf_smul he v, by rw [nsmul_smul_comm, ← h, (isHalf_iff _ _).1 hd]⟩

theorem sum_average {a : AE D} (ha : IsSplitIdem D a) {Λ : AddSubgroup (WO S T)} {k : ℕ} {f : WO S T → ℂ}
    (hfix : ∀ u ∈ Λ, IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y X : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hX : ∀ x ∈ X, IsHalf a x)
    (hXo : ∀ y, IsHalf (cA D a) y → k • y ∈ Λ →
      ((∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∀ x ∈ X, ψ (symplO S T y x) = 1) ∧
      ((¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∑ x ∈ X, ψ (symplO S T y x) = 0)) :
    ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = (X.card : ℂ) • f := by
  have e1 : ∀ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) =
      ∑ y ∈ Y, ψ (symplO S T y x) • heisO ψ S T y f := by
    intro x hx
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [heisO_comm, ← heisO_add_of_orth ψ S T (half_orth ha (isHalf_neg' (hX x hx)) (hX x hx)),
      neg_add_cancel, heisO_zero, symplO_neg_left, ← symplO_skew]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  obtain ⟨y₀, ⟨hy₀Y, u₀, hu₀, hu₀h, hy₀⟩, huniq⟩ :=
    hYu 0 (isHalf_zero _) (by rw [nsmul_zero]; exact zero_mem _)
  rw [Finset.sum_eq_single_of_mem y₀ hy₀Y]
  · have hy₀' : y₀ = k • (-u₀) := by rw [neg_nsmul, ← hy₀, zero_sub, neg_neg]
    have hyy : ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y₀ = k • u := ⟨-u₀, neg_mem hu₀, isHalf_neg' hu₀h, hy₀'⟩
    rw [Finset.sum_congr rfl ((hXo y₀ (hY y₀ hy₀Y).1 (hY y₀ hy₀Y).2).1 hyy), Finset.sum_const, nsmul_eq_mul,
      mul_one, hy₀', hfix _ (neg_mem hu₀) (isHalf_neg' hu₀h)]
  · intro y hy hne
    have hnot : ¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u := by
      rintro ⟨u, hu, huh, rfl⟩
      exact hne (huniq _ ⟨hy, -u, neg_mem hu, isHalf_neg' huh, by rw [zero_sub, neg_nsmul]⟩)
    rw [(hXo y (hY y hy).1 (hY y hy).2).2 hnot, zero_smul]

theorem sum_translates_eq_zero {a : AE D} (ha : IsSplitIdem D a) (hψ : IsStdChar D ψ (-1)) {Λ : AddSubgroup (WO S T)}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)
    (hstab : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ)
    {k : ℕ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ Λ, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0)
    {x : WO S T} (hxa : IsHalf a x) (hkx : k • x ∈ Λ) :
    ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := by
  have ha' := isSplitIdem_conj ha
  have hcc : cA D (cA D a) = a := GlobalTheory.DualPairCheck.cA_cA a
  obtain ⟨K, hK⟩ := exists_nsmul_subgroup Λ k
  obtain ⟨Λ', memA, memC⟩ := exists_mixed_subgroup ha Λ k
  have hYK : ∀ u', IsHalf (cA D a) u' → k • u' ∈ Λ → ∃! v, v ∈ Y ∧ u' - v ∈ K := by
    intro u' hu' hku'
    obtain ⟨y, ⟨hyY, w, hw, -, hyw⟩, huniq⟩ := hYu u' hu' hku'
    refine ⟨y, ⟨hyY, (hK _).2 ⟨w, hw, hyw⟩⟩, fun y' hy' => huniq y' ⟨hy'.1, ?_⟩⟩
    exact rep_half ha'.1 (hstab _ ha'.1) (isHalf_sub hu' (hY y' hy'.1).1) ((hK _).1 hy'.2)
  by_contra hn
  have hfx : IsThetaFunO ψ S T (heisO ψ S T x f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x
  have hGx : ∀ d, IsHalf (cA D a) d → d ∈ K → heisO ψ S T d (heisO ψ S T x f) = heisO ψ S T x f := by
    intro d hdh hdK
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha'.1 (hstab _ ha'.1) hdh ((hK d).1 hdK)
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ hkx, one_smul, hfix v hv (Or.inr hvh)]
  have hd : ∀ y, IsHalf (cA D a) y → y ∉ Λ' → ∃ l ∈ Λ', IsHalf (cA D (cA D a)) l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyΛ'
    have hky : k • y ∉ Λ := fun h => hyΛ' ((memC y hy).2 h)
    obtain ⟨l, hl, hlh, hne⟩ := exists_dual_half ha' hdual (hstab _ (by rw [hcc]; exact ha.1))
      (isHalf_nsmul hy k) hky
    refine ⟨k • l, ?_, isHalf_nsmul hlh k, by rwa [symplO_nsmul_swap]⟩
    rw [hcc] at hlh
    exact (memA _ (isHalf_nsmul hlh k)).2 ⟨l, hl, rfl⟩
  have h1 : ∀ u ∈ Λ', IsHalf (cA D a) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) :=
    fun u hu huh => sum_reps_invariant (ψ := ψ) (Λ := K) (Λ' := Λ') ha'
      (fun y hy => ⟨(memC y (hY y hy).1).2 (hY y hy).2, (hY y hy).1⟩)
      (fun u' hu' hu'h => hYK u' hu'h ((memC u' hu'h).1 hu')) (fun d hdK _ hdh => hGx d hdh hdK) hu huh
  have h2 : ∀ u ∈ Λ', IsHalf (cA D (cA D a)) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) := by
    intro u hu huh
    rw [hcc] at huh
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha.1 (hstab _ ha.1) huh ((memA u huh).1 hu)
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ (hY y hy).2, one_smul, heisO_comm ψ S T (k • v) x,
      half_orth ha (isHalf_nsmul hvh k) hxa, AddChar.map_zero_eq_one, one_smul, hfix v hv (Or.inl hvh)]
  obtain ⟨ℓ, hℓ0, hℓinv⟩ := GlobalTheory.SplitHecke.exists_invariant_form' (Λ := Λ') (ψ := ψ) ha' hd hn h1 h2
  apply hℓ0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun y hy => hℓinv y (hY y hy).1 _ hfx, hℓ ℓ hℓinv x hxa,
    Finset.sum_const_zero]

theorem invForms_separate (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (a : AE D)
    (ha : IsSplitIdem D a) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0) : f = 0 := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  have ha' := isSplitIdem_conj ha
  obtain ⟨k, hk, hfix, -⟩ := (GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D ψ S T hψ _ _ hS hT a ha f hf).1
  obtain ⟨Y, -, hY, hYu, -⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, hXne, hX, -, hXo⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT (cA D a) ha'.1 (infPart_splitIdem ha') k hk
  rw [GlobalTheory.DualPairCheck.cA_cA] at hX
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) ↔
        ∀ u' ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfinΛ : ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), u.map (infPart D) = 0 :=
    fun u hu => latO_fin hu
  have hstab : ∀ e : AE D, e * e = e → ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T),
      e • u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) :=
    fun e he => idem_smul_mem he
  generalize latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) = Λ at *
  have hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu => (hdual u (hfinΛ u hu)).1 hu
  have hB : ∀ x ∈ X, ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := fun x hx =>
    sum_translates_eq_zero ha hψ hdual hpair hstab hf hfix hY hYu hℓ (hX x hx).1 (hX x hx).2
  have hA := sum_average (ψ := ψ) ha (fun u hu huh => hfix u hu (Or.inr huh)) hY hYu (fun x hx => (hX x hx).1) hXo
  have h0 : ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hB x hx]
    exact (heisL ψ S T (-x)).map_zero
  rw [h0] at hA
  have hc : (X.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hXne)
  exact (smul_eq_zero.1 hA.symm).resolve_left hc

end GlobalTheory.DownLift.SplitSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0) → f = 0 := by
  first | exact @GlobalTheory.DownLift.SplitSep.invForms_separate | exact GlobalTheory.DownLift.SplitSep.invForms_separate | (intros; apply GlobalTheory.DownLift.SplitSep.invForms_separate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionTrivialOffSupport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

theorem idemAt_mul_idem_add_conj {D : D7} {P Q' : Finset (Pl D.host.E)} (hP : SplitSet P) (hQ : Q' ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) (hPQ : PP ∉ Q') : idemAt PP * (idem Q' + cA D (idem Q')) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_eq_zero fun q hq => hP.mul_eq_zero hPP (hQ hq) (fun e => hPQ (e ▸ hq)),
    Finset.sum_eq_zero fun q hq => hP.mul_conj hPP (hQ hq), add_zero]


set_option maxHeartbeats 6000000 in
theorem redFn_eq_one_of_suppAt : ∀ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {P Q' : Finset (Pl D.host.E)}, SplitSet P → Q' ⊆ P → ∀ {PP : Pl D.host.E}, PP ∈ P → PP ∉ Q' → ∀ {κ : GA D V}, Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ → redFn β PP (Lev.finE V κ) = 1 := by
  intro D V β P Q' hP hQ PP hPP hPQ κ hS hSupp
  obtain ⟨y, hy⟩ := hS
  obtain ⟨hint, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP (hP.isIdemAt hPP)
  have h0 := idemAt_mul_idem_add_conj hP hQ hPP hPQ

  have hk : ∀ i j, idemAt PP * (Formalism.L2.Theta.mt V κ - 1) i j = 0 := fun i j => by
    rw [← hSupp i j, ← mul_assoc, h0, zero_mul]
  have hval : (Lev.finE V κ).val = (Formalism.L2.Theta.mt V κ).map (toEAf D) := rfl

  have hA : toEAf D (idemAt PP) • ((Lev.finE V κ).val - 1) = 0 := by
    ext i j
    have := congrArg (toEAf D) (hk i j)
    rw [RingHom.map_mul, RingHom.map_zero, Matrix.sub_apply, RingHom.map_sub] at this
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, hval, Matrix.map_apply, Matrix.zero_apply]
    convert this using 3
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hY : toEAf D (idemAt PP) • ((intGL D.host.F D.host.E _ y).val - 1) = 0 := by
    have hg : intGL D.host.F D.host.E _ y = β⁻¹ * Lev.finE V κ * β := by
      rw [← hy]; simp [frGL, MulAut.conj_apply, mul_assoc]
    have e1 : (intGL D.host.F D.host.E _ y).val - 1 = (β⁻¹).val * ((Lev.finE V κ).val - 1) * β.val := by
      rw [hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul β⁻¹ β, inv_mul_cancel, Units.val_one,
        Units.val_mul, Units.val_mul]
    rw [e1, ← Matrix.smul_mul, ← Matrix.mul_smul, hA, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hy, redFn_frGL]
  ext i j
  have hij := congrFun (congrFun hY i) j
  have hsub : (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * y.val i j = (⟨toEAf D (idemAt PP), hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    have hij' : toEAf D (idemAt PP) * ((intGL D.host.F D.host.E _ y).val i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j) = 0 := by
      simpa only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.zero_apply] using hij
    have h1ij : ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j : Lev.EAf D) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, h1ij, ← sub_eq_zero, ← mul_sub]
    exact hij'
  have := congrArg (resS D.host.F PP) hsub
  rw [RingHom.map_mul, RingHom.map_mul, h1, one_mul, one_mul] at this
  change (resS D.host.F PP) (y.val i j) = _
  rw [this, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.ExportSeries

end
end
