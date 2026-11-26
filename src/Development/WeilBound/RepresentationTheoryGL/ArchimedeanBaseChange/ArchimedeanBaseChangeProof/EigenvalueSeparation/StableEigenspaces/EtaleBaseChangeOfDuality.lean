module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.SizeBounds.SizetHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoExpMulPoly

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.CentralEigenvalues.IsStableEigenspaceCap
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.E.E3

namespace centeig

theorem isStable_eigenspace_cap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (τ : E →+* ℂ)
    (u c : ℂ) : _root_.GlobalTheory.CuspRep.IsStable (Module.End.eigenspace (cap (a := N) τ u) c) := by
  intro o φ hφ
  rw [Module.End.mem_eigenspace_iff] at hφ ⊢
  rw [← Module.End.mul_apply, (GlobalTheory.SpehInfChar.cap_commute_act τ u o).eq, Module.End.mul_apply, hφ, map_smul]

theorem isStable_autSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} :
    _root_.GlobalTheory.CuspRep.IsStable (GlobalTheory.DiscClosure.autSub E N) := by
  intro o φ hφ
  exact PositivityTheory.Rg.Rs.PrAut.isAutForm_act PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL o hφ

end centeig

theorem hullaut_holds : HullAut := by
  intro E _ _ _ N S hS
  refine ⟨fun φ hφ => ?_, fun τ m hm => ⟨hm.1, fun u φ hφ => ?_⟩⟩
  · have hle : hull S ≤ GlobalTheory.DiscClosure.autSub E N := sInf_le ⟨fun ψ h => hS ψ h, centeig.isStable_autSub⟩
    exact hle hφ
  · have hle : hull S ≤ Module.End.eigenspace (cap (a := N) τ u) ((m.map (u + ·)).prod) :=
      sInf_le ⟨fun ψ h => Module.End.mem_eigenspace_iff.2 (hm.2 u ψ (Submodule.subset_span h)),
        centeig.isStable_eigenspace_cap τ u _⟩
    exact Module.End.mem_eigenspace_iff.1 (hle hφ)

end PositivityTheory.Rg.BcB.E.E3

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.CentralEigenvalues.CenteigHolds
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC PositivityTheory.S2.Clozel

namespace PositivityTheory.Rg.BcB.E.E3

namespace centeig

open Polynomial Formalism.REAL GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem trace_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (V : Submodule ℂ (Sm E a))
    (τ : E →+* ℂ) (m : Multiset ℂ) (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases a with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end centeig

theorem centeig_holds : CentEig := by
  intro E _ _ _ N V m hm
  refine ⟨∑ τ : E →+* ℂ, (m τ).sum, fun φ hφ t g => ?_⟩
  refine GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ ?_ t g
  rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => centeig.trace_eq V τ (m τ) (hm τ) φ hφ

end PositivityTheory.Rg.BcB.E.E3

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTranslate
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E.E3 PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.CentRe

theorem no_growth (b I K : ℝ) (M : ℕ) (hb : 0 < b) (hI : 0 < I)
    (h : ∀ s : ℝ, 0 ≤ s → I * Real.exp (b * s) ≤ K * (1 + s) ^ M) : False := by
  set K' : ℝ := K / b ^ M / I * Real.exp b with hK'
  obtain ⟨x, hx1, hx2⟩ := (((Real.tendsto_exp_div_pow_atTop M).eventually_gt_atTop K').and
    (eventually_ge_atTop b)).exists
  have hx0 : 0 < x := lt_of_lt_of_le hb hx2
  have hs : 0 ≤ x / b - 1 := by
    rw [sub_nonneg, le_div_iff₀ hb]; linarith
  have hh := h _ hs
  rw [lt_div_iff₀ (pow_pos hx0 M)] at hx1
  have h1 : I * Real.exp (-b) * (K' * x ^ M) < I * Real.exp (-b) * Real.exp x :=
    mul_lt_mul_of_pos_left hx1 (mul_pos hI (Real.exp_pos _))
  have e1 : I * Real.exp (-b) * (K' * x ^ M) = K * (1 + (x / b - 1)) ^ M := by
    have hE := Real.exp_pos b
    rw [hK', Real.exp_neg, show 1 + (x / b - 1) = x / b by ring, div_pow]
    field_simp
  have e2 : I * Real.exp (-b) * Real.exp x = I * Real.exp (b * (x / b - 1)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [e1, e2] at h1
  exact absurd hh (not_le.2 h1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem lintegral_translate [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure]
    (φ : GA E N → ℂ) (z : ℂ) (hz : ∀ (t : ℝ) g, φ (splitCentre E N t * g) = Complex.exp (z * t) * φ g)
    (t : ℝ) (Q : Set (GA E N)) :
    ∫⁻ g in (fun q => splitCentre E N t * q) '' Q, ‖φ g‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (Real.exp (2 * z.re * t)) * ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂μ := by
  rw [← (measurePreserving_mul_left μ (splitCentre E N t)).setLIntegral_comp_emb
    (measurableEmbedding_mulLeft _) (fun g => ‖φ g‖ₑ ^ 2) Q,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun g => ?_
  rw [hz, enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm_eq_enorm, Complex.norm_exp, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  simp
  ring

theorem centReGlue_holds : CentReGlue := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hS hM E _ _ _ N φ z hφ hne hL hz
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  obtain ⟨C, M, hC⟩ := hL Measure.haar inferInstance
  by_contra ha
  obtain ⟨x₀, hx₀⟩ : ∃ x, φ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  obtain ⟨Q, hQ, hQn⟩ := exists_compact_mem_nhds x₀
  obtain ⟨n, hn⟩ := hM E N Q hQ
  obtain ⟨C₁, hC₁, hsz⟩ := hS E N {1} Q isCompact_singleton hQ
  set I : ENNReal := ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E N)) with hI
  have key : ∀ t : ℝ, ENNReal.ofReal (Real.exp (2 * z.re * t)) * I ≤
      ENNReal.ofReal (C * n * (1 + C₁ * (1 + |t|)) ^ M) := by
    intro t
    rw [hI, ← lintegral_translate _ φ z hz t Q]
    refine hC _ (hQ.image (continuous_const.mul continuous_id)) n _ (by positivity) (hn _ ?_) ?_
    · exact fun g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g
    · rintro _ ⟨q, hq, rfl⟩
      have h1 := hsz 1 rfl q hq (fun _ => t)
      rw [one_mul, PositivityTheory.Rg.Rs.JDict.tor_const] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
      have : ‖(fun _ : Fin N => t)‖ ≤ |t| :=
        (pi_norm_le_iff_of_nonneg (abs_nonneg t)).2 fun _ => (Real.norm_eq_abs t).le
      linarith
  have hIpos : 0 < I := by
    rw [hI, setLIntegral_pos_iff (hφ.measurable.enorm.pow_const 2)]
    have hV : IsOpen (interior Q ∩ {x | φ x ≠ 0}) :=
      isOpen_interior.inter (isOpen_ne_fun hφ continuous_const)
    have hVne : (interior Q ∩ {x | φ x ≠ 0}).Nonempty :=
      ⟨x₀, mem_interior_iff_mem_nhds.2 hQn, hx₀⟩
    refine (hV.measure_pos _ hVne).trans_le (measure_mono ?_)
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, interior_subset hx1⟩
    simpa [Function.mem_support] using hx2
  have hItop : I ≠ ⊤ := by
    have h0 := key 0
    simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h0
    exact (h0.trans_lt ENNReal.ofReal_lt_top).ne
  have hI' : 0 < I.toReal := ENNReal.toReal_pos hIpos.ne' hItop
  have key' : ∀ t : ℝ, I.toReal * Real.exp (2 * z.re * t) ≤ C * n * (1 + C₁ * (1 + |t|)) ^ M := by
    intro t
    have h := key t
    rw [← ENNReal.ofReal_toReal hItop, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h
    · rwa [mul_comm]
    · exact absurd h (not_le.2 (mul_pos (Real.exp_pos _) hI'))
  refine no_growth (2 * |z.re|) I.toReal (|C * n| * (1 + C₁) ^ M) M
    (by have := abs_pos.2 ha; positivity) hI' fun s hs => ?_
  have hsign : ∃ t : ℝ, 2 * z.re * t = 2 * |z.re| * s ∧ |t| = s := by
    rcases le_total 0 z.re with h | h
    · exact ⟨s, by rw [abs_of_nonneg h], abs_of_nonneg hs⟩
    · exact ⟨-s, by rw [abs_of_nonpos h]; ring, by rw [abs_neg, abs_of_nonneg hs]⟩
  obtain ⟨t, ht1, ht2⟩ := hsign
  have h := key' t
  rw [ht1, ht2] at h
  refine h.trans ?_
  have hb : 1 + C₁ * (1 + s) ≤ (1 + C₁) * (1 + s) := by nlinarith
  calc C * n * (1 + C₁ * (1 + s)) ^ M ≤ |C * n| * (1 + C₁ * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C * n| * ((1 + C₁) * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb M) (abs_nonneg _)
    _ = |C * n| * (1 + C₁) ^ M * (1 + s) ^ M := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CentRe

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.StableHulls.IsStableHull
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.E.E3.asm

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem subset_hull {N : ℕ} (S : Set (Sm E N)) : S ⊆ (hull S : Set (Sm E N)) := fun _ hφ =>
  Submodule.mem_sInf.2 fun _ hU => hU.1 hφ

theorem hull_eq_bot {N : ℕ} {S : Set (Sm E N)} (h : ∀ φ ∈ S, φ = 0) : hull S = ⊥ := by
  refine le_bot_iff.1 (sInf_le ⟨fun φ hφ => ?_, ?_⟩)
  · rw [h φ hφ]; exact Submodule.zero_mem _
  · intro o φ hφ
    rw [(Submodule.mem_bot ℂ).1 hφ, map_zero]; exact Submodule.zero_mem _

theorem isStable_hull {N : ℕ} (S : Set (Sm E N)) : _root_.GlobalTheory.CuspRep.IsStable (hull S) := by
  intro o φ hφ
  rw [hull, Submodule.mem_sInf] at hφ ⊢
  exact fun U hU => hU.2 o φ (hφ U hU)

theorem type₁ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : SpectralAccumulation.TypeH K₁ K₂ W₁ W₂ F) (y : GA E b) :
    (∀ u ∈ K₁, ∀ x, F (x * finGL E a u, y) = F (x, y)) ∧
      ∀ x, (fun k : Kinf E a => F (x * infGL E a (Unitary.toUnits k), y)) ∈ W₁ := by
  refine ⟨fun u hu x => ?_, fun x => ?_⟩
  · have h := hF.1 u hu 1 K₂.one_mem (x, y)
    simpa using h
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) := LinearMap.funLeft ℂ ℂ fun k => (k, 1)
    have hle : Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2} ≤
        W₁.comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have h : L (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k; simp [L, LinearMap.funLeft_apply, mul_comm]
      show L _ ∈ W₁
      rw [h]; exact W₁.smul_mem _ hw₁
    have h := hle (hF.2 (x, y))
    rw [Submodule.mem_comap] at h
    convert h using 1
    funext k
    simp [L, LinearMap.funLeft_apply]

theorem type₂ {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ}
    (hF : SpectralAccumulation.TypeH K₁ K₂ W₁ W₂ F) (y : GA E a) :
    (∀ u ∈ K₂, ∀ x, F (y, x * finGL E b u) = F (y, x)) ∧
      ∀ x, (fun k : Kinf E b => F (y, x * infGL E b (Unitary.toUnits k))) ∈ W₂ := by
  refine ⟨fun u hu x => ?_, fun x => ?_⟩
  · have h := hF.1 1 K₁.one_mem u hu (y, x)
    simpa using h
  · let L : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) := LinearMap.funLeft ℂ ℂ fun k => (1, k)
    have hle : Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2} ≤
        W₂.comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have h : L (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k; simp [L, LinearMap.funLeft_apply]
      show L _ ∈ W₂
      rw [h]; exact W₂.smul_mem _ hw₂
    have h := hle (hF.2 (y, x))
    rw [Submodule.mem_comap] at h
    convert h using 1
    funext k
    simp [L, LinearMap.funLeft_apply]

theorem fd_range₂ {ι : Type} (f : ι → H E a b → ℂ) (i : ι) (h₂ : ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (slices₂ f))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x y => f i (x, y))) := by
  have hle : Submodule.span ℂ (Set.range fun x y => f i (x, y)) ≤
      (Submodule.span ℂ (slices₂ f)).map (Sm E b).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨φ, hφ⟩ := h₂ i x
    exact ⟨φ, Submodule.subset_span (show ∃ j m, φ.1 = fun y => f j (m, y) from ⟨i, x, hφ⟩), hφ⟩
  exact Submodule.finiteDimensional_of_le hle

theorem fd_range₁ {ι : Type} (f : ι → H E a b → ℂ) (i : ι) (h₁ : ∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (slices₁ f))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y x => f i (x, y))) := by
  have hle : Submodule.span ℂ (Set.range fun y x => f i (x, y)) ≤
      (Submodule.span ℂ (slices₁ f)).map (Sm E a).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ⟩ := h₁ i y
    exact ⟨φ, Submodule.subset_span (show ∃ j m, φ.1 = fun x => f j (x, m) from ⟨i, y, hφ⟩), hφ⟩
  exact Submodule.finiteDimensional_of_le hle

theorem centIm {N : ℕ} (hCE : CentEig) (hCR : CentRe) (S : Set (Sm E N)) (m : (E →+* ℂ) → Multiset ℂ)
    (hm : ∀ τ, HasInfCharGL (hull S) τ (m τ)) (hc : ∀ φ ∈ S, Continuous φ.1) (hl : ∀ φ ∈ S, Loc φ.1) :
    SpectralAccumulation.CentIm (hull S) := by
  obtain ⟨z, hz⟩ := hCE E N (hull S) m hm
  by_cases h0 : ∃ φ ∈ S, φ ≠ 0
  · obtain ⟨φ, hφ, hne⟩ := h0
    refine ⟨z, hCR E N φ.1 z (hc φ hφ) (fun h => hne (Subtype.ext h)) (hl φ hφ) (hz φ (subset_hull S hφ)), hz⟩
  · push Not at h0
    refine ⟨0, by simp, fun φ hφ t g => ?_⟩
    rw [hull_eq_bot h0, Submodule.mem_bot] at hφ
    subst hφ
    simp

end PositivityTheory.Rg.BcB.E.E3.asm

namespace PositivityTheory.Rg.BcB.E.E3

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E.E3.asm

theorem asm_holds : Asm := by
  intro hFin hLocSl hLNP hCE hCR hHA hHNP hPS E _ _ _ a b D ι _ M f K₁ K₂ W₁ W₂ m₁ m₂ hK₁ hK₂ hW₁ hW₂ hcont hinv
    hwl2 htype hs₁ hs₂ haut₁ haut₂ hinf₁ hinf₂
  have fd₁ : FiniteDimensional ℂ (Submodule.span ℂ (slices₁ f)) := by
    refine hFin E a K₁ W₁ m₁ (slices₁ f) hK₁ hW₁ (fun φ hφ => ?_) hinf₁
    obtain ⟨i, y, hφ'⟩ := hφ
    obtain ⟨hl, hk⟩ := type₁ (htype i) y
    refine ⟨haut₁ φ ⟨i, y, hφ'⟩, fun u hu x => ?_, fun x => ?_⟩
    · rw [hφ']; exact hl u hu x
    · rw [hφ']; exact hk x
  have fd₂ : FiniteDimensional ℂ (Submodule.span ℂ (slices₂ f)) := by
    refine hFin E b K₂ W₂ m₂ (slices₂ f) hK₂ hW₂ (fun φ hφ => ?_) hinf₂
    obtain ⟨i, y, hφ'⟩ := hφ
    obtain ⟨hl, hk⟩ := type₂ (htype i) y
    refine ⟨haut₂ φ ⟨i, y, hφ'⟩, fun u hu x => ?_, fun x => ?_⟩
    · rw [hφ']; exact hl u hu x
    · rw [hφ']; exact hk x
  have hloc := fun i => hLocSl E a b D M (f i) (hcont i) (fun _ γ x => hinv i γ x) (fun _ => hwl2 i)
  have loc₁ : ∀ φ ∈ slices₁ f, Loc φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; exact (hloc i).1 (fd_range₂ f i hs₂ fd₂) y
  have loc₂ : ∀ φ ∈ slices₂ f, Loc φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; exact (hloc i).2 (fd_range₁ f i hs₁ fd₁) y
  have cont₁ : ∀ φ ∈ slices₁ f, Continuous φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; have := hcont i; fun_prop
  have cont₂ : ∀ φ ∈ slices₂ f, Continuous φ.1 := by
    intro φ hφ
    obtain ⟨i, y, hφ'⟩ := hφ
    rw [hφ']; have := hcont i; fun_prop
  have ha₁ := hHA E a (slices₁ f) haut₁
  have ha₂ := hHA E b (slices₂ f) haut₂
  have inf₁ : ∀ τ, HasInfCharGL (hull (slices₁ f)) τ (m₁ τ) := fun τ => ha₁.2 τ (m₁ τ) (hinf₁ τ)
  have inf₂ : ∀ τ, HasInfCharGL (hull (slices₂ f)) τ (m₂ τ) := fun τ => ha₂.2 τ (m₂ τ) (hinf₂ τ)
  refine ⟨isStable_hull _, isStable_hull _, ha₁.1, ha₂.1,
    hHNP E a (slices₁ f) fun φ hφ => ⟨haut₁ φ hφ, hLNP E a φ (haut₁ φ hφ) (loc₁ φ hφ)⟩,
    hHNP E b (slices₂ f) fun φ hφ => ⟨haut₂ φ hφ, hLNP E b φ (haut₂ φ hφ) (loc₂ φ hφ)⟩,
    centIm hCE hCR _ m₁ inf₁ cont₁ loc₁, centIm hCE hCR _ m₂ inf₂ cont₂ loc₂, inf₁, inf₂, fun i => ?_⟩
  refine hPS E a b (f i) _ _ (fun y => ?_) (fun x => ?_) (fd_range₁ f i hs₁ fd₁)
  · obtain ⟨φ, hφ⟩ := hs₁ i y
    exact ⟨φ, subset_hull _ ⟨i, y, hφ⟩, hφ⟩
  · obtain ⟨ψ, hψ⟩ := hs₂ i x
    exact ⟨ψ, subset_hull _ ⟨i, x, hψ⟩, hψ⟩

end PositivityTheory.Rg.BcB.E.E3

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralCompactLe
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E.E3
open scoped ENNReal GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.LocSlice

theorem lintegral_compact_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Fd P : Set G) (hF : IsFundamentalDomain Γ Fd μ) (hP : IsCompact P) (f : G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (w : G → ℝ) (W : ℝ) (K : ℕ) (hw1 : ∀ x, 1 ≤ w x)
    (hw : ∀ γ ∈ Γ, ∀ p ∈ P, w (γ * p) ≤ W) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ P}.encard ≤ N) :
    ∫⁻ x in P, ‖f x‖ₑ ^ 2 ∂μ ≤
      N * (ENNReal.ofReal (W ^ (2 * K)) *
        ∫⁻ x in Fd, ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2 ∂μ) := by
  classical
  let T : Set G := ⋃ γ : Γ, (fun x => (γ : G) * x) '' P
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun γ =>
    (hP.image (continuous_const.mul continuous_id)).isClosed.measurableSet
  have hPT : P ⊆ T := fun x hx => Set.mem_iUnion.2 ⟨1, x, hx, by simp⟩
  have hTinv : ∀ γ ∈ Γ, ∀ x ∈ T, γ * x ∈ T := by
    intro γ hγ x hx
    obtain ⟨δ, p, hp, rfl⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩ * δ, p, hp, by simp [mul_assoc]⟩
  let h : G → ℝ≥0∞ := T.indicator fun x => ‖f x‖ₑ ^ 2
  have hh : Measurable h := (hf.measurable.enorm.pow_const 2).indicator hTm
  have hhinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x := by
    intro γ hγ x
    by_cases hx : x ∈ T
    · simp only [h, Set.indicator_of_mem hx, Set.indicator_of_mem (hTinv γ hγ x hx), hinv γ hγ x]
    · have hx' : γ * x ∉ T := fun h' => hx (by
        simpa using hTinv γ⁻¹ (inv_mem hγ) _ h')
      simp only [h, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  have h1 : ∫⁻ x in P, ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ x in P, h x ∂μ :=
    setLIntegral_congr_fun hP.measurableSet fun x hx => by
      simp only [h, Set.indicator_of_mem (hPT hx)]
  have h2 := GlobalTheory.CompanionTheory.Unfolding.setLIntegral_le_mul_fundamentalDomain_diff Γ μ Fd P ∅ hF hP.measurableSet
    MeasurableSet.empty h hh hhinv N hN (by simp)
  rw [h1]
  refine h2.trans ?_
  gcongr
  rw [Set.diff_empty, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ T
  · obtain ⟨δ, p, hp, rfl⟩ := Set.mem_iUnion.1 hx
    have hwW := hw δ δ.2 p hp
    have hw0 : 0 < w ((δ : G) * p) := lt_of_lt_of_le one_pos (hw1 _)
    have hpow : w ((δ : G) * p) ^ (2 * K) ≤ W ^ (2 * K) := pow_le_pow_left₀ hw0.le hwW _
    have hq : (1 : ℝ) ≤ W ^ (2 * K) * w ((δ : G) * p) ^ (-(2 * K : ℤ)) := by
      have e : w ((δ : G) * p) ^ (-(2 * K : ℤ)) = (w ((δ : G) * p) ^ (2 * K))⁻¹ := by
        rw [_root_.zpow_neg]
        norm_cast
      rw [e, ← div_eq_mul_inv, one_le_div (pow_pos hw0 _)]
      exact hpow
    have hW0 : 0 ≤ W ^ (2 * K) := (pow_pos hw0 _).le.trans hpow
    simp only [h, Set.indicator_of_mem hx]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hW0]
    calc ‖f ((δ : G) * p)‖ₑ ^ 2 = 1 * ‖f ((δ : G) * p)‖ₑ ^ 2 := (one_mul _).symm
      _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hq
  · simp only [h, Set.indicator_of_notMem hx, zero_le]

theorem pair_bound {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [T2Space X] [T2Space Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m)
    (Γ : Subgroup (X × Y)) [Countable Γ] (μ : @Measure (X × Y) m)
    (hL : @Measure.IsMulLeftInvariant _ m _ μ) (hO : @Measure.IsOpenPosMeasure _ _ m μ)
    (hLF : @IsLocallyFiniteMeasure _ m _ μ) (Fd : Set (X × Y))
    (hF : @IsFundamentalDomain Γ (X × Y) _ _ m Fd μ) (f : X × Y → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (w : X × Y → ℝ) (K : ℕ) (hw1 : ∀ x, 1 ≤ w x) :
    ∃ c : NNReal, ∀ (A : Set X) (B : Set Y) (W : ℝ) (N : ℕ), IsCompact A → IsCompact B →
      (∀ γ ∈ Γ, ∀ p ∈ A ×ˢ B, w (γ * p) ≤ W) →
      (∀ x, {γ : Γ | (γ : X × Y) * x ∈ A ×ˢ B}.encard ≤ N) →
      (∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ ≤ c * (N * (ENNReal.ofReal (W ^ (2 * K)) *
        @lintegral _ m (@Measure.restrict _ m μ Fd)
          fun x => ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2))) ∧
      (∫⁻ y in B, ∫⁻ x in A, ‖f (x, y)‖ₑ ^ 2 ∂μ₁ ∂μ₂ ≤ c * (N * (ENNReal.ofReal (W ^ (2 * K)) *
        @lintegral _ m (@Measure.restrict _ m μ Fd)
          fun x => ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2))) := by
  subst e
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  haveI := hL
  haveI := hO
  haveI := hLF
  haveI : μ.IsHaarMeasure := {}
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ₁.prod μ₂ = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun A B W N hA hB hw hN => ?_⟩
  have hmeas : Measurable fun p : X × Y => ‖f p‖ₑ ^ 2 := hf.measurable.enorm.pow_const 2
  have h1 : ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ =
      c * ∫⁻ p in A ×ˢ B, ‖f p‖ₑ ^ 2 ∂μ := by
    have e1 : ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ =
        ∫⁻ p in A ×ˢ B, ‖f p‖ₑ ^ 2 ∂(μ₁.prod μ₂) := by
      rw [← Measure.prod_restrict, lintegral_prod _ hmeas.aemeasurable]
    rw [e1, hc, Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have h2 := lintegral_compact_le Γ μ Fd (A ×ˢ B) hF (hA.prod hB) f hf hinv w W K hw1 hw N hN
  have h3 : ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ ≤ c * (N * (ENNReal.ofReal (W ^ (2 * K)) *
      ∫⁻ x in Fd, ENNReal.ofReal (w x ^ (-(2 * K : ℤ))) * ‖f x‖ₑ ^ 2 ∂μ)) := by
    rw [h1]; gcongr
  refine ⟨h3, ?_⟩
  have h4 : ∫⁻ y in B, ∫⁻ x in A, ‖f (x, y)‖ₑ ^ 2 ∂μ₁ ∂μ₂ = ∫⁻ x in A, ∫⁻ y in B, ‖f (x, y)‖ₑ ^ 2 ∂μ₂ ∂μ₁ :=
    (lintegral_lintegral_swap (f := fun x y => ‖f (x, y)‖ₑ ^ 2) hmeas.aemeasurable).symm
  rw [h4]
  exact h3

theorem final_le (Cy c : NNReal) (n n₂ K : ℕ) (R R₂ : ℝ) (hR : 0 ≤ R) (hR₂ : 0 ≤ R₂) (I : ℝ≥0∞) (hI : I ≠ ⊤) :
    (Cy : ℝ≥0∞) * (c * (((n * n₂ : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 + R + R₂) ^ (2 * K)) * I))) ≤
      ENNReal.ofReal ((Cy : ℝ) * c * n₂ * (1 + R₂) ^ (2 * K) * I.toReal * n * (1 + R) ^ (2 * K)) := by
  have e1 : I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hI).symm
  have e2 : (Cy : ℝ≥0∞) = ENNReal.ofReal Cy := (ENNReal.ofReal_coe_nnreal).symm
  have e3 : (c : ℝ≥0∞) = ENNReal.ofReal c := (ENNReal.ofReal_coe_nnreal).symm
  have e4 : ((n * n₂ : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n * n₂ : ℕ) : ℝ) := (ENNReal.ofReal_natCast _).symm
  have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  have hp : (0 : ℝ) ≤ (1 + R + R₂) ^ (2 * K) := by positivity
  rw [e4, e2, e3]
  nth_rw 1 [e1]
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (1 + R + R₂) ^ (2 * K) ≤ (1 + R) ^ (2 * K) * (1 + R₂) ^ (2 * K) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hR hR₂]) _
  have h2 : (0 : ℝ) ≤ (Cy : ℝ) * c * (n * n₂) * I.toReal := by positivity
  push_cast
  calc (Cy : ℝ) * (c * (n * n₂ * ((1 + R + R₂) ^ (2 * K) * I.toReal)))
      = ((Cy : ℝ) * c * (n * n₂) * I.toReal) * (1 + R + R₂) ^ (2 * K) := by ring
    _ ≤ ((Cy : ℝ) * c * (n * n₂) * I.toReal) * ((1 + R) ^ (2 * K) * (1 + R₂) ^ (2 * K)) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem logSize_nonneg {n : ℕ} (g : GA E n) : 0 ≤ logSize g := by
  have hM : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (hM _) (hM _)

theorem redSize_nonneg {n : ℕ} (g : GA E n) : 0 ≤ redSize g :=
  Real.iInf_nonneg fun _ => logSize_nonneg _

theorem redSize_mul_le {n : ℕ} (γ : GL (Fin n) E) (g : GA E n) : redSize (ratGL E n γ * g) ≤ logSize g := by
  have h := ciInf_le (f := fun δ : GL (Fin n) E => logSize (ratGL E n δ * (ratGL E n γ * g)))
    ⟨0, by rintro _ ⟨δ, rfl⟩; exact logSize_nonneg _⟩ γ⁻¹
  simpa [redSize, ← mul_assoc] using h

theorem one_le_wt (x : H E a b) : 1 ≤ wt x := by
  have h1 := redSize_nonneg x.1
  have h2 := redSize_nonneg x.2
  unfold wt
  linarith

theorem wt_mul_le {R₁ R₂ : ℝ} (γ : H E a b) (hγ : γ ∈ ratH E a b) (p : H E a b) (h₁ : logSize p.1 ≤ R₁)
    (h₂ : logSize p.2 ≤ R₂) : wt (γ * p) ≤ 1 + R₁ + R₂ := by
  obtain ⟨⟨A, B⟩, rfl⟩ := hγ
  have h3 := redSize_mul_le A p.1
  have h4 := redSize_mul_le B p.2
  have e : wt (((ratGL E a).prodMap (ratGL E b) (A, B)) * p) =
      1 + redSize (ratGL E a A * p.1) + redSize (ratGL E b B * p.2) := rfl
  rw [e]
  linarith

theorem mult_prod {A : Set (GA E a)} {B : Set (GA E b)} {n₁ n₂ : ℕ} (h₁ : Mult A n₁) (h₂ : Mult B n₂)
    (x : H E a b) : {γ : ratH E a b | (γ : H E a b) * x ∈ A ×ˢ B}.encard ≤ ((n₁ * n₂ : ℕ) : ℕ∞) := by
  let φ : ratH E a b → (ratGL E a).range × (ratGL E b).range := fun γ =>
    (⟨γ.1.1, γ.2.choose.1, congrArg Prod.fst γ.2.choose_spec⟩,
      ⟨γ.1.2, γ.2.choose.2, congrArg Prod.snd γ.2.choose_spec⟩)
  have hφ : Function.Injective φ := fun u v h => Subtype.ext (Prod.ext
    (congrArg (fun z => (z.1 : GA E a)) h) (congrArg (fun z => (z.2 : GA E b)) h))
  calc {γ : ratH E a b | (γ : H E a b) * x ∈ A ×ˢ B}.encard
      = (φ '' {γ : ratH E a b | (γ : H E a b) * x ∈ A ×ˢ B}).encard := (hφ.encard_image _).symm
    _ ≤ ({γ : (ratGL E a).range | (γ : GA E a) * x.1 ∈ A} ×ˢ
          {γ : (ratGL E b).range | (γ : GA E b) * x.2 ∈ B}).encard := by
        refine Set.encard_le_encard ?_
        rintro _ ⟨γ, hγ, rfl⟩
        exact ⟨hγ.1, hγ.2⟩
    _ = {γ : (ratGL E a).range | (γ : GA E a) * x.1 ∈ A}.encard *
          {γ : (ratGL E b).range | (γ : GA E b) * x.2 ∈ B}.encard := Set.encard_prod
    _ ≤ (n₁ : ℕ∞) * n₂ := mul_le_mul' (h₁ _) (h₂ _)
    _ = _ := by push_cast; rfl

theorem exists_logSize_le (hS : SizeT) {n : ℕ} {Q : Set (GA E n)} (hQ : IsCompact Q) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ Q, logSize q ≤ R := by
  obtain ⟨C, hC0, hC⟩ := hS E n {(An.tor E (0 : Fin n → ℝ) : GA E n)⁻¹} Q isCompact_singleton hQ
  refine ⟨C, hC0, fun q hq => ?_⟩
  have h := hC _ rfl q hq 0
  simpa using h

theorem countable_ratH (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Countable (ratH E a b) := by
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  have hM : ∀ m : ℕ, Countable (GL (Fin m) E) := fun m =>
    haveI : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
    (Units.val_injective (α := Matrix (Fin m) (Fin m) E)).countable
  haveI := hM a
  haveI := hM b
  exact ((ratGL E a).prodMap (ratGL E b)).rangeRestrict_surjective.countable

theorem loc_first (hT : SizeT) (hM : MultC) (hI : InterpolationL2Bound) (D : Dom E a b) (K : ℕ) (F : H E a b → ℂ)
    (hF : Continuous F) (hinv : LeftInv (fun _ : Unit => F)) (hW : WL2 D K (fun _ : Unit => F))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x y => F (x, y)))) (y₀ : GA E b)
    (μ : Measure (GA E a)) (hμ : μ.IsHaarMeasure) :
    ∃ (C : ℝ) (M : ℕ), ∀ S : Set (GA E a), IsCompact S → ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      Mult S n → (∀ g ∈ S, logSize g ≤ R) →
      ∫⁻ g in S, ‖F (g, y₀)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * n * (1 + R) ^ M) := by
  haveI := hμ
  haveI := countable_ratH E a b
  obtain ⟨Ω, hΩ, hC⟩ := hI (GA E a) (GA E b) (Measure.haar : Measure (GA E b)) (fun x y => F (x, y))
    (fun x => hF.comp (Continuous.prodMk_right x)) hfd
  obtain ⟨Cy, hCy⟩ := hC y₀
  obtain ⟨n₂, hn₂⟩ := hM E b Ω hΩ
  have hm₂ : Mult Ω n₂ := by simpa using hn₂ 1 (by simp)
  obtain ⟨R₂, hR₂0, hR₂⟩ := exists_logSize_le hT hΩ
  obtain ⟨c, hc⟩ := pair_bound μ (Measure.haar : Measure (GA E b)) (borelH E a b)
    Prod.borelSpace.measurable_eq (ratH E a b) D.μ D.haar.1 D.haar.2.2.1 D.haar.2.2.2 D.F D.fd F hF
    (fun γ hγ x => hinv () ⟨γ, hγ⟩ x) wt K one_le_wt
  have hIt := (hW ()).ne
  refine ⟨(Cy : ℝ) * c * n₂ * (1 + R₂) ^ (2 * K) *
    (∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * K : ℤ))) * ‖F x‖ₑ ^ 2 ∂D.ν).toReal, 2 * K, fun S hS n R hR hn hSz => ?_⟩
  have h1 := (hc S Ω (1 + R + R₂) (n * n₂) hS hΩ
    (fun γ hγ p hp => wt_mul_le γ hγ p (hSz _ hp.1) (hR₂ _ hp.2)) (mult_prod hn hm₂)).1
  calc ∫⁻ g in S, ‖F (g, y₀)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in S, (Cy : ℝ≥0∞) * ∫⁻ y in Ω, ‖F (g, y)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E b)) ∂μ :=
        lintegral_mono fun x => hCy x
    _ = Cy * ∫⁻ g in S, ∫⁻ y in Ω, ‖F (g, y)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E b)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := mul_le_mul_right h1 _
    _ ≤ _ := final_le Cy c n n₂ K R R₂ hR hR₂0 _ hIt

theorem loc_second (hT : SizeT) (hM : MultC) (hI : InterpolationL2Bound) (D : Dom E a b) (K : ℕ) (F : H E a b → ℂ)
    (hF : Continuous F) (hinv : LeftInv (fun _ : Unit => F)) (hW : WL2 D K (fun _ : Unit => F))
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y x => F (x, y)))) (x₀ : GA E a)
    (μ : Measure (GA E b)) (hμ : μ.IsHaarMeasure) :
    ∃ (C : ℝ) (M : ℕ), ∀ S : Set (GA E b), IsCompact S → ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      Mult S n → (∀ g ∈ S, logSize g ≤ R) →
      ∫⁻ g in S, ‖F (x₀, g)‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * n * (1 + R) ^ M) := by
  haveI := hμ
  haveI := countable_ratH E a b
  obtain ⟨Ω, hΩ, hC⟩ := hI (GA E b) (GA E a) (Measure.haar : Measure (GA E a)) (fun y x => F (x, y))
    (fun y => hF.comp (Continuous.prodMk_left y)) hfd
  obtain ⟨Cy, hCy⟩ := hC x₀
  obtain ⟨n₂, hn₂⟩ := hM E a Ω hΩ
  have hm₂ : Mult Ω n₂ := by simpa using hn₂ 1 (by simp)
  obtain ⟨R₂, hR₂0, hR₂⟩ := exists_logSize_le hT hΩ
  obtain ⟨c, hc⟩ := pair_bound (Measure.haar : Measure (GA E a)) μ (borelH E a b)
    Prod.borelSpace.measurable_eq (ratH E a b) D.μ D.haar.1 D.haar.2.2.1 D.haar.2.2.2 D.F D.fd F hF
    (fun γ hγ x => hinv () ⟨γ, hγ⟩ x) wt K one_le_wt
  have hIt := (hW ()).ne
  refine ⟨(Cy : ℝ) * c * n₂ * (1 + R₂) ^ (2 * K) *
    (∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * K : ℤ))) * ‖F x‖ₑ ^ 2 ∂D.ν).toReal, 2 * K, fun S hS n R hR hn hSz => ?_⟩
  have h1 := (hc Ω S (1 + R + R₂) (n * n₂) hΩ hS
    (fun γ hγ p hp => (wt_mul_le γ hγ p (hR₂ _ hp.1) (hSz _ hp.2)).trans_eq (by ring))
    (fun x => by rw [mul_comm n n₂]; exact mult_prod hm₂ hn x)).2
  calc ∫⁻ g in S, ‖F (x₀, g)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in S, (Cy : ℝ≥0∞) * ∫⁻ x in Ω, ‖F (x, g)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E a)) ∂μ :=
        lintegral_mono fun x => hCy x
    _ = Cy * ∫⁻ g in S, ∫⁻ x in Ω, ‖F (x, g)‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E a)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := mul_le_mul_right h1 _
    _ ≤ _ := final_le Cy c n n₂ K R R₂ hR hR₂0 _ hIt

theorem locSlGlue : PositivityTheory.Rg.BcB.E.E3.LocSlGlue := by
  intro hT hM hI E _ _ _ a b D K F hF hinv hW
  exact ⟨fun hfd y μ hμ => loc_first hT hM hI D K F hF hinv hW hfd y μ hμ,
    fun hfd x μ hμ => loc_second hT hM hI D K F hF hinv hW hfd x μ hμ⟩

end GlobalTheory.CompanionTheory.LocSlice

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvEqOfCentral
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralMult

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem finite_range_inter (C : Set (GA E N)) (hC : IsCompact C) :
    (C ∩ ((ratGL E N).range : Set (GA E N))).Finite := by
  have : T2Space (GA E N) := by
    have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
    exact Units.isEmbedding_embedProduct.t2Space
  have : T1Space (GA E N) := T2Space.t1Space
  have hd : DiscreteTopology ((ratGL E N).range) := GlobalTheory.MirTower.discrete_of_le_range le_rfl
  have hcl : IsClosed (((ratGL E N).range : Subgroup (GA E N)) : Set (GA E N)) :=
    Subgroup.isClosed_of_discrete
  have hK : IsCompact (C ∩ ((ratGL E N).range : Set (GA E N))) := hC.inter_right hcl
  have hds : DiscreteTopology ↥(C ∩ ((ratGL E N).range : Set (GA E N))) :=
    DiscreteTopology.of_subset hd Set.inter_subset_right
  exact hK.finite ⟨hds⟩

theorem mul_inv_eq_of_central {G : Type} [Group G] {z x a b q r : G} (hz : ∀ g, z * g = g * z)
    (ha : a * x = z * q) (hb : b * x = z * r) : a * b⁻¹ = q * r⁻¹ := by
  have h1 : a = z * q * x⁻¹ := eq_mul_inv_of_mul_eq ha
  have h2 : b = z * r * x⁻¹ := eq_mul_inv_of_mul_eq hb
  have h3 : z * q * x⁻¹ * (z * r * x⁻¹)⁻¹ = z * (q * r⁻¹) * z⁻¹ := by group
  rw [h1, h2, h3, hz, mul_inv_cancel_right]

theorem multC : PositivityTheory.Rg.BcB.E.E3.MultC := by
  intro E _ _ _ N Q hQ
  have hC : IsCompact (Q * Q⁻¹) := hQ.mul hQ.inv
  have hF := finite_range_inter (Q * Q⁻¹) hC
  refine ⟨hF.toFinset.card, fun z hz x => ?_⟩
  rw [← hF.encard_eq_coe_toFinset_card]
  rcases Set.eq_empty_or_nonempty
    {γ : (ratGL E N).range | (γ : GA E N) * x ∈ (fun q => z * q) '' Q} with h0 | ⟨γ₀, q₀, hq₀, e₀⟩
  · rw [h0]
    simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : (ratGL E N).range => (γ : GA E N) * (γ₀ : GA E N)⁻¹) ?_ ?_
    · rintro γ ⟨q, hq, e⟩
      refine ⟨?_, mul_mem γ.2 (inv_mem γ₀.2)⟩
      have e' : (γ : GA E N) * (γ₀ : GA E N)⁻¹ = q * q₀⁻¹ := mul_inv_eq_of_central hz e.symm e₀.symm
      change (γ : GA E N) * (γ₀ : GA E N)⁻¹ ∈ Q * Q⁻¹
      rw [e']
      exact Set.mul_mem_mul hq (Set.inv_mem_inv.2 hq₀)
    · intro γ _ γ' _ h
      exact Subtype.ext (mul_right_cancel h)

end GlobalTheory.CompanionTheory.CentralMult

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSp
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.PairSpProof

theorem pairSp : PositivityTheory.Rg.BcB.E.E3.PairSp := by
  intro E _ _ _ a b F U₁ U₂ h₁ h₂ hfd
  classical
  set A : Submodule ℂ (GA E a → ℂ) := Submodule.span ℂ (Set.range fun y x => F (x, y)) with hA
  have : FiniteDimensional ℂ A := hfd
  obtain ⟨S, c, hc⟩ := PositivityTheory.Rg.Rs.SliceTensor.interp A

  let V : Submodule ℂ (GA E a → ℂ) := (U₁.map (Submodule.subtype _))
  have hAV : A ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ, e⟩ := h₁ y
    exact ⟨φ, hφ, e⟩
  have hF : F = ∑ κ : S, fun x : GA E a × GA E b => (c κ : GA E a → ℂ) x.1 * F (κ.1, x.2) := by
    funext ⟨x, y⟩
    have hy : (fun x => F (x, y)) ∈ A := Submodule.subset_span ⟨y, rfl⟩
    have := congrFun (hc _ hy) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  rw [hF]
  refine Submodule.sum_mem _ fun κ _ => Submodule.subset_span ?_
  obtain ⟨φ, hφ, e⟩ := hAV (c κ).2
  obtain ⟨ψ, hψ, e'⟩ := h₂ κ.1
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  funext x
  have e1 : φ.1 = (c κ : GA E a → ℂ) := e
  rw [e1, e']

end GlobalTheory.CompanionTheory.PairSpProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterpolationLocalL2Bound
open MeasureTheory

namespace GlobalTheory.CompanionTheory.InterpLoc

theorem exists_finset_separating {Y : Type} (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ] :
    ∃ t : Finset Y, ∀ ψ ∈ Ψ, (∀ y ∈ t, ψ y = 0) → ψ = 0 := by
  classical
  let K : Finset Y → Submodule ℂ (Y → ℂ) := fun t =>
    { carrier := {ψ | ψ ∈ Ψ ∧ ∀ y ∈ t, ψ y = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨Ψ.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩
      zero_mem' := ⟨Ψ.zero_mem, fun _ _ => rfl⟩
      smul_mem' := fun c a ha =>
        ⟨Ψ.smul_mem c ha.1, fun y hy => by simp [ha.2 y hy]⟩ }
  have hKle : ∀ t, K t ≤ Ψ := fun t _ h => h.1
  haveI : ∀ t, FiniteDimensional ℂ (K t) := fun t => Submodule.finiteDimensional_of_le (hKle t)
  let f : Finset Y → ℕ := fun t => Module.finrank ℂ (K t)
  refine ⟨Function.argmin f, fun ψ hψ h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set t := Function.argmin f with ht
  have hlt : K (insert y t) < K t := by
    refine lt_of_le_of_ne (fun a ha => ⟨ha.1, fun z hz => ha.2 z (Finset.mem_insert_of_mem hz)⟩) ?_
    intro heq
    have hmem : ψ ∈ K t := ⟨hψ, h0⟩
    rw [← heq] at hmem
    exact hy (hmem.2 y (Finset.mem_insert_self y t))
  have h1 : f (insert y t) < f t := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : f t ≤ f (insert y t) := Function.argmin_le f _
  omega

theorem bound_of_injective {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ]
    (hm : ∀ ψ ∈ Ψ, MemLp ψ 2 μ) (hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[μ] 0 → ψ = 0) (y₀ : Y) :
    ∃ C : NNReal, ∀ ψ ∈ Ψ, ‖ψ y₀‖ₑ ^ 2 ≤ C * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
  let T : Ψ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun ψ => (hm ψ.1 ψ.2).toLp ψ.1
      map_add' := fun a b => MemLp.toLp_add (hm a.1 a.2) (hm b.1 b.2)
      map_smul' := fun c a => MemLp.toLp_const_smul c (hm a.1 a.2) }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ψ hψ
    have h0 : ψ.1 =ᵐ[μ] 0 := (MemLp.toLp_eq_toLp_iff (hm ψ.1 ψ.2) MemLp.zero).1 (by
      rw [MemLp.toLp_zero]; exact hψ)
    exact Subtype.ext (hinj ψ.1 ψ.2 h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hker
  let ev : Ψ →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ψ.1 y₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ℓ : LinearMap.range T →ₗ[ℂ] ℂ := (ev ∘ₗ g).domRestrict (LinearMap.range T)
  let L : LinearMap.range T →L[ℂ] ℂ := ⟨ℓ, LinearMap.continuous_of_finiteDimensional ℓ⟩
  refine ⟨‖L‖₊ ^ 2, fun ψ hψ => ?_⟩
  let p : Ψ := ⟨ψ, hψ⟩
  have hL : L ⟨T p, LinearMap.mem_range_self T p⟩ = ψ y₀ := by
    change ev (g (T p)) = ψ y₀
    have : g (T p) = p := LinearMap.congr_fun hg p
    rw [this]; rfl
  have hb : ‖ψ y₀‖₊ ≤ ‖L‖₊ * ‖T p‖₊ := by
    rw [← hL]
    exact L.le_opNNNorm _
  have hen : ‖T p‖ₑ = eLpNorm ψ 2 μ := Lp.enorm_toLp (hm ψ hψ)
  have hb' : ‖ψ y₀‖ₑ ≤ (‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ := by
    rw [← hen]
    simp only [enorm_eq_nnnorm]
    exact_mod_cast hb
  have hsq : eLpNorm ψ 2 μ ^ 2 = ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := ψ) (μ := μ) (p := 2) (by norm_num)
      (hm ψ hψ).aestronglyMeasurable
    simpa using this
  calc ‖ψ y₀‖ₑ ^ 2 ≤ ((‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ) ^ 2 := by gcongr
    _ = ((‖L‖₊ ^ 2 : NNReal) : ENNReal) * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
      rw [mul_pow, hsq]; push_cast; rfl

theorem interpolation_local_L2_bound : PositivityTheory.Rg.BcB.E.E3.InterpolationL2Bound := by
  intro X Y _ _ _ _ _ ν _ _ F hF hfin
  set Ψ : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (Set.range F) with hΨ
  haveI : FiniteDimensional ℂ Ψ := hfin
  have hc : ∀ ψ ∈ Ψ, Continuous ψ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hF i
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  obtain ⟨t, ht⟩ := exists_finset_separating Ψ
  choose N hNc hNn using fun y : Y => exists_compact_mem_nhds y
  have hΩ : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y _ => hNc y
  set Ω : Set Y := ⋃ y ∈ t, N y with hΩdef
  refine ⟨Ω, hΩ, fun y₀ => ?_⟩
  haveI : IsFiniteMeasure (ν.restrict Ω) := ⟨by simpa using hΩ.measure_lt_top⟩
  have hm : ∀ ψ ∈ Ψ, MemLp ψ 2 (ν.restrict Ω) := by
    intro ψ hψ
    obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (hc ψ hψ).continuousOn
    refine MemLp.of_bound (hc ψ hψ).aestronglyMeasurable B ?_
    have hmeas : MeasurableSet Ω := hΩ.measurableSet
    exact (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hB)
  have hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[ν.restrict Ω] 0 → ψ = 0 := by
    intro ψ hψ h0
    refine ht ψ hψ fun y hy => ?_
    have hsub : interior (N y) ⊆ Ω := interior_subset.trans (Set.subset_biUnion_of_mem (u := N) hy)
    have h1 : ψ =ᵐ[ν.restrict (interior (N y))] 0 :=
      ae_mono (Measure.restrict_mono hsub le_rfl) h0
    have h2 := Measure.eqOn_open_of_ae_eq h1 isOpen_interior (hc ψ hψ).continuousOn
      continuousOn_const
    exact h2 (mem_interior_iff_mem_nhds.2 (hNn y))
  obtain ⟨C, hC⟩ := bound_of_injective (ν.restrict Ω) Ψ hm hinj y₀
  exact ⟨C, fun x => hC (F x) (Submodule.subset_span ⟨x, rfl⟩)⟩

end GlobalTheory.CompanionTheory.InterpLoc
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FrobeniusUniformizerIdentity
namespace PositivityTheory.Rg.BcB.E.E3

theorem frobenius_uniformizer_identity (h : LocNonPosGlue) : PositivityTheory.Rg.BcB.E.E3 :=
  asm_holds fintype_holds (GlobalTheory.CompanionTheory.LocSlice.locSlGlue sizet_holds GlobalTheory.CompanionTheory.CentralMult.multC GlobalTheory.CompanionTheory.InterpLoc.interpolation_local_L2_bound)
    (h sizet_holds) centeig_holds (GlobalTheory.CompanionTheory.CentRe.centReGlue_holds sizet_holds GlobalTheory.CompanionTheory.CentralMult.multC) hullaut_holds
    GlobalTheory.CompanionTheory.HullExp.hullNonPos GlobalTheory.CompanionTheory.PairSpProof.pairSp

end PositivityTheory.Rg.BcB.E.E3
end

namespace PositivityTheory.Rg.BcB.E.E3

theorem etale_base_change_of_duality : PositivityTheory.Rg.BcB.E.E3 := frobenius_uniformizer_identity GlobalTheory.CompanionTheory.LocExponent.locNonPosGlue_holds

end PositivityTheory.Rg.BcB.E.E3
