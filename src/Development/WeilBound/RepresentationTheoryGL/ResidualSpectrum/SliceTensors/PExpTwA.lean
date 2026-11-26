module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ExponentTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem card_places : ((Module.finrank ℚ E : ℕ) : ℂ) = 2 * (Fintype.card (InfinitePlace E) : ℂ) := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  push_cast; ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem chiDet_absC_val (a : ℕ) (s : ℂ) (g : GA E a) :
    ((chiDet a (Model.absC E s) g : ℂˣ) : ℂ) =
      Complex.exp (s * (GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g) : ℂ)) := rfl

theorem sum_ite_lt {N r : ℕ} (h : r ≤ N) (t : ℂ) :
    ∑ i : Fin N, (if (i : ℕ) < r then t else 0) = r * t := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then t else 0), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [show Finset.filter (fun x => x < r) (Finset.range N) = Finset.range r by ext x; simp; omega]
  simp

theorem det_aInf_apply {N r : ℕ} (h : r ≤ N) (t : ℝ) (w : InfinitePlace E) :
    ((Matrix.GeneralLinearGroup.det (aInf E N r t) : (Cinf E)ˣ) : Cinf E) w = Complex.exp ((r * t : ℝ) : ℂ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (Matrix.diagonal fun (i : Fin N) (_ : InfinitePlace E) => Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0)).det w = _
  rw [Matrix.det_diagonal, Finset.prod_apply, ← Complex.exp_sum, sum_ite_lt h]
  push_cast; rfl

theorem chiDet_aT {N r : ℕ} (h : r ≤ N) (z : ℂ) (t : ℝ) :
    ((chiDet N (Model.absC E z) (aT E N r t) : ℂˣ) : ℂ) = Complex.exp (z * r * (Module.finrank ℚ E : ℂ) * t) := by
  rw [chiDet_absC_val, aT, det_infGL, Model.logNorm_infId]
  simp only [det_aInf_apply h, Complex.norm_exp_ofReal, Real.log_exp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_places]
  congr 1
  push_cast; ring

theorem splitCentre_eq (a : ℕ) (t : ℝ) : splitCentre E a t = aT E a a t := by
  refine congrArg (infGL E a) (Units.ext ?_)
  change Matrix.scalar (Fin a) (expU fun _ : InfinitePlace E => (t : ℂ)).val = Matrix.diagonal _
  ext i j
  simp [Matrix.scalar_apply, expU]

end PositivityTheory.Rg.Rs.ExponentTwist
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

def LocSub : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  AscEmb V π d → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N) (w.adicCompletion E))), π.IsLocComp w σ → IsLocCompGL V w σ' →
    ∃ hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
      ∃ f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr
        (fun i : Fin d => GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd), f ≠ 0

def LocDual : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] (N d : ℕ) (x : GlobalTheory.LocGL.IrrGL (k := k)) (σ' : SmIrr (GL (Fin N) k)), IsUnitarisable x.rep → IsUnitarisable σ'.ρ →
  ∀ (hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor x d i.rev).1 = N)
    (f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr (fun i : Fin d => GlobalTheory.LocGL.spehFactor x d i.rev) hd)), f ≠ 0 →
    ∃ hd' : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N,
      ∃ g : (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd').IntertwiningMap σ'.ρ, Function.Surjective g

def Clause3Asc : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  π.IsUnitary → IsNormalised π → AscEmb V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
    GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

def AscSeed : Prop := AscAll ∧ Clause3Asc

end PositivityTheory.Rg.Rs

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem absNorm_cpow_ne_zero (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) ≠ 0 := by
  have h : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  exact fun e => h ((Complex.cpow_eq_zero_iff _ _).1 e).1

def qU (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂˣ :=
  Units.mk0 (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s) (absNorm_cpow_ne_zero w s)

@[simp] theorem qU_val (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    ((qU w s : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ s := rfl

def SatLike {m : ℕ} (U : Submodule ℂ (Sm E m)) (w : HeightOneSpectrum (𝓞 E)) (S : Multiset ℂˣ) : Prop :=
  ∀ ψ ∈ U, (∀ k ∈ GlobalTheory.LFun.KGL w (n := m), finRep E m (locGL E m w k) ψ = ψ) → ψ ≠ 0 →
    GlobalTheory.LFun.IsSatVecGL w ((finRep E m).comp (locGL E m w)) ψ S

theorem satLike_of_satV {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatV V w B) : SatLike V w B := h.2

theorem satTw_eq (w : HeightOneSpectrum (𝓞 E)) (z : ℂ) (B : Multiset ℂˣ) :
    satTw w z B = (B.map (· * qU w (-z))).map fun b : ℂˣ => (b : ℂ) := by
  simp [satTw, Multiset.map_map, Function.comp_def]

end PositivityTheory.Rg.Rs.SatakeVectors

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PAscAll
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

namespace PAscAll

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem regInt_of_le {n : ℕ} {V : Submodule ℂ (Sm E n)} {τ : E →+* ℂ} {m m₁ : Multiset ℂ} {z : ℂ}
    (hnd : m.Nodup) (hint : ∀ x ∈ m, ∀ y ∈ m, ∃ k : ℤ, x - y = k) (hle : m₁.map (· + z) ≤ m)
    (h : HasInfCharGL V τ m₁) : RegInt V τ := by
  refine ⟨m₁, h, (Multiset.nodup_of_le hle hnd).of_map _, fun x hx y hy => ?_⟩
  obtain ⟨k, hk⟩ := hint (x + z) (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hx))
    (y + z) (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  exact ⟨k, by rw [← hk]; ring⟩

theorem exists_extremal (hF : ExpFin) (hN : ExpNeg) {N : ℕ} (V : Submodule ℂ (Sm E N)) (hV : IsDiscrete V)
    (hne : ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty) :
    ∃ (r : ℕ) (c : ℂ) (lam : ℝ), 0 < r ∧ r < N ∧ c ∈ ExpV r V ∧ 0 < lam ∧
      pE E N r c = -lam * (r * ((N : ℝ) - r)) ∧
      ∀ m, 0 < m → m < N → ∀ c' ∈ ExpV m V, pE E N m c' ≤ -lam * (m * ((N : ℝ) - m)) := by
  set S : Set (ℕ × ℂ) := {p | 0 < p.1 ∧ p.1 < N ∧ p.2 ∈ ExpV p.1 V} with hSdef
  have hfin : S.Finite := by
    refine ((Set.finite_Ioo 0 N).biUnion fun r hr => (hF E N V hV r hr.1 hr.2).image (Prod.mk r)).subset ?_
    intro p hp
    exact Set.mem_iUnion₂.2 ⟨p.1, ⟨hp.1, hp.2.1⟩, p.2, hp.2.2, rfl⟩
  obtain ⟨r₀, hr₀, hr₀N, c₀, hc₀⟩ := hne
  have hD : ∀ m : ℕ, 0 < m → m < N → (0 : ℝ) < m * ((N : ℝ) - m) := fun m h0 h1 =>
    mul_pos (by exact_mod_cast h0) (sub_pos.2 (by exact_mod_cast h1))
  let f : ℕ × ℂ → ℝ := fun p => -pE E N p.1 p.2 / ((p.1 : ℝ) * ((N : ℝ) - p.1))
  obtain ⟨⟨r, c⟩, ⟨hr, hrN, hc⟩, hmin⟩ := Set.exists_min_image S f hfin ⟨(r₀, c₀), hr₀, hr₀N, hc₀⟩
  have hneg : pE E N r c < 0 := by
    obtain ⟨φ, hφ, hcφ⟩ := hc
    exact hN E N φ (hV.aut φ hφ) (hV.sqInt φ hφ) r hr hrN c hcφ
  refine ⟨r, c, f (r, c), hr, hrN, hc, div_pos (neg_pos.2 hneg) (hD r hr hrN), ?_, ?_⟩
  · simp only [f]
    rw [neg_mul, div_mul_cancel₀ _ (hD r hr hrN).ne', neg_neg]
  · intro m hm hmN c' hc'
    have h1 := (le_div_iff₀ (hD m hm hmN)).1 (hmin (m, c') ⟨hm, hmN, hc'⟩)
    linarith [neg_mul (f (r, c)) ((m : ℝ) * ((N : ℝ) - m))]

end PAscAll

theorem ascAll_of (hD : Dich) (hF : ExpFin) (hN : ExpNeg) (hS : Slice) (hC : Chord) (hP : Proj) (hI : InfInd2)
    (hSS : StringStep) (hSt : Stages) : AscAll := by
  intro E _ _ _ N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN1 V hV τ hτ
  rcases hD E N hN1 V hV with ⟨π, hu, hn, h⟩ | hne
  · exact ⟨N, 1, π, hu, hn, h⟩
  obtain ⟨r, c, lam, hr0, hrN, hc, hlam, hpc, hbd⟩ := PAscAll.exists_extremal hF hN V hV hne
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  have hs0 : 0 < s := by omega
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hdC : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hpc' : pE E (r + s) r c = -lam * (r * s) := by rw [hpc]; push_cast; ring
  obtain ⟨T, hT⟩ := hS E r s hr0 hs0 V hV c hc
  have hL2 := hC E r s hr0 hs0 V c T lam hlam hT hpc' hbd
  obtain ⟨V₁, V₂, hV₁, hV₂, hemb⟩ := hP E r s hr0 hs0 V hV c _ _ T hT hL2
  obtain ⟨m, hm, hnd, hint⟩ := hτ
  obtain ⟨m₁, m₂, hm₁, hm₂, he⟩ := hI E r s V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ m hm
  have hτ₁ : RegInt V₁ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_right _ _) hm₁
  have hτ₂ : RegInt V₂ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_left _ _) hm₂
  obtain ⟨a₁, d₁, π₁, hu₁, hn₁, h₁⟩ := ih r (by omega) hr0 V₁ hV₁ τ hτ₁
  obtain ⟨a₂, d₂, π₂, hu₂, hn₂, h₂⟩ := ih s (by omega) hs0 V₂ hV₂ τ hτ₂
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsum : (r : ℂ) * (c / (r * (Module.finrank ℚ E : ℂ))) + s * (-c / (s * (Module.finrank ℚ E : ℂ))) = 0 := by
    field_simp; ring
  have hre : (c / (r * (Module.finrank ℚ E : ℂ))).re < (s : ℝ) / 2 := by
    have e : (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((r : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [e, Complex.div_ofReal_re, div_lt_iff₀ (mul_pos hrR hd)]
    have h3 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * s / 2 := by
      have h4 := hpc'
      unfold pE at h4
      push_cast at h4
      nlinarith [mul_pos hlam (mul_pos hrR (show (0 : ℝ) < s by exact_mod_cast hs0))]
    rw [div_lt_iff₀ hd] at h3
    nlinarith
  obtain ⟨hsig, hz₁, hz₂⟩ := hSS E r s hr0 hs0 V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ ⟨m, hm, hnd, hint⟩ hsum hre
    a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ (h₁ π₁ (Setoid.refl π₁)) hu₂ hn₂ (h₂ π₂ (Setoid.refl π₂))
  obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.mp hsig
  have hiso : π₁.Iso π₂ := Quotient.exact (eq_of_heq hq)
  rw [hz₁, hz₂] at hemb
  refine ⟨a₁, d₁ + d₂, π₁, hu₁, hn₁, fun π' h' => ?_⟩
  exact hSt E r s a₁ d₁ d₂ V V₁ V₂ π' hV hV₁ hV₂ hemb (h₁ π' h') (h₂ π' ((CuspSub.setoid E a₁).iseqv.trans ((CuspSub.setoid E a₁).iseqv.symm hiso) h'))

end PositivityTheory.Rg.Rs

end
end
