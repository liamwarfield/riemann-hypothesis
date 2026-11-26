module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ProjOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesB
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopGap
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.CharZeroCompletion
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsUnitaryAbsPow
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.LFun GlobalTheory.CuspRep GlobalTheory.HeckeGal.Model

namespace GlobalTheory.Published.JacquetShalikaModel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
omit [_root_.NumberField.IsTotallyComplex E] in
theorem _root_.GlobalTheory.Published.JacquetShalikaModel.infinite_places : Infinite (HeightOneSpectrum (𝓞 E)) := by
  classical
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hfin : (Set.range fun P : HeightOneSpectrum (𝓞 E) =>
      Ideal.comap (algebraMap ℤ (𝓞 E)) P.asIdeal).Finite := Set.finite_range _
  apply Nat.infinite_setOf_prime
  have hinj : Set.InjOn (fun p : ℕ => Ideal.span {(p : ℤ)}) {p | p.Prime} := by
    intro p _ q _ hpq
    have := Ideal.span_singleton_eq_span_singleton.mp hpq
    rw [Int.associated_iff_natAbs] at this
    simpa using this
  refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
  rintro _ ⟨p, hp, rfl⟩
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQ, hlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hcomap : Ideal.comap (algebraMap ℤ (𝓞 E)) Q = Ideal.span {(p : ℤ)} :=
    (hlies.over).symm
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hmem : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) :=
      hcomap ▸ Ideal.subset_span rfl
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at hmem
    exact hp.ne_zero hmem
  exact ⟨⟨Q, hQ.isPrime, hne⟩, hcomap⟩

end GlobalTheory.Published.JacquetShalikaModel
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscAllOfRest
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStages
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesC
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d N : ℕ}

theorem tw_unip_inv {h : ∑ _ : Fin d, a = N} {fam : Fin d → CuspSub E a} {z : ℂ} {F : Sm E N}
    (hF : F ∈ tw (indForms h fam) z) : ∀ u ∈ unipRad (Ad E) (stdBlocks (fun _ : Fin d => a) h), ∀ g, F.1 (u * g) = F.1 g := by
  obtain ⟨G, hG, rfl⟩ := hF
  intro u hu g
  have h1 : chiDet N (Model.absC E z) u = 1 := by
    simp only [chiDet, MonoidHom.comp_apply, det_eq_one_of_mem_unipRad (Ad E) hu, map_one]
  change (mulChi N (Model.absC E z) G).1 (u * g) = (mulChi N (Model.absC E z) G).1 g
  rw [mulChi_apply, mulChi_apply, hG.1 u hu g, map_mul, h1, one_mul]

theorem tw_slice_mem {h : ∑ _ : Fin d, a = N} {fam : Fin d → CuspSub E a} {z : ℂ} {F : Sm E N}
    (hF : F ∈ tw (indForms h fam) z) :
    (fun m : Fin d → GA E a => F.1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d => a) h) m)) ∈
      tensorForms (n := fun _ => a) (fun b => (fam b).twist (Model.absC E z)) := by
  obtain ⟨G, hG, rfl⟩ := hF
  have h1 := tensorForms_mulChi fam (Model.absC E z) (hG.2.2.2 1 1)
  convert h1 using 1
  funext m
  change (mulChi N (Model.absC E z) G).1 _ = _
  rw [mulChi_apply, chiDet_leviEmb]
  simp

variable {r s d₁ d₂ : ℕ}

theorem mem_indForms_of_slices (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    {fam₁ : Fin d₁ → CuspSub E a} {fam₂ : Fin d₂ → CuspSub E a} {fam : Fin (d₁ + d₂) → CuspSub E a} {z₁ z₂ : ℂ}
    (he₁ : ∀ b, fam (Fin.castAdd d₂ b) = (fam₁ b).twist (Model.absC E z₁))
    (he₂ : ∀ b, fam (Fin.natAdd d₁ b) = (fam₂ b).twist (Model.absC E z₂)) {Φ : Sm E (r + s)}
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, Φ.1 (unip x * g) = Φ.1 g)
    (hsl : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (F₁ : Fin n → Sm E r) (F₂ : Fin n → Sm E s),
      (∀ i, F₁ i ∈ tw (indForms h₁ fam₁) z₁) ∧ (∀ i, F₂ i ∈ tw (indForms h₂ fam₂) z₂) ∧
      ∀ m : GA E r × GA E s, Φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (F₁ i).1 m.1 * (F₂ i).1 m.2)
    (hsm : Φ ∈ GlobalTheory.PRep.smoothPart (finRep E (r + s))) (hfv : Φ ∈ finVec (cptRep E (r + s))) :
    Φ ∈ indForms H fam := by
  have key : ∀ w ∈ unipRad (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H), ∀ (m : Fin (d₁ + d₂) → GA E a)
      (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      Φ.1 (w * leviEmb (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m *
        (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
      Φ.1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m *
        (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) := by
    intro w hw m k g
    obtain ⟨x, w₁, w₂, hw₁, hw₂, rfl⟩ := unipRad_split h₁ h₂ H hw
    obtain ⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩ := hsl k g
    rw [leviEmb_split h₁ h₂ H, mul_assoc (unip x), ← map_mul, Prod.mk_mul_mk, mul_assoc, hu, hΦ, hΦ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tw_unip_inv (hF₁ i) w₁ hw₁, tw_unip_inv (hF₂ i) w₂ hw₂]
  refine ⟨fun u hu g' => ?_, hsm, hfv, fun k g => ?_⟩
  · obtain ⟨u', hu', m, k, gf, rfl⟩ := GlobalTheory.IwasawaAdelic.iwasawa E (fun _ => a) H g'
    have e : ∀ X Y Z W : GA E (r + s), X * (Y * Z * W) = X * Y * Z * W := fun _ _ _ _ => by simp only [mul_assoc]
    rw [e, key _ (mul_mem hu hu'), key _ hu']
  · obtain ⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩ := hsl k g
    have hmem : ∀ i, (fun m : Fin (d₁ + d₂) → GA E a =>
        (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) (fun b => m (Fin.castAdd d₂ b))) *
        (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) (fun b => m (Fin.natAdd d₁ b)))) ∈
          tensorForms (n := fun _ => a) fam := by
      intro i
      have e₁ : (fun b => fam (Fin.castAdd d₂ b)) = fun b => (fam₁ b).twist (Model.absC E z₁) := funext he₁
      have e₂ : (fun b => fam (Fin.natAdd d₁ b)) = fun b => (fam₂ b).twist (Model.absC E z₂) := funext he₂
      refine tensorForms_append fam
        (G₁ := fun m₁ => (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) m₁))
        (G₂ := fun m₂ => (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) m₂)) ?_ ?_
      · rw [e₁]; exact tw_slice_mem (hF₁ i)
      · rw [e₂]; exact tw_slice_mem (hF₂ i)
    convert Submodule.sum_mem _ (fun i _ => hmem i) using 1
    funext m
    rw [Finset.sum_apply, leviEmb_split h₁ h₂ H, hΦ]

end PositivityTheory.Rg.Rs.InductionInStages

end
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

open InductionInStages ParabolicProjection in
theorem stages_of (hI : IndMap) : Stages := by
  intro E _ _ _ r s a d₁ d₂ V V₁ V₂ π hV hV₁ hV₂ hemb h₁ h₂
  obtain ⟨T, hTmem, hTinj, hTeq⟩ := hemb
  obtain ⟨hs₁, ν₁, hν₁, f₁, hf₁mem, hf₁inj, hf₁eq⟩ := h₁
  obtain ⟨hs₂, ν₂, hν₂, f₂, hf₂mem, hf₂inj, hf₂eq⟩ := h₂
  set z₁ : ℂ := ((s : ℂ) - d₂) / 2 with hz₁
  set z₂ : ℂ := ((d₁ : ℂ) - r) / 2 with hz₂
  obtain ⟨T', hT'eq, hT'u, hT'sl⟩ := hI E r s V (tw V₁ z₁) (tw V₂ z₂) T (twMap r z₁ f₁) (twMap s z₂ f₂) hV.stable hV.aut
    (isStable_tw hV₁.stable z₁) (isStable_tw hV₂.stable z₂) hTeq hTmem (twMap_equiv hV₁.stable hf₁eq)
    (twMap_equiv hV₂.stable hf₂eq)
  have hr : r = d₁ * a := sum_const_eq hs₁
  have hs : s = d₂ * a := sum_const_eq hs₂
  have H : ∑ _ : Fin (d₁ + d₂), a = r + s := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; rw [hr, hs]; ring
  let ν : Fin (d₁ + d₂) → HChar E := fun i =>
    Model.absC E ((-spehExp (d₁ + d₂) i + a * spehExp (d₁ + d₂) i : ℝ) : ℂ)

  have hsl : ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r)
      (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ tw V₁ z₁) ∧ (∀ i, ψ₂ i ∈ tw V₂ z₂) ∧
      (∀ m : GA E r × GA E s, (T φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∧
      ∀ m : GA E r × GA E s, (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (twMap r z₁ f₁ (ψ₁ i)).1 m.1 * (twMap s z₂ f₂ (ψ₂ i)).1 m.2 := by
    intro φ hφ k g
    obtain ⟨n, ψ₁, ψ₂, h1, h2, he⟩ := tensor_pair_finite_sum ((hTmem φ hφ).2 k g)
    exact ⟨n, ψ₁, ψ₂, h1, h2, he, hT'sl φ hφ k g n ψ₁ ψ₂ h1 h2 he⟩
  refine ⟨H, ν, fun i => isAbsPow_absC _, T', fun φ hφ => ?_, ?_, hT'eq⟩
  · refine mem_indForms_of_slices hs₁ hs₂ H (fam₁ := fun b => π.twist (ν₁ b)) (fam₂ := fun b => π.twist (ν₂ b))
      (z₁ := z₁) (z₂ := z₂) (fun b => ?_) (fun b => ?_) (hT'u φ hφ) (fun k g => ?_) ?_ ?_
    · rw [← CuspSub.twist_mul, eq_absC (hν₁ b), absC_mul]
      refine congrArg (fun x => π.twist (Model.absC E x)) ?_
      simp only [spehExp, Fin.val_castAdd, hz₁, hs]
      push_cast; ring
    · rw [← CuspSub.twist_mul, eq_absC (hν₂ b), absC_mul]
      refine congrArg (fun x => π.twist (Model.absC E x)) ?_
      simp only [spehExp, Fin.val_natAdd, hz₂, hr]
      push_cast; ring
    · obtain ⟨n, ψ₁, ψ₂, h1, h2, -, he⟩ := hsl φ hφ k g
      exact ⟨n, fun i => twMap r z₁ f₁ (ψ₁ i), fun i => twMap s z₂ f₂ (ψ₂ i), fun i => twMap_mem hf₁mem _ (h1 i),
        fun i => twMap_mem hf₂mem _ (h2 i), he⟩
    · refine isOpen_stab_of_mem_nhds (finRep E (r + s)) (T' φ) (Filter.mem_of_superset
        ((hV.aut φ hφ).level.mem_nhds (by simp)) fun k hk => ?_)
      have hk' : finRep E (r + s) k φ = φ := hk
      exact (hT'eq (.fin k) φ hφ).symm.trans (congrArg T' hk')
    · have := (hV.aut φ hφ).kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)).map T')
        (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, hT'eq (.cpt k) φ hφ⟩
  · obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := (Submodule.ne_bot_iff V).1 hV.ne_bot
    refine inj_of_irred hV hT'eq ⟨φ₀, hφ₀, fun h0 => ?_⟩
    have hTne : T φ₀ ≠ 0 := fun h => hφ₀ne (hTinj φ₀ hφ₀ h)
    obtain ⟨k, g, m, hne⟩ := exists_slice_ne hTne (hTmem φ₀ hφ₀).1
    obtain ⟨n, ψ₁, ψ₂, h1, h2, he, he'⟩ := hsl φ₀ hφ₀ k g
    rw [he m] at hne
    have hθ₁ := sum_left_ne hne
    have hθ₁m : ∑ i, (ψ₂ i).1 m.2 • ψ₁ i ∈ tw V₁ z₁ := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i)
    obtain ⟨b₁, hb₁⟩ := step_left (twMap r z₁ f₁) (fun h => hθ₁ (twMap_ne hf₁inj _ hθ₁m h))
    have hθ₂ := sum_right_ne (ψ₁ := fun i => twMap r z₁ f₁ (ψ₁ i)) hb₁
    have hθ₂m : ∑ i, (twMap r z₁ f₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw V₂ z₂ :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h2 i)
    obtain ⟨b₂, hb₂⟩ := step_right (twMap s z₂ f₂) (fun h => hθ₂ (twMap_ne hf₂inj _ hθ₂m h))
    refine hb₂ ?_
    have := he' (b₁, b₂)
    rw [h0] at this
    exact this.symm

end PositivityTheory.Rg.Rs

end
end

namespace PositivityTheory.Rg.Rs

theorem ascAll_of_rest (hS : Slice) (hP : Pr) (hI : IndMap) (hT : StringStep) : AscAll :=
  ascAll_of (dich_of dict_holds finTr_holds killPoly_holds) (expFin_of dict_holds finTr_holds) expNeg_holds hS
    (chord_of expTw_holds sqIntCrit_holds) (proj_of hP sliceTens_holds hI) infInd2_holds hT (stages_of hI)

end PositivityTheory.Rg.Rs
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsOpenStabTw
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs

namespace SatakeInductionStabiliserOpen

open SatakeVectors PInfInd2A

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem isOpen_stab_tw {m : ℕ} {V : Submodule ℂ (Sm E m)} (hV : IsDiscrete V) (z : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    ∀ ψ ∈ tw V z, IsOpen {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) ψ = ψ} := by
  intro ψ hψ
  obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hψ
  set χ := Model.absC E z
  have hA : IsOpen {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) φ = φ} :=
    (hV.aut φ hφ).level.preimage (CuspSub.continuous_locGL w)
  have hC := CuspSub.isOpen_ker_locDet (a := m) χ w
  let H : Subgroup (GL (Fin m) (w.adicCompletion E)) :=
    { carrier := {g | finRep E m (locGL E m w g) (mulChi m χ φ) = mulChi m χ φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change finRep E m (locGL E m w (a * b)) _ = _
        rw [map_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change finRep E m (locGL E m w a⁻¹) _ = _
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply] }
  have hsub : {g : GL (Fin m) (w.adicCompletion E) | finRep E m (locGL E m w g) φ = φ} ∩
      {g | CuspSub.locDet m χ w g = 1} ⊆ (H : Set _) := fun g hg => by
    change finRep E m (locGL E m w g) (mulChi m χ φ) = mulChi m χ φ
    rw [finRep_mulChi]
    have e1 : χ.loc w (Matrix.GeneralLinearGroup.det g) = 1 := hg.2
    rw [e1, Units.val_one, one_smul, hg.1]
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset ((hA.inter hC).mem_nhds
    ⟨(by simp : finRep E m (locGL E m w 1) φ = φ), by simp⟩) hsub)

def blkS (B₁ B₂ : Multiset ℂˣ) : Fin 2 → Multiset ℂˣ
  | ⟨0, _⟩ => B₁
  | ⟨1, _⟩ => B₂

end SatakeInductionStabiliserOpen

open SatakeVectors SatakeInductionStabiliserOpen PInfInd2A in
theorem satInd2_holds : SatInd2 := by
  intro E _ _ _ r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb
  filter_upwards [eventually_satV hV, eventually_satV hV₁, eventually_satV hV₂] with w hB hB₁ hB₂
  obtain ⟨B, hB⟩ := hB
  obtain ⟨B₁, hB₁⟩ := hB₁
  obtain ⟨B₂, hB₂⟩ := hB₂
  refine ⟨B, B₁, B₂, hB, hB₁, hB₂, ?_⟩
  obtain ⟨f, hfP, hfi, hfe⟩ := hemb
  obtain ⟨φ, hφ, hsat⟩ := hB.1
  have hF0 : f φ ≠ 0 := fun e => hsat.1 (hfi φ hφ e)

  have hsatD : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφ⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E (r + s)).comp (locGL E (r + s) w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective hsat
  have hFB : GlobalTheory.LFun.IsSatVecGL w ((finRep E (r + s)).comp (locGL E (r + s) w)) (f φ) B :=
    hsatD.map (f ∘ₗ V.subtype) (fun g v => hfe (.fin (locGL E (r + s) w g)) v.1 v.2) hF0
  have hFK : ∀ k ∈ GlobalTheory.LFun.KGL w (n := (r + s)), finRep E (r + s) (locGL E (r + s) w k) (f φ) = f φ := fun k hk =>
    GlobalTheory.LGrp.mem_fixed.1 hFB.2.1 k hk
  have h : ∑ i, (![r, s] : Fin 2 → ℕ) i = r + s := GlobalTheory.CompanionTheory.CTFin.CapFactor.two_sum _
  have hcore := isSatVecGL_of_ind (n := ![r, s]) h (blkV (tw V₁ z₁) (tw V₂ z₂))
    (fun i => by fin_cases i
                 · exact fun g ψ hψ => ParabolicProjection.isStable_tw hV₁.stable z₁ (.fin g) ψ hψ
                 · exact fun g ψ hψ => ParabolicProjection.isStable_tw hV₂.stable z₂ (.fin g) ψ hψ)
    (fun i => by fin_cases i
                 · exact isOpen_stab_tw hV₁ z₁ w
                 · exact isOpen_stab_tw hV₂ z₂ w)
    (blkS (B₁.map (· * qU w (-z₁))) (B₂.map (· * qU w (-z₂))))
    (fun i => by fin_cases i
                 · exact satLike_tw (satLike_of_satV hB₁) z₁
                 · exact satLike_tw (satLike_of_satV hB₂) z₂)
    hF0 hFK
    (fun u hu g => by
      obtain ⟨x, rfl⟩ := GlobalTheory.CompanionTheory.CTFin.CapFactor.exists_unip_of_mem ![r, s] h hu
      exact (hfP φ hφ).1 x g)
    (fun k g => by
      have := tensorSp_of_tens2 (n := ![r, s]) (tw V₁ z₁) (tw V₂ z₂) ((hfP φ hφ).2 k g)
      convert this using 2 with m
      have e := GlobalTheory.CompanionTheory.CTFin.CapFactor.lev_eq_leviEmb (![r, s]) h (m 0, m 1)
      rw [levPair_eta] at e
      exact congrArg (fun x => (f φ).1 (x * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) e.symm)
  have hBeq := GlobalTheory.LFun.IsSatVecGL.unique hFB hcore
  have q0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot
  rw [hBeq, Fin.sum_univ_two, Multiset.map_add (f := _)]
  congr 1
  · change ((B₁.map (· * qU w (-z₁))).map (· * qU w ((modExp (fun i => Fin (![r, s] i)) 0 : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = _
    rw [GlobalTheory.CompanionTheory.CTFin.CapFactor.modExp_zero, satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, qU_val]
    rw [mul_assoc, ← Complex.cpow_add _ _ q0]
    congr 2
    simp
    ring
  · change ((B₂.map (· * qU w (-z₂))).map (· * qU w ((modExp (fun i => Fin (![r, s] i)) 1 : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = _
    rw [GlobalTheory.CompanionTheory.CTFin.CapFactor.modExp_one, satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, qU_val]
    rw [mul_assoc, ← Complex.cpow_add _ _ q0]
    congr 2
    simp
    ring

end PositivityTheory.Rg.Rs

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PLocDual
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Cos

namespace PositivityTheory.Rg.Rs

namespace PLocDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem basis (N : ℕ) : ∀ U ∈ nhds (1 : GL (Fin N) k), ∃ K : Subgroup (GL (Fin N) k),
    IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) ∧ (K : Set (GL (Fin N) k)) ⊆ U :=
  fun U hU => by
    obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin N) U hU
    exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem contraMap_surjective {N : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ (GL (Fin N) k) X} {τ : Representation ℂ (GL (Fin N) k) Y} (hσ : IsSmooth σ)
    (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Surjective (GlobalTheory.ContraRefl.contraMap f) := by
  intro l
  obtain ⟨K, ho, hc, hKs⟩ := basis N _ ((isSmooth_contra σ l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra σ) K := GlobalTheory.ContraRefl.mem_fix.2 fun h hh => hKs hh
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f.toLinearMap (LinearMap.ker_eq_bot.2 hf)
  obtain ⟨l', h1, h2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hτ ho hc
    (((l : Module.Dual ℂ X) ∘ₗ g) ∘ₗ (fixed τ K).subtype)
  have hl'K : l' ∈ fixed (contra τ) K := GlobalTheory.ContraRefl.mem_fix.2 h1
  refine ⟨l', Subtype.ext (GlobalTheory.ContraRefl.form_ext hσ hc (fun h hh w => ?_) (fun h hh w => ?_) fun w hw => ?_)⟩
  · show (l' : Module.Dual ℂ Y) (f (σ h w)) = (l' : Module.Dual ℂ Y) (f w)
    rw [f.isIntertwining]
    exact GlobalTheory.ContraRefl.invariant_of_fixed ⟨l', hl'K⟩ h hh (f w)
  · exact GlobalTheory.ContraRefl.invariant_of_fixed ⟨l, hlK⟩ h hh w
  · have hfw : f w ∈ fixed τ K := GlobalTheory.ContraRefl.mem_fix.2 fun h hh => by
      rw [← f.isIntertwining]
      exact congrArg f (GlobalTheory.ContraRefl.mem_fix.1 hw h hh)
    show (l' : Module.Dual ℂ Y) (f w) = (l : Module.Dual ℂ X) w
    have e1 := h2 ⟨f w, hfw⟩
    have e2 := LinearMap.congr_fun hg w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e2
    rw [show f w = ((⟨f w, hfw⟩ : fixed τ K) : Y) from rfl, e1]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg _ e2

def untwist {N : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {π : Representation ℂ (GL (Fin N) k) X} {σ : Representation ℂ (GL (Fin N) k) Y}
    (q : π.IntertwiningMap (σ.comp (thetaW k N))) : Representation.IntertwiningMap (π.comp (thetaW k N)) σ where
  toLinearMap := q.toLinearMap
  isIntertwining' g := by
    ext x
    have h := q.isIntertwining _ _ (thetaW k N g) x
    simp only [MonoidHom.comp_apply, GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW] at h
    exact h

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩


set_option maxHeartbeats 2000000 in
theorem exists_surjective_rev {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (σ : GlobalTheory.CuspRep.SmIrr (GL (Fin N) k)) (f : σ.ρ.IntertwiningMap (prodIrr x hd)) (hf : f ≠ 0) :
    ∃ hd' : ∑ a, (x (Fin.rev a)).1 = N,
      ∃ g : (prodIrr (fun a => x (Fin.rev a)) hd').IntertwiningMap σ.ρ, Function.Surjective g := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hGK : GKLocal k := GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA
  have hinj : Function.Injective f := GlobalTheory.DiscreteSpectrumCM.injective_of_irreducible σ.irred f fun e =>
    hf (Representation.IntertwiningMap.ext e)
  obtain ⟨hd1, ⟨E1⟩⟩ := GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr hA x hd
  have hs := contraMap_surjective σ.smooth (isSmooth_prodIrr x hd) f hinj
  obtain ⟨E2⟩ := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra hGK N σ.ρ σ.smooth σ.irred
  let q : (prodIrr (fun a => dualCl (x a)) hd1).IntertwiningMap (σ.ρ.comp (thetaW k N)) :=
    (E2.symm.toIntertwiningMap.comp (GlobalTheory.ContraRefl.contraMap f)).comp E1.symm.toIntertwiningMap
  have hq : Function.Surjective q :=
    E2.symm.toLinearEquiv.surjective.comp (hs.comp E1.symm.toLinearEquiv.surjective)
  obtain ⟨hd2, ⟨E3⟩⟩ := GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW hA hGK (fun a => dualCl (x a)) hd1
  have e : (fun a => dualCl (dualCl (x (Fin.rev a)))) = fun a => x (Fin.rev a) :=
    funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA _
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  obtain ⟨E4⟩ := prodIrr_congr e hd2 hd'
  exact ⟨hd', ((untwist q).comp E3.symm.toIntertwiningMap).comp E4.symm.toIntertwiningMap,
    (hq.comp E3.symm.toLinearEquiv.surjective).comp E4.symm.toLinearEquiv.surjective⟩

end PLocDual

set_option maxHeartbeats 2000000 in
open PLocDual in
theorem locDual_holds : LocDual := by
  intro k _ _ _ _ _ N d x σ' _ _ hd f hf
  obtain ⟨hd', g, hg⟩ := exists_surjective_rev (fun i : Fin d => spehFactor x d i.rev) hd σ' f hf
  have e : (fun a : Fin d => spehFactor x d (Fin.rev (Fin.rev a))) = spehFactor x d :=
    funext fun a => by rw [Fin.rev_rev]
  have hd'' : ∑ i, (spehFactor x d i).1 = N := by simpa only [Fin.rev_rev] using hd'
  obtain ⟨E⟩ := prodIrr_congr e hd' hd''
  exact ⟨hd'', g.comp E.symm.toIntertwiningMap, hg.comp E.symm.toLinearEquiv.surjective⟩

end PositivityTheory.Rg.Rs

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStep
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepD
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Rs.StrStepD

def strSet (c₁ c₂ : ℝ) (d₁ d₂ : ℕ) : Set ℝ :=
  {x | (∃ i : ℕ, i < d₁ ∧ x = c₁ + ((d₁ : ℝ) - 1) / 2 - i) ∨ ∃ j : ℕ, j < d₂ ∧ x = c₂ + ((d₂ : ℝ) - 1) / 2 - j}

theorem mem_strSet {c₁ c₂ x : ℝ} {d₁ d₂ : ℕ} :
    x ∈ strSet c₁ c₂ d₁ d₂ ↔ (∃ i : Fin d₁, x = c₁ + spehExp d₁ i) ∨ ∃ j : Fin d₂, x = c₂ + spehExp d₂ j := by
  simp only [strSet, Set.mem_setOf_eq, spehExp]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨⟨i, hi⟩, by simp only; ring⟩
    · exact Or.inr ⟨⟨j, hj⟩, by simp only; ring⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨i, i.2, by ring⟩
    · exact Or.inr ⟨j, j.2, by ring⟩

theorem of_infChar (m m₀ : Multiset ℂ) {d₁ d₂ : ℕ} (c₁ c₂ : ℝ)
    (hm : m = (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + (c₁ : ℂ)) +
      (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + (c₂ : ℂ)))
    (hne : m₀ ≠ 0) (hnd : m.Nodup) (hint : ∀ x ∈ m, ∀ y ∈ m, ∃ n : ℤ, x - y = n) :
    (∀ i j : ℕ, i < d₁ → j < d₂ → c₁ + ((d₁ : ℝ) - 1) / 2 - i ≠ c₂ + ((d₂ : ℝ) - 1) / 2 - j) ∧
      ∀ u ∈ strSet c₁ c₂ d₁ d₂, ∀ v ∈ strSet c₁ c₂ d₁ d₂, ∃ n : ℤ, u - v = n := by
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hne
  have h1 : ∀ i : Fin d₁, t + (spehExp d₁ i : ℂ) + c₁ ∈
      (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + (c₁ : ℂ)) := fun i =>
    Multiset.mem_map.2 ⟨t + spehExp d₁ i, Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Multiset.mem_map.2 ⟨t, ht, rfl⟩⟩, rfl⟩
  have h2 : ∀ j : Fin d₂, t + (spehExp d₂ j : ℂ) + c₂ ∈
      (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + (c₂ : ℂ)) := fun j =>
    Multiset.mem_map.2 ⟨t + spehExp d₂ j, Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, Multiset.mem_map.2 ⟨t, ht, rfl⟩⟩, rfl⟩
  have hnd' := hm ▸ hnd
  rw [Multiset.nodup_add] at hnd'
  have key : ∀ u ∈ strSet c₁ c₂ d₁ d₂, t + (u : ℂ) ∈ m := by
    intro u hu
    rw [mem_strSet] at hu
    rw [hm]
    rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine Multiset.mem_add.2 (Or.inl ?_)
      convert h1 i using 1
      push_cast; ring
    · refine Multiset.mem_add.2 (Or.inr ?_)
      convert h2 j using 1
      push_cast; ring
  refine ⟨fun i j hi hj e => ?_, fun u hu v hv => ?_⟩
  · have e' : t + (spehExp d₁ ⟨i, hi⟩ : ℂ) + c₁ = t + (spehExp d₂ ⟨j, hj⟩ : ℂ) + c₂ := by
      have e2 := congrArg (fun r : ℝ => (r : ℂ)) e
      simp only [spehExp] at e2 ⊢
      push_cast at e2 ⊢
      linear_combination e2
    exact Multiset.disjoint_left.1 hnd'.2.2 (h1 ⟨i, hi⟩) (e' ▸ h2 ⟨j, hj⟩)
  · obtain ⟨n, hn⟩ := hint _ (key u hu) _ (key v hv)
    refine ⟨n, ?_⟩
    have : ((u - v : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by push_cast; linear_combination hn
    exact_mod_cast this

theorem mem_sat (q : ℂ) (B : Multiset ℂ) {d₁ d₂ : ℕ} (c₁ c₂ : ℝ) (z : ℂ) :
    z ∈ (∑ i : Fin d₁, B.map (fun b => b * q ^ (-((c₁ : ℂ) + (spehExp d₁ i : ℂ))))) +
        ∑ j : Fin d₂, B.map (fun b => b * q ^ (-((c₂ : ℂ) + (spehExp d₂ j : ℂ)))) ↔
      ∃ x ∈ strSet c₁ c₂ d₁ d₂, ∃ β ∈ B, z = β * q ^ (-(x : ℂ)) := by
  simp only [Multiset.mem_add, Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_map, mem_strSet]
  constructor
  · rintro (⟨i, β, hβ, rfl⟩ | ⟨j, β, hβ, rfl⟩)
    · exact ⟨c₁ + spehExp d₁ i, Or.inl ⟨i, rfl⟩, β, hβ, by push_cast; rfl⟩
    · exact ⟨c₂ + spehExp d₂ j, Or.inr ⟨j, rfl⟩, β, hβ, by push_cast; rfl⟩
  · rintro ⟨x, (⟨i, rfl⟩ | ⟨j, rfl⟩), β, hβ, rfl⟩
    · exact Or.inl ⟨i, β, hβ, by push_cast; rfl⟩
    · exact Or.inr ⟨j, β, hβ, by push_cast; rfl⟩

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem match_left {a₁ a₂ d₁ d₂ : ℕ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂)
    (hn₁ : IsNormalised π₁) (hn₂ : IsNormalised π₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ)
    (hp : (StrStepC.twL π₁ π₂ x y).Perm (StrStepC.twL π₁ π₂ (fun i => -conj (x i)) (fun j => -conj (y j))))
    (i : Fin d₁) :
    (∃ i', x i = -conj (x i')) ∨
      ∃ j, x i = -conj (y j) ∧ (⟨a₁, CG.mk π₁⟩ : Σ b, CG E b) = ⟨a₂, CG.mk π₂⟩ := by
  have hmem : (⟨a₁, (CG.mk π₁).twist (GlobalTheory.CuspRep.Model.absC E (x i))⟩ : Σ b, CG E b) ∈ StrStepC.twL π₁ π₂ x y :=
    List.mem_append.2 (Or.inl (List.mem_ofFn.2 ⟨i, rfl⟩))
  rcases List.mem_append.1 (hp.mem_iff.1 hmem) with h | h
  · obtain ⟨i', hi'⟩ := List.mem_ofFn.1 h
    exact Or.inl ⟨i', (StrStepB.match_twist ha₁ π₁ π₁ hn₁ hn₁ hi'.symm).1⟩
  · obtain ⟨j, hj⟩ := List.mem_ofFn.1 h
    obtain ⟨e1, e2⟩ := StrStepB.match_twist ha₁ π₁ π₂ hn₁ hn₂ hj.symm
    exact Or.inr ⟨j, e1, e2⟩

theorem match_right {a₁ a₂ d₁ d₂ : ℕ} (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂)
    (hn₁ : IsNormalised π₁) (hn₂ : IsNormalised π₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ)
    (hp : (StrStepC.twL π₁ π₂ x y).Perm (StrStepC.twL π₁ π₂ (fun i => -conj (x i)) (fun j => -conj (y j))))
    (j : Fin d₂) :
    (∃ j', y j = -conj (y j')) ∨
      ∃ i, y j = -conj (x i) ∧ (⟨a₂, CG.mk π₂⟩ : Σ b, CG E b) = ⟨a₁, CG.mk π₁⟩ := by
  have hmem : (⟨a₂, (CG.mk π₂).twist (GlobalTheory.CuspRep.Model.absC E (y j))⟩ : Σ b, CG E b) ∈ StrStepC.twL π₁ π₂ x y :=
    List.mem_append.2 (Or.inr (List.mem_ofFn.2 ⟨j, rfl⟩))
  rcases List.mem_append.1 (hp.mem_iff.1 hmem) with h | h
  · obtain ⟨i, hi⟩ := List.mem_ofFn.1 h
    obtain ⟨e1, e2⟩ := StrStepB.match_twist ha₂ π₂ π₁ hn₂ hn₁ hi.symm
    exact Or.inr ⟨i, e1, e2⟩
  · obtain ⟨j', hj'⟩ := List.mem_ofFn.1 h
    exact Or.inl ⟨j', (StrStepB.match_twist ha₂ π₂ π₂ hn₂ hn₂ hj'.symm).1⟩

end PositivityTheory.Rg.Rs.StrStepD

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.SdNormCpow
namespace PositivityTheory.Rg.Rs.StrStepA

theorem sd_norm_cpow (q : ℕ) (hq : 1 < q) (x : ℝ) : ‖(q : ℂ) ^ (-(x : ℂ))‖ = (q : ℝ) ^ (-x) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem step_down (q : ℕ) (hq : 1 < q) (B₀ : Multiset ℂ)
    (hB : ∀ β ∈ B₀, (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧ ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ)) {α : ℂ} (hα : α ∈ B₀)
    (S : Set ℝ) (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n) (M : Multiset ℂ)
    (hM : ∀ z, z ∈ M ↔ ∃ x ∈ S, ∃ β ∈ B₀, z = β * (q : ℂ) ^ (-(x : ℂ)))
    (hgap : ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) → M.count z ≤ M.count ((q : ℂ) * z))
    {u : ℝ} (hu : u ∈ S) (hu1 : 1 ≤ u) : u - 1 ∈ S := by
  have hQ : (1 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  set z : ℂ := α * (q : ℂ) ^ (-(u : ℂ)) with hz
  have hzM : z ∈ M := (hM z).2 ⟨u, hu, α, hα, rfl⟩
  have hnz : ‖z‖ = ‖α‖ * (q : ℝ) ^ (-u) := by rw [hz, norm_mul, sd_norm_cpow q hq]
  have hsmall : ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [hnz]
    have h1 : ‖α‖ * (q : ℝ) ^ (-u) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) :=
      mul_lt_mul_of_pos_right (hB α hα).2 (Real.rpow_pos_of_pos hQ0 _)
    have h2 : (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) = (q : ℝ) ^ (1 / 2 - u) := by
      rw [← Real.rpow_add hQ0]; ring_nf
    have h3 : (q : ℝ) ^ (1 / 2 - u) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
    linarith
  have hc1 : 0 < M.count z := Multiset.count_pos.2 hzM
  have hc2 : 0 < M.count ((q : ℂ) * z) := lt_of_lt_of_le hc1 (hgap z hsmall)
  obtain ⟨x, hx, β, hβ, e⟩ := (hM _).1 (Multiset.count_pos.1 hc2)
  have en : (q : ℝ) * (‖α‖ * (q : ℝ) ^ (-u)) = ‖β‖ * (q : ℝ) ^ (-x) := by
    have h := congrArg norm e
    rw [norm_mul, hnz, norm_mul, sd_norm_cpow q hq, Complex.norm_natCast] at h
    exact h
  have hβn : ‖β‖ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by
    have e1 : (q : ℝ) ^ (1 - u + x) = q * (q : ℝ) ^ (-u) * (q : ℝ) ^ x := by
      rw [Real.rpow_add hQ0, Real.rpow_sub hQ0, Real.rpow_one, Real.rpow_neg hQ0.le]
      field_simp
    have hxx : (q : ℝ) ^ (-x) * (q : ℝ) ^ x = 1 := by rw [← Real.rpow_add hQ0]; simp
    calc ‖β‖ = ‖β‖ * (q : ℝ) ^ (-x) * (q : ℝ) ^ x := by rw [mul_assoc, hxx, mul_one]
      _ = q * (‖α‖ * (q : ℝ) ^ (-u)) * (q : ℝ) ^ x := by rw [en]
      _ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by rw [e1]; ring
  obtain ⟨n, hn⟩ := hint x hx u hu
  have hk : 1 - u + x = ((n + 1 : ℤ) : ℝ) := by push_cast; linarith
  rw [hk, Real.rpow_intCast] at hβn
  obtain ⟨hb1, hb2⟩ := hB β hβ
  obtain ⟨ha1, ha2⟩ := hB α hα
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hQ0 _
  have hhalf : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) := by
    have h := (Real.rpow_add hQ0 (-(1 / 2) : ℝ) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; norm_num
  rcases lt_trichotomy (n + 1) 0 with hneg | hzero | hposn
  ·
    exfalso
    have hle : (q : ℝ) ^ (n + 1) ≤ (q : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hQ.le (by omega)
    have hzp : (0 : ℝ) < (q : ℝ) ^ (n + 1) := zpow_pos hQ0 _
    have : ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-1 : ℤ) := by
      rw [hβn]
      calc ‖α‖ * (q : ℝ) ^ (n + 1) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha2 hzp
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos hQ0 _).le
    rw [← hhalf, zpow_neg_one, mul_assoc, mul_inv_cancel₀ hQ0.ne', mul_one] at this
    linarith
  · have hx' : x = u - 1 := by
      have : (n : ℝ) = -1 := by exact_mod_cast (by omega : n = -1)
      linarith
    rw [← hx']; exact hx
  · exfalso
    have hle : (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (n + 1) := zpow_le_zpow_right₀ hQ.le (by omega)
    have : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) < ‖β‖ := by
      rw [hβn]
      calc (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hle hpos.le
        _ < ‖α‖ * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha1 (zpow_pos hQ0 _)
    rw [zpow_one, hhalf] at this
    linarith

end PositivityTheory.Rg.Rs.StrStepA
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepA
namespace PositivityTheory.Rg.Rs.StrStepA

theorem adjacent (c₁ c₂ : ℝ) (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (S : Set ℝ)
    (hS : ∀ x, x ∈ S ↔ (∃ i : ℕ, i < d₁ ∧ x = c₁ + ((d₁ : ℝ) - 1) / 2 - i) ∨
      ∃ j : ℕ, j < d₂ ∧ x = c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hdisj : ∀ i j : ℕ, i < d₁ → j < d₂ → c₁ + ((d₁ : ℝ) - 1) / 2 - i ≠ c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n)
    (hneg : ∀ x ∈ S, -x ∈ S) (hP : ∀ u ∈ S, 1 ≤ u → u - 1 ∈ S) (hc : c₁ < c₂) :
    c₂ - c₁ = ((d₁ : ℝ) + d₂) / 2 := by
  set e₁ : ℝ := ((d₁ : ℝ) - 1) / 2 with he₁
  set e₂ : ℝ := ((d₂ : ℝ) - 1) / 2 with he₂
  have hd₁' : (1 : ℝ) ≤ d₁ := by exact_mod_cast hd₁
  have hd₂' : (1 : ℝ) ≤ d₂ := by exact_mod_cast hd₂
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; linarith
  have he₂0 : 0 ≤ e₂ := by rw [he₂]; linarith
  have hcast₁ : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub hd₁]; simp
  have hcast₂ : ((d₂ - 1 : ℕ) : ℝ) = d₂ - 1 := by rw [Nat.cast_sub hd₂]; simp
  set B : ℝ := c₁ + e₁ with hBdef
  set C : ℝ := c₂ + e₂ - ((d₂ : ℝ) - 1) with hCdef
  have hB : B ∈ S := (hS _).2 (Or.inl ⟨0, hd₁, by simp [hBdef]⟩)
  have hC : C ∈ S := (hS _).2 (Or.inr ⟨d₂ - 1, by omega, by rw [hcast₂]⟩)
  have hmem : ∀ x ∈ S, x ≤ B ∨ C ≤ x := by
    intro x hx
    rcases (hS x).1 hx with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · left; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    · right
      have h1 : j ≤ d₂ - 1 := by omega
      have h2 : (j : ℝ) ≤ ((d₂ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hcast₂] at h2; linarith
  obtain ⟨n, hn⟩ := hint _ hC _ hB
  rcases lt_trichotomy n 1 with h | h | h
  · exfalso
    have hn0 : n ≤ 0 := by omega
    have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    by_cases hCA : c₁ - e₁ ≤ C
    · have hk : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have hk' : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by exact_mod_cast hk
      have hkd : (-n).toNat < d₁ := by
        have : (((-n).toNat : ℕ) : ℝ) < d₁ := by rw [hk']; linarith
        exact_mod_cast this
      refine hdisj (-n).toNat (d₂ - 1) hkd (by omega) ?_
      rw [hk', hcast₂]; linarith
    · rw [not_le] at hCA
      have hJ0 : (0 : ℤ) ≤ n + d₁ + d₂ - 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) + d₁ + d₂ - 2 := by linarith
        exact_mod_cast this
      have hJ1 : n + d₁ + d₂ - 2 < (d₂ : ℤ) := by
        have : (n : ℝ) + d₁ + d₂ - 2 < d₂ := by linarith
        exact_mod_cast this
      have hj : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℤ) = n + d₁ + d₂ - 2 := Int.toNat_of_nonneg hJ0
      have hj' : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℝ) = (n : ℝ) + d₁ + d₂ - 2 := by exact_mod_cast hj
      have hjd : (n + d₁ + d₂ - 2).toNat < d₂ := by omega
      refine hdisj (d₁ - 1) (n + d₁ + d₂ - 2).toNat (by omega) hjd ?_
      rw [hj', hcast₁]; linarith
  · subst h
    push_cast at hn
    linarith
  · exfalso
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
    have hC1 : C - 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hB1 : B + 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hClt : C < 1 := by
      by_contra h3; exact hC1 (hP _ hC (not_lt.1 h3))
    have hBgt : -1 < B := by
      by_contra h3; rw [not_lt] at h3
      have h4 := hneg _ (hP _ (hneg _ hB) (by linarith))
      exact hB1 (by convert h4 using 1; ring)
    linarith

end PositivityTheory.Rg.Rs.StrStepA
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Rs

theorem stringStep_of : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.JacquetShalikaBound → InfInd2 → InfAsc →
    SatInd2 → SatAsc → SatHerm → Gap → StringStep := by
  intro hR hJ hInf hIA hSI hSA hSH hG E _ _ _ r s hr hs V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ hτ hsum hre
    a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ h₁ hu₂ hn₂ h₂

  have hr₁ : d₁ * a₁ = r := by obtain ⟨h, -⟩ := h₁; simpa using h
  have hs₂ : d₂ * a₂ = s := by obtain ⟨h, -⟩ := h₂; simpa using h
  have hd₁ : 0 < d₁ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have hd₂ : 0 < d₂ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have ha₁ : 1 ≤ a₁ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have ha₂ : 1 ≤ a₂ := Nat.pos_of_ne_zero fun h => by subst h; omega

  have hexp := StrStepC.sat_expand hSI hSA hSH V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb π₁ π₂ ha₁ ha₂ hu₁ hn₁ hu₂ hn₂ h₁ h₂
  have hp₀ := StrStepC.perm_of hR π₁ π₂ ha₁ ha₂ (fun i : Fin d₁ => z₁ - (s : ℂ) / 2 + (spehExp d₁ i : ℂ))
    (fun j : Fin d₂ => z₂ + (r : ℂ) / 2 + (spehExp d₂ j : ℂ))
    (hexp.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)

  rcases StrStepD.match_left ha₁ ha₂ π₁ π₂ hn₁ hn₂ _ _ hp₀ ⟨d₁ - 1, by omega⟩ with ⟨i', hi'⟩ | ⟨j, hj, hcls⟩
  · exfalso
    have h := congrArg Complex.re hi'
    have hi : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [spehExp, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re,
      Complex.div_ofNat_re, Complex.natCast_re, hi] at h
    have : (0 : ℝ) ≤ (i' : ℕ) := Nat.cast_nonneg _
    linarith
  have him : z₁.im = z₂.im := by
    have h := congrArg Complex.im hj
    simpa [spehExp, map_ofNat, Complex.div_ofNat_im] using h
  have hsim := congrArg Complex.im hsum
  simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
    Complex.zero_im] at hsim
  have h1im : z₁.im = 0 := by
    have : ((r : ℝ) + s) * z₁.im = 0 := by rw [← him] at hsim; linarith
    rcases mul_eq_zero.1 this with h | h
    · have : (0 : ℝ) < r := by exact_mod_cast hr
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      linarith
    · exact h
  have h2im : z₂.im = 0 := him ▸ h1im
  obtain ⟨ha, hh⟩ := Sigma.mk.inj_iff.1 hcls
  subst ha
  have hmk : CG.mk π₁ = CG.mk π₂ := eq_of_heq hh
  have hiso : π₁.Iso π₂ := Quotient.exact hmk
  subst hr₁ hs₂

  obtain ⟨c₁, hc₁d⟩ : ∃ c : ℝ, c = z₁.re - ((d₂ * a₁ : ℕ) : ℝ) / 2 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂d⟩ : ∃ c : ℝ, c = z₂.re + ((d₁ * a₁ : ℕ) : ℝ) / 2 := ⟨_, rfl⟩
  have hc₁ : ((c₁ : ℝ) : ℂ) = z₁ - ((d₂ * a₁ : ℕ) : ℂ) / 2 := by
    apply Complex.ext <;> simp [hc₁d, h1im]
  have hc₂ : ((c₂ : ℝ) : ℂ) = z₂ + ((d₁ * a₁ : ℕ) : ℂ) / 2 := by
    apply Complex.ext <;> simp [hc₂d, h2im]

  obtain ⟨m, hm, hnd, hint⟩ := hτ
  obtain ⟨m₁, m₂, hm₁, hm₂, hme⟩ := hInf E _ _ V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ m hm
  obtain ⟨m₀, hm₀, hme₁⟩ := hIA E _ a₁ d₁ V₁ π₁ hV₁ h₁ τ m₁ hm₁
  obtain ⟨m₀', hm₀', hme₂⟩ := hIA E _ a₁ d₂ V₂ π₂ hV₂ h₂ τ m₂ hm₂
  have hm₀e : m₀' = m₀ := hm₀'.unique (hiso.hasInfChar hm₀)
  have hform : m = (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + ((c₁ : ℝ) : ℂ)) +
      (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + ((c₂ : ℝ) : ℂ)) := by
    rw [hme, hme₁, hme₂, hm₀e, hc₁, hc₂]
  have hne : m₀ ≠ 0 := by
    rintro rfl
    have h := hm.1
    rw [hform] at h
    simp at h
    linarith
  obtain ⟨hdisj, hintS⟩ := StrStepD.of_infChar m m₀ c₁ c₂ hform hne hnd hint

  have hexp' : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ, SatV V w BV ∧
      (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧
      BV.map (fun b : ℂˣ => (b : ℂ)) =
        (∑ i : Fin d₁, B₁.map fun b : ℂˣ =>
          (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((c₁ + spehExp d₁ i : ℝ) : ℂ))) +
          ∑ j : Fin d₂, B₂.map (fun b : ℂˣ =>
            (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((c₂ + spehExp d₂ j : ℝ) : ℂ))) ∧
      BV.map (fun b => (star b)⁻¹) = BV ∧ B₁.map (fun b => (star b)⁻¹) = B₁ ∧
        B₂.map (fun b => (star b)⁻¹) = B₂ := by
    refine hexp.mono fun w ⟨BV, B₁, B₂, h0, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h0, h1, h2, ?_, hh⟩
    rw [e]
    simp only [Complex.ofReal_add, hc₁, hc₂]
  have hp := StrStepC.perm_of hR π₁ π₂ ha₁ ha₁ (fun i : Fin d₁ => ((c₁ + spehExp d₁ i : ℝ) : ℂ))
    (fun j : Fin d₂ => ((c₂ + spehExp d₂ j : ℝ) : ℂ))
    (hexp'.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)
  have hneg : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, -u ∈ StrStepD.strSet c₁ c₂ d₁ d₂ := by
    intro u hu
    rcases StrStepD.mem_strSet.1 hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rcases StrStepD.match_left ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp i with ⟨i', e⟩ | ⟨j, e, -⟩
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inl ⟨i', by linarith⟩)
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inr ⟨j, by linarith⟩)
    · rcases StrStepD.match_right ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp j with ⟨j', e⟩ | ⟨i, e, -⟩
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inr ⟨j', by linarith⟩)
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inl ⟨i, by linarith⟩)

  have := GlobalTheory.Published.JacquetShalikaModel.infinite_places (E := E)
  obtain ⟨w, BV, B₁, B₂, hBV, hs₁, hs₂, e, -⟩ := hexp'.exists
  have hB₂ : B₂ = B₁ := by
    rw [← hmk] at hs₂
    exact hs₂.unique hs₁
  rw [hB₂] at e
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hM : ∀ z, z ∈ BV.map (fun b : ℂˣ => (b : ℂ)) ↔ ∃ x ∈ StrStepD.strSet c₁ c₂ d₁ d₂,
      ∃ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), z = β * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(x : ℂ)) := by
    intro z
    rw [e, ← StrStepD.mem_sat]
    simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_add]
  have hgap : ∀ z : ℂ, ‖z‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) →
      (BV.map fun b : ℂˣ => (b : ℂ)).count z ≤
        (BV.map fun b : ℂˣ => (b : ℂ)).count ((Ideal.absNorm w.asIdeal : ℂ) * z) :=
    fun z hz => hG E _ V hV w BV hBV z hz
  have hbound : ∀ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧
      ‖β‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    exact hJ E a₁ (CG.mk π₁) ((CG.isUnitary_mk π₁).2 hu₁) w B₁ hs₁ b hb
  obtain ⟨α, hα⟩ : ∃ α, α ∈ B₁.map (fun b : ℂˣ => (b : ℂ)) := by
    obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hs₁.card]; omega)
    exact ⟨_, Multiset.mem_map_of_mem _ hb⟩
  have hP : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, 1 ≤ u → u - 1 ∈ StrStepD.strSet c₁ c₂ d₁ d₂ :=
    fun u hu hu1 => StrStepA.step_down _ hq _ hbound hα _ hintS _ hM hgap hu hu1

  have hlin : (d₁ : ℝ) * c₁ + d₂ * c₂ = 0 := by
    have hsre := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, h1im, h2im, mul_zero,
      sub_zero, Complex.zero_re] at hsre
    have ha : (0 : ℝ) < a₁ := by exact_mod_cast ha₁
    have : (a₁ : ℝ) * (d₁ * c₁ + d₂ * c₂) = 0 := by
      rw [hc₁d, hc₂d]
      push_cast at hsre ⊢
      linear_combination hsre
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have hc₁n : c₁ < 0 := by rw [hc₁d]; linarith
  have hc₂p : 0 < c₂ := by
    have : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
    have : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
    nlinarith
  have hadj := StrStepA.adjacent c₁ c₂ d₁ d₂ hd₁ hd₂ (StrStepD.strSet c₁ c₂ d₁ d₂) (fun x => Iff.rfl) hdisj hintS
    hneg hP (by linarith)
  have hc₁v : c₁ = -(d₂ : ℝ) / 2 := by
    have h : ((d₁ : ℝ) + d₂) * (c₁ + d₂ / 2) = 0 := by linear_combination hlin - (d₂ : ℝ) * hadj
    rcases mul_eq_zero.1 h with h | h
    · have : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
      have : (0 : ℝ) ≤ d₂ := Nat.cast_nonneg _
      linarith
    · linarith
  have hc₂v : c₂ = (d₁ : ℝ) / 2 := by linarith
  push_cast at hc₁d hc₂d
  refine ⟨by rw [hmk], ?_, ?_⟩
  · apply Complex.ext
    · simp
      linarith
    · simp [h1im]
  · apply Complex.ext
    · simp
      linarith
    · simp [h2im]

end PositivityTheory.Rg.Rs

end
end

namespace PositivityTheory.Rg.Rs

theorem ascAll_holds : AscAll := by
  exact ascAll_of_rest (slice_of dict_holds finTr_holds) pr_holds indMap_holds
    (stringStep_of PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.AdelicQuotientData.jacquetShalika.2 infInd2_holds infAsc_holds
      satInd2_holds satAsc_holds satHerm_holds gap_holds)

theorem ascSeed_of_locSub (h : LocSub) : AscSeed := by
  exact ⟨ascAll_holds, C3.clause3Asc_holds h locDual_holds⟩

end PositivityTheory.Rg.Rs
