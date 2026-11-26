module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCore

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrIrr
noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth
  GlobalTheory.LevelTypeProj GlobalTheory.PRep GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs.PrAdm

namespace PositivityTheory.Rg.Rs.PrIrr

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem isStable_sInf (S : Set (Submodule ℂ (Sm E N))) (hS : ∀ U ∈ S, _root_.GlobalTheory.CuspRep.IsStable U) : _root_.GlobalTheory.CuspRep.IsStable (sInf S) := by
  intro o φ hφ
  rw [Submodule.mem_sInf] at hφ ⊢
  exact fun U hU => hS U hU o φ (hφ U hU)

variable {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

def orthIn (V U : Submodule ℂ (Sm E N)) (hV : V ≤ W) : Submodule ℂ (Sm E N) where
  carrier := {x | x ∈ V ∧ ∀ u ∈ U, inner ℂ (cls h x) (cls h u) = 0}
  add_mem' := fun {x y} hx hy => ⟨V.add_mem hx.1 hy.1, fun u hu => by
    rw [cls_add h (hV hx.1) (hV hy.1), inner_add_left, hx.2 u hu, hy.2 u hu, add_zero]⟩
  zero_mem' := ⟨V.zero_mem, fun u _ => by
    rw [show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 W.zero_mem, zero_smul, inner_zero_left]⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, fun u hu => by
    rw [cls_smul h c (hV hx.1), inner_smul_left, hx.2 u hu, mul_zero]⟩

theorem exists_irr (hW : _root_.GlobalTheory.CuspRep.IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0)
    (hadj : ∀ o : Op E N, ∃ B : Module.End ℂ (Sm E N), (∀ U : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable U → ∀ u ∈ U, B u ∈ U) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (act o φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (B ψ)))
    {ψ : Sm E N} (hψW : ψ ∈ W) (hψ0 : ψ ≠ 0) :
    ∃ V : Submodule ℂ (Sm E N), _root_.GlobalTheory.CuspRep.IsStable V ∧ V ≤ SupSpansPsiPart W ψ ∧ V ≠ ⊥ ∧
      (∀ U ≤ V, _root_.GlobalTheory.CuspRep.IsStable U → U = ⊥ ∨ U = V) ∧ ∃ v ∈ V, inner ℂ (cls h ψ) (cls h v) ≠ 0 := by
  classical
  obtain ⟨L, hLo, hLc, hψT⟩ := exists_type (hA ψ hψW)
  have : FiniteDimensional ℂ (orbSpan ψ) := (hA ψ hψW).kfin
  have hρ := isContRep_sub (orbSpan ψ) (orbSpan_stable ψ)
  set ρ := sub (cptRep E N) (orbSpan ψ) (orbSpan_stable ψ)
  set T := typePart L ρ
  set A := SupSpansPsiPart W ψ
  have hAst : _root_.GlobalTheory.CuspRep.IsStable A := isStable_admissible_span hW ψ
  have hAW : A ≤ W := admissible_span_le W ψ
  have hfd : ∀ V' ≤ A, FiniteDimensional ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) := fun V' h' =>
    haveI := finiteDimensional_admissible_isotypic hA (hA ψ hψW) hLo ρ hρ
    Submodule.finiteDimensional_of_le (inf_le_inf_right T h')
  let Cand : Submodule ℂ (Sm E N) → Prop := fun V' =>
    _root_.GlobalTheory.CuspRep.IsStable V' ∧ V' ≤ A ∧ ∃ v ∈ V' ⊓ T, inner ℂ (cls h ψ) (cls h v) ≠ 0
  have hψψ : inner ℂ (cls h ψ) (cls h ψ) ≠ 0 := fun e => hψ0 (hinj ψ hψW (inner_self_eq_zero.1 e))
  have hex : ∃ n, ∃ V', Cand V' ∧ Module.finrank ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) = n :=
    ⟨_, A, ⟨hAst, le_rfl, ψ, ⟨mem_admissible_span_self hψW, hψT⟩, hψψ⟩, rfl⟩
  obtain ⟨V1, hV1, hV1n⟩ := Nat.find_spec hex
  have hmin : ∀ V', Cand V' → Nat.find hex ≤ Module.finrank ℂ (V' ⊓ T : Submodule ℂ (Sm E N)) :=
    fun V' hV' => Nat.find_min' hex ⟨V', hV', rfl⟩
  let V0 := sInf {U : Submodule ℂ (Sm E N) | _root_.GlobalTheory.CuspRep.IsStable U ∧ V1 ⊓ T ≤ U}
  have hV0st : _root_.GlobalTheory.CuspRep.IsStable V0 := isStable_sInf _ fun U hU => hU.1
  have hV0le : V0 ≤ V1 := sInf_le ⟨hV1.1, inf_le_left⟩
  have hgen : ∀ U, _root_.GlobalTheory.CuspRep.IsStable U → V1 ⊓ T ≤ U → V0 ≤ U := fun U hU hle => sInf_le ⟨hU, hle⟩
  have hTV0 : V1 ⊓ T ≤ V0 := le_sInf fun U hU => hU.2
  have hV0T : V0 ⊓ T = V1 ⊓ T := le_antisymm (inf_le_inf_right T hV0le) (le_inf hTV0 inf_le_right)
  have hV0A : V0 ≤ A := hV0le.trans hV1.2.1
  obtain ⟨v, hvT, hvψ⟩ := hV1.2.2
  have hvT0 : v ∈ V0 ⊓ T := hV0T ▸ hvT
  have key : ∀ U', Cand U' → U' ≤ V0 → V0 ≤ U' := by
    intro U' hU' hle
    have := hfd V1 hV1.2.1
    have := hfd U' hU'.2.1
    have h1 : U' ⊓ T ≤ V1 ⊓ T := hV0T ▸ inf_le_inf_right T hle
    have h2 : Module.finrank ℂ (V1 ⊓ T : Submodule ℂ (Sm E N)) ≤ Module.finrank ℂ (U' ⊓ T : Submodule ℂ (Sm E N)) :=
      hV1n ▸ hmin U' hU'
    have h3 : U' ⊓ T = V1 ⊓ T := Submodule.eq_of_le_of_finrank_le h1 h2
    exact hgen U' hU'.1 (h3 ▸ inf_le_left)
  refine ⟨V0, hV0st, hV0A, fun e => ?_, fun U hU hUst => ?_, v, hvT0.1, hvψ⟩
  · have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 (e ▸ hvT0.1)
    rw [hv0] at hvψ
    exact hvψ (by rw [show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 W.zero_mem, zero_smul,
      inner_zero_right])
  · let C := orthIn h V0 U (hV0A.trans hAW)
    have hCst : _root_.GlobalTheory.CuspRep.IsStable C := fun o x hx => ⟨hV0st o x hx.1, fun u hu => by
      obtain ⟨B, hB, hadjB⟩ := hadj o
      rw [hadjB x (hAW (hV0A hx.1)) u (hAW (hV0A (hU hu)))]
      exact hx.2 _ (hB U hUst u hu)⟩
    have := hfd U (hU.trans hV0A)
    obtain ⟨v1, ⟨hv1U, hv1T⟩, hv1⟩ := exists_orth h hW hA hinj hUst (hU.trans (hV0A.trans hAW))
      (hAW (hV0A hvT0.1)) hLo hLc ρ hρ hvT0.2
    have hv2C : v - v1 ∈ C := ⟨V0.sub_mem hvT0.1 (hU hv1U), hv1⟩
    have hv2T : v - v1 ∈ T := T.sub_mem hvT0.2 hv1T
    have hsplit : inner ℂ (cls h ψ) (cls h v) =
        inner ℂ (cls h ψ) (cls h v1) + inner ℂ (cls h ψ) (cls h (v - v1)) := by
      rw [cls_sub h (hAW (hV0A hvT0.1)) (hAW (hV0A (hU hv1U))), inner_sub_right]
      ring
    by_cases hc : inner ℂ (cls h ψ) (cls h v1) = 0
    · left
      have hC : Cand C := ⟨hCst, fun x hx => hV0A hx.1, v - v1, ⟨hv2C, hv2T⟩, by
        rw [hsplit, hc, zero_add] at hvψ
        exact hvψ⟩
      have hV0C := key C hC fun x hx => hx.1
      rw [eq_bot_iff]
      intro u hu
      exact (Submodule.mem_bot ℂ).2 (hinj u (hAW (hV0A (hU hu))) (inner_self_eq_zero.1 ((hV0C (hU hu)).2 u hu)))
    · right
      exact le_antisymm hU (key U ⟨hUst, hU.trans hV0A, v1, ⟨hv1U, hv1T⟩, hc⟩ hU)

end PositivityTheory.Rg.Rs.PrIrr

end
end

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth
  GlobalTheory.LevelTypeProj GlobalTheory.PRep GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs.PrAdm

namespace PositivityTheory.Rg.Rs

theorem pr_holds : Pr := by
  intro E _ _ _ N
  have hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL
  have hW : _root_.GlobalTheory.CuspRep.IsStable (A2 E N) := PrSt.isStable_square_integrable_forms hF
  refine ⟨hW, fun ψ hψ hψ0 => ?_⟩
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N μ
  have hA : ∀ φ ∈ A2 E N, IsAutForm φ := fun φ hφ => (PrSt.mem_square_integrable_forms hφ).1
  have h : ∀ φ ∈ A2 E N, MemL2Quotient (latticeGL E N) μ φ.1 := fun φ hφ =>
    memL2_of_isAutForm (PrSt.mem_square_integrable_forms hφ).1 (PrSt.mem_square_integrable_forms hφ).2
  have hF2 := toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level
  have hinj : ∀ x ∈ A2 E N, cls h x = 0 → x = 0 := fun x hx e => by
    rw [cls_mk h hx] at e
    exact congrArg Subtype.val (hF2 (e.trans (map_zero _).symm))
  have hadj := fun o => PrSt.exists_adj h hW hA o
  obtain ⟨V, hVst, hVA, hV0, hirr, v, hvV, hvψ⟩ := PrIrr.exists_irr h hW hA hinj hadj hψ hψ0
  have hVW : V ≤ A2 E N := hVA.trans (admissible_span_le _ ψ)
  have hexist : ∀ χ ∈ A2 E N, ∃ v ∈ V, ∀ w ∈ V, inner ℂ (cls h (χ - v)) (cls h w) = 0 := by
    intro χ hχ
    obtain ⟨L, hLo, hLc, hχT⟩ := exists_type (hA χ hχ)
    have : FiniteDimensional ℂ (orbSpan χ) := (hA χ hχ).kfin
    have hρ := isContRep_sub (orbSpan χ) (orbSpan_stable χ)
    have : FiniteDimensional ℂ (V ⊓ typePart L (sub (cptRep E N) (orbSpan χ) (orbSpan_stable χ)) :
        Submodule ℂ (Sm E N)) :=
      have := finiteDimensional_admissible_isotypic hA (hA ψ hψ) hLo _ hρ
      Submodule.finiteDimensional_of_le (inf_le_inf_right _ hVA)
    obtain ⟨v, hv, hv'⟩ := exists_orth h hW hA hinj hVst hVW hχ hLo hLc _ hρ hχT
    exact ⟨v, hv.1, hv'⟩
  choose! P hPV hP using hexist
  let pW : A2 E N →ₗ[ℂ] Sm E N :=
    { toFun := fun χ => P χ.1
      map_add' := fun x y => by
        refine orth_unique h hinj hVW ((A2 E N).add_mem x.2 y.2) (hPV _ ((A2 E N).add_mem x.2 y.2))
          (V.add_mem (hPV _ x.2) (hPV _ y.2)) (hP _ ((A2 E N).add_mem x.2 y.2)) fun w hw => ?_
        have e : x.1 + y.1 - (P x.1 + P y.1) = (x.1 - P x.1) + (y.1 - P y.1) := by abel
        change inner ℂ (cls h (x.1 + y.1 - (P x.1 + P y.1))) (cls h w) = 0
        rw [e, cls_add h ((A2 E N).sub_mem x.2 (hVW (hPV _ x.2))) ((A2 E N).sub_mem y.2 (hVW (hPV _ y.2))),
          inner_add_left, hP _ x.2 w hw, hP _ y.2 w hw, add_zero]
      map_smul' := fun c x => by
        refine orth_unique h hinj hVW ((A2 E N).smul_mem c x.2) (hPV _ ((A2 E N).smul_mem c x.2))
          (V.smul_mem c (hPV _ x.2)) (hP _ ((A2 E N).smul_mem c x.2)) fun w hw => ?_
        have e : c • x.1 - c • P x.1 = c • (x.1 - P x.1) := (smul_sub c _ _).symm
        change inner ℂ (cls h (c • x.1 - (RingHom.id ℂ) c • P x.1)) (cls h w) = 0
        rw [RingHom.id_apply, e, cls_smul h c ((A2 E N).sub_mem x.2 (hVW (hPV _ x.2))), inner_smul_left,
          hP _ x.2 w hw, mul_zero] }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend pW
  have hpW : ∀ χ ∈ A2 E N, p χ = P χ := fun χ hχ => LinearMap.congr_fun hp ⟨χ, hχ⟩
  refine ⟨V, p, ⟨fun φ hφ => hA φ (hVW hφ), fun φ hφ => (PrSt.mem_square_integrable_forms (hVW hφ)).2, hVst, hV0, hirr⟩,
    fun χ hχ => by rw [hpW χ hχ]; exact hPV χ hχ, fun o χ hχ => ?_, ?_⟩
  · rw [hpW _ (hW o χ hχ), hpW χ hχ]
    refine orth_unique h hinj hVW (hW o χ hχ) (hPV _ (hW o χ hχ)) (hVst o _ (hPV χ hχ)) (hP _ (hW o χ hχ))
      fun w hw => ?_
    obtain ⟨B, hB, hadjB⟩ := hadj o
    rw [← map_sub, hadjB _ ((A2 E N).sub_mem hχ (hVW (hPV χ hχ))) w (hVW hw)]
    exact hP χ hχ _ (hB V hVst w hw)
  · rw [hpW ψ hψ]
    intro e
    have := hP ψ hψ v hvV
    rw [e, sub_zero] at this
    exact hvψ this

end PositivityTheory.Rg.Rs

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatAsc
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs

namespace satakeAscent

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem eventually_spherical {a : ℕ} (π : CuspSub E a) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      GlobalTheory.LGrp.IsSpherical (π.locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw
  refine (Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun e => h0 (congrArg Subtype.val e)⟩
  obtain ⟨g, rfl⟩ := hk
  exact Subtype.ext (hw g)

theorem satLike_cusp {m : ℕ} (π' : CuspSub E m) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w (π'.locRep w) B) : SatakeVectors.SatLike π'.V w B := fun ψ hψ hK h0 => by
  have hx := h.2 ⟨ψ, hψ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hK k hk))
    fun e => h0 (congrArg Subtype.val e)
  exact hx.map (ρ' := (finRep E m).comp (locGL E m w)) π'.V.subtype (fun _ _ => rfl) h0

theorem modExp_const {a d : ℕ} (i : Fin d) :
    modExp (fun _ : Fin d => Fin a) i = (a : ℤ) * ((d : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) := by
  have e : modExp (fun _ : Fin d => Fin a) i =
      (∑ _b ∈ Finset.Ioi i, (a : ℤ)) - ∑ _b ∈ Finset.Iio i, (a : ℤ) := by
    unfold modExp
    congr 1
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
    · exact Finset.sum_congr (by ext; simp) fun _ _ => by simp
  have hi := i.2
  have hc : ((d - 1 - (i : ℕ) : ℕ) : ℤ) = (d : ℤ) - 1 - ((i : ℕ) : ℤ) := by omega
  rw [e, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul, hc]
  ring

theorem spehExp_rev (d : ℕ) (i : Fin d) : spehExp d i.rev = -spehExp d i := by
  have h := i.2
  simp only [spehExp, Fin.val_rev]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem term_eq {a d : ℕ} (w : HeightOneSpectrum (𝓞 E)) (B₀ : Multiset ℂˣ) (ν : HChar E) (i : Fin d)
    (hν : ν.IsAbsPow (-spehExp d i + a * spehExp d i)) :
    ((B₀.map (· * ν.val w)).map (· * SatakeVectors.qU w ((modExp (fun _ : Fin d => Fin a) i : ℂ) / 2))).map
      (fun b : ℂˣ => (b : ℂ)) = satTw w (-(spehExp d i : ℂ)) B₀ := by
  rw [SatakeVectors.satTw_eq, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, SatakeVectors.qU_val, hν.2.1 w, modExp_const]
  rw [mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w).ne_bot)]
  congr 2
  simp only [spehExp]
  push_cast
  ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem sum_rev {d : ℕ} (w : HeightOneSpectrum (𝓞 E)) (B₀ : Multiset ℂˣ) :
    ∑ i : Fin d, satTw w (-(spehExp d i : ℂ)) B₀ = ∑ i : Fin d, satTw w (spehExp d i : ℂ) B₀ := by
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, spehExp_rev]
  push_cast
  ring_nf

end satakeAscent

open satakeAscent in
theorem satAsc_holds : SatAsc := by
  intro E _ _ _ N a d V π hV hA
  obtain ⟨hsum, ν, hν, f, hfP, hfi, hfe⟩ := hA
  filter_upwards [eventually_spherical π] with w hw
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.CuspRep.UnrSat.exists_hasSatGL_locRep PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a π w hw
  refine ⟨B₀, hB₀, fun B hB => ?_⟩
  obtain ⟨φ, hφV, hφ⟩ := hB.1
  have hF := hfP φ hφV
  have hF0 : f φ ≠ 0 := fun e => hφ.1 (hfi φ hφV e)
  have hFK : ∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) (f φ) = f φ := fun k hk => by
    have e := hfe (.fin (locGL E N w k)) φ hφV
    have e2 : finRep E N (locGL E N w k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ.2.1 k hk
    exact e.symm.trans (congrArg f e2)
  have hS : ∀ i, SatakeVectors.SatLike (π.twist (ν i)).V w (B₀.map (· * (ν i).val w)) := fun i =>
    satLike_cusp _ (GlobalTheory.SphGal.hasSatGL_twist E a π (ν i) w B₀ ((hν i).1 w) hB₀)
  have hc := SatakeVectors.isSatVecGL_of_ind hsum (fun i => (π.twist (ν i)).V)
    (fun i g ψ hψ => (π.twist (ν i)).stable (.fin g) ψ hψ) (fun i ψ hψ => ((π.twist (ν i)).cusp ψ hψ).1.level.preimage (CuspSub.continuous_locGL w))
    _ hS hF0 hFK hF.1 hF.2.2.2
  have hφ' : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφV⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E N).comp (locGL E N w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective hφ
  have hm := hφ'.map (ρ' := (finRep E N).comp (locGL E N w)) (f ∘ₗ V.subtype) (fun g v => hfe (.fin (locGL E N w g)) v.1 v.2) hF0
  rw [hm.unique hc, ← sum_rev, ← Finset.sum_congr rfl fun i _ => term_eq w B₀ (ν i) i (hν i)]
  exact map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ)) _ _

end PositivityTheory.Rg.Rs

end
end
