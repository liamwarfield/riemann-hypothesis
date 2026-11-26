module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetVectorsNonzeroDepthFockVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateHalfCommutantActsOnCosetVectorByScalar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantDepthLatticePermutesCosetVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantPartChosenPlacesMemCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantPartChosenPlacesMemCompletedLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AnnPart

theorem idemSum_mul_conj {D : D7} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e₀ a : AE D} (he₀ : IsIdemSum e₀ P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (ha : Formalism.L2.NTheta.IsIdemAt a Q) : e₀ * cA D a = 0 := by
  obtain ⟨q0, q1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₀
  obtain ⟨-, d2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt ha
  have k : e₀ * a = a := by
    refine GlobalTheory.DepthFix.ext_cpt ?_ fun R => ?_
    · rw [RingHom.map_mul, q0, zero_mul, GlobalTheory.SplitScalar.infPart_splitIdem ha.1]
    · rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hR : R = Q
      · rw [hR, q1 _ hQ, one_mul]
      · rw [d2 R hR, mul_zero]
  rw [← k, RingHom.map_mul, ← mul_assoc, he₀.2, zero_mul]

theorem part_mem_latO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → e • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True := by
  intro D T L sc μ₀ hL G ψ hψ i hi e he w hw hinf
  obtain ⟨hS, hT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨-, hw2⟩ := hw
  have hmx : MxAt (fun _ => True) (e • w) := fun a b => by
    refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun v => (v.2 trivial).elim⟩
    have h0 : infPart D (w a b) = 0 := by simpa using congrFun (congrFun hinf a) b
    rw [RingHom.mem_ker, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, h0, mul_zero]
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ _ _ _ _ hS hT (fun _ => True) (e • w) hmx).2 fun u hu => ?_
  rw [GlobalTheory.SplitScalar.symplO_smul]
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_smul, ← GlobalTheory.LatVac.symplHom_apply, map_sum]
  refine Finset.sum_induction _ (fun z => ψ z = 1) (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, mul_one])
    (AddChar.map_zero_eq_one ψ) fun PP hPP => ?_
  rw [GlobalTheory.LatVac.symplHom_apply]
  have hsp := GlobalTheory.SplitScalar.isSplitIdem_conj (hes PP hPP).1
  have hmem : cA D (es PP) • u ∈ depLat G (.chi i 0) := by
    show _ ∧ _
    refine ⟨GlobalTheory.CosetRow.smul_mem_latO_idem _ _ hsp.1 hu, fun e₀ he₀ => ?_⟩
    rw [smul_smul, idemSum_mul_conj he₀ hPP (hes PP hPP), zero_smul]
    exact zero_mem _
  refine hw2 _ hsp _ hmem ?_
  rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hsp.1]

end GlobalTheory.AnnPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantPartChosenPlacesMemCompletedLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutantPart_chosenPlaces_mem_completedLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → e • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True := by
  first | exact @GlobalTheory.AnnPart.part_mem_latO | exact GlobalTheory.AnnPart.part_mem_latO | (intros; apply GlobalTheory.AnnPart.part_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHomApproxHalfModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHomApproxHalfModIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosRatApprox

open GlobalTheory.FunObj.Comparison₂

theorem infPart_idemSum_mul {D : D7} {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) (a : AE D) :
    infPart D (e * a) = 0 := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  rw [(infPart D).map_mul, e0, zero_mul]


set_option maxHeartbeats 1000000 in
theorem exists_rat_approx : ∀ {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → Submodule.IsFullLattice D.host.E Λ → Submodule.IsFullLattice D.host.E Λ' → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → ∀ z : Mx D m n, IsHalf e z → z ∈ hatMx (homLat Λ Λ') → ∃ x₁ : homLat Λ Λ', z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  intro D m n Λ Λ' 𝔪 h𝔪 hΛ hΛ' e P he z hz hzmem
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E n Λ hΛ
  obtain ⟨β', hβ'⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E m Λ' hΛ'
  have hz' : z ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat Λ Λ') := by rwa [Submodule.top_smul]
  obtain ⟨-, hs⟩ := (mem_hatMx_iff hβ hβ' ⊤ z).1 hz'
  choose s _ hs' using hs
  obtain ⟨x₀, hx₀, ht⟩ := GlobalTheory.FunObj.HatFrame.homLat_approx_mod Λ Λ' β β' hβ hβ' 𝔪 h𝔪 s
  choose t htI htv using ht
  have k1 : ∀ i j, (z - e • x₀.map (incA D)) i j = e * (z i j - incA D (x₀ i j)) :=
    fun i j => by rw [mul_sub, hz i j]; rfl
  have k2 : ∀ i j, fr β' β ((z - e • x₀.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr β' β (z.map (toEAf D)) i j - fr β' β (x₀.map (eToEAf D)) i j) := fun i j => by
    have : (z - e • x₀.map (incA D)).map (toEAf D) = toEAf D e • (z.map (toEAf D) - x₀.map (eToEAf D)) :=
      Matrix.ext fun i j => by rw [Matrix.map_apply, k1, RingHom.map_mul, RingHom.map_sub]; rfl
    rw [this, fr_smul, fr_sub]; rfl
  refine ⟨⟨x₀, hx₀⟩, ?_⟩
  show z - e • x₀.map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')
  refine (mem_hatMx_iff hβ hβ' 𝔪 _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [k1 i j]; exact infPart_idemSum_mul he _
  · let eS : {x // x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E} := ⟨toEAf D e, GlobalTheory.CosToCoset.idem_mem_OA he⟩
    refine ⟨eS * -t i j, Ideal.mul_mem_left _ eS (neg_mem (htI i j)), ?_⟩
    rw [k2, ← hs' i j]
    show toEAf D e * -((t i j : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = _
    rw [htv i j, neg_sub]

end GlobalTheory.CosRatApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHomApproxHalfModIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_hom_approx_half_mod_ideal : ∀ {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → Submodule.IsFullLattice D.host.E Λ → Submodule.IsFullLattice D.host.E Λ' → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → ∀ z : Mx D m n, IsHalf e z → z ∈ hatMx (homLat Λ Λ') → ∃ x₁ : homLat Λ Λ', z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  first | exact @GlobalTheory.CosRatApprox.exists_rat_approx | exact GlobalTheory.CosRatApprox.exists_rat_approx | (intros; apply GlobalTheory.CosRatApprox.exists_rat_approx <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantDepthLatticePermutesCosetVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosShift

variable {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
  {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}

theorem isHalf_sub' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x - y) := fun i j => by
  simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_add' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem map_smul_sub (e : AE D) (a b : homLat Λ Λ') : e • ((a - b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  rw [Submodule.coe_sub, Matrix.map_sub _ (incA D).map_sub, smul_sub]

theorem map_smul_add (e : AE D) (a b : homLat Λ Λ') : e • ((a + b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  ext i j
  simp only [Submodule.coe_add, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    (incA D).map_add, smul_add]

theorem mk_sub' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a - b) = (Submodule.Quotient.mk a - Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_sub _

theorem mk_add' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a + b) = (Submodule.Quotient.mk a + Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_add _

theorem mem_cosSet_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₀ x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (t : Mx D m n) :
    t + z ∈ cosSet e (Cos.mk 𝔪 x₀) ↔ t ∈ cosSet e (Cos.mk 𝔪 (x₀ - x₁)) := by
  constructor
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨?_, y - x₁, ?_, ?_⟩
    · have := isHalf_sub' ht hz
      rwa [add_sub_cancel_right] at this
    · rw [mk_sub', mk_sub']
      exact congrArg (· - _) hy
    · rw [map_smul_sub]
      have h2 := sub_mem hm hx₁
      have e2 : t + z - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) -
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨isHalf_add' ht hz, y + x₁, ?_, ?_⟩
    · rw [mk_add']
      rw [mk_sub'] at hy
      have hy' : (Submodule.Quotient.mk y : homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) =
          Submodule.Quotient.mk x₀ - Submodule.Quotient.mk x₁ := hy
      rw [hy', sub_add_cancel]
      rfl
    · rw [map_smul_add]
      have h2 := add_mem hm hx₁
      have e2 : t - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) +
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t + z - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2

theorem cosInd_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (κ : Cos Λ Λ' 𝔪) :
    ∃ κ' : Cos Λ Λ' 𝔪, (fun t => cosInd e κ (t + z)) = cosInd e κ' := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Cos.mk 𝔪 x₀ = κ := Submodule.Quotient.mk_surjective _ κ
  refine ⟨Cos.mk 𝔪 (x₀ - x₁), funext fun t => ?_⟩
  have key := mem_cosSet_add hz x₀ x₁ hx₁ t
  rw [hx₀] at key
  show Set.indicator (cosSet e κ) 1 (t + z) = Set.indicator (cosSet e (Cos.mk 𝔪 (x₀ - x₁))) 1 t
  classical
  simp only [Set.indicator_apply, key, Pi.one_apply]

end GlobalTheory.CosShift

private theorem GlobalTheory.CosShift.selfDual_full {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := fun V Λ hΛ => _root_.DedupShared.selfDual_isFullLattice V Λ hΛ


theorem GlobalTheory.CosShift.mem_hatMx_of_latO {D : D7} (hq : OffQ D) {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}
    (hL : L.Is μ₀) (G : GridData L sc) {i : ℕ} (hi : i < D.R.m) {e : AE D} (he : IsIdemSum e G.pl.W0)
    {z : WO (G.pS (.chi i 0)) (G.pT (.chi i 0))} (hz : IsHalf e z)
    (hm : z ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) :
    z ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨βS, hβS⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latS (.chi i 0)) (GlobalTheory.CosShift.selfDual_full _ _ hSD.1)
  obtain ⟨βT, hβT⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latT (.chi i 0)) (GlobalTheory.CosShift.selfDual_full _ _ hSD.2)
  exact GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hz fun w hw a b =>
    GlobalTheory.RowLatChi.int_of_mem_latO hSD.1 hβS hβT w (GlobalTheory.DepthFix.aa_int hL hq G hw) hm a b


set_option maxHeartbeats 1000000 in
open GlobalTheory.CosShift in
theorem GlobalTheory.CosShift.epart : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → (∀ κ, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd e κ) (W.cosVec i κ)) → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∀ κ, ∃ κ', heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (W.cosVec i κ) = W.cosVec i κ' := by
  intro D hq T L μ₀ hL sc G W M hM i hi e he hθ w hw hwinf κ
  obtain ⟨⟨T₀, hT₀⟩, -⟩ := hθ κ
  have hv : ∀ κ, W.cosVec i κ = T₀ (cosInd e κ) := fun κ => (hθ κ).2 T₀ hT₀
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hz : IsHalf e (e • w) := fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)),
      e • w - e • (x₁ : Matrix _ _ D.host.E).map (incA D) ∈
        hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) :=
    (by
      apply GlobalTheory.T.exists_rational_hom_approx_half_mod_ideal (G.pl.modul_ne_bot sc)
      · with_unfolding_all exact selfDual_full (G.pS (.chi i 0)) (G.latS (.chi i 0)) hSD.1
      · with_unfolding_all exact selfDual_full (G.pT (.chi i 0)) (G.latT (.chi i 0)) hSD.2
      · exact he
      · exact hz
      · exact mem_hatMx_of_latO hq hL G hi he hz (GlobalTheory.T.commutantPart_chosenPlaces_mem_completedLattice hL G W.ψ W.ψ_std i hi e he w hw hwinf))
  obtain ⟨κ', hκ'⟩ := cosInd_add hz x₁ hx₁ κ
  refine ⟨κ', ?_⟩
  rw [hv κ, hv κ', ← hκ']
  exact (hT₀.trans (cosInd e κ) (GlobalTheory.GridWeil.isSBHalf_cosInd hSD.1 hSD.2 (G.pl.modul_ne_bot sc) hee
    (GlobalTheory.PlaceDatum.infPart_idemSum he) κ) (e • w) hz).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantDepthLatticePermutesCosetVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_depth_lattice_permutes_coset_vectors : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → (∀ κ, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd e κ) (W.cosVec i κ)) → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∀ κ, ∃ κ', heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (W.cosVec i κ) = W.cosVec i κ' := by
  first | exact @GlobalTheory.CosShift.epart | exact GlobalTheory.CosShift.epart | (intros; apply GlobalTheory.CosShift.epart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOffPartVacuumCommutantActsByScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOffPartVacuumCommutantActsByScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CommVac

variable {D : D7}

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_left (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hO_smul_right (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem symplO_smul_comm (S T : HSp D) {a : AE D} (ha : cA D a = a) (x y : WO S T) :
    symplO S T (a • x) y = symplO S T x (a • y) := by
  unfold symplO
  rw [hO_smul_left, hO_smul_right, ha]


set_option maxHeartbeats 1000000 in
theorem heisO_offPart_vac : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 →
    ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) ((1 - e - cA D e) • w) (W.vac i) = c • W.vac i := by
  intro D _ T L μ0 hL sc G W M _ i hi e he w hw hinf
  classical
  obtain ⟨hsdS, hsdT⟩ := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D W.ψ _ _ (G.latS (.chi i 0)) (G.latT (.chi i 0)) W.ψ_std hsdS hsdT
  have hlat := (W.vac_is i hi).2.lat
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    linear_combination hee + hce + 2 * hec
  have hfc : cA D (1 - e - cA D e) = 1 - e - cA D e := by
    rw [map_sub, map_sub, map_one, Formalism.L2.Theta.cA_cA]; ring
  have hfint : finPart D (1 - e - cA D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hff])
  have hef : ∀ e', IsIdemSum e' G.pl.W0 → e' * (1 - e - cA D e) = 0 := fun e' he' => by
    rw [GlobalTheory.StepVecSum.idemSum_eq (G.V (.grid 0 0)) he he']
    linear_combination -hee - hec
  have hdep : ∀ u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
      (fun _ => True), (1 - e - cA D e) • u ∈ depLat G (.chi i 0) := fun u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfint u hu, fun e' he' => by
      rw [smul_smul, hef e' he', zero_smul]; exact AddSubgroup.zero_mem _⟩
  have key : ∀ u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
      (fun _ => True), W.ψ (symplO _ _ w ((1 - e - cA D e) • u)) = 1 := by
    intro u hu
    obtain ⟨v, hvdef⟩ : ∃ v, v = (1 - e - cA D e) • u := ⟨_, rfl⟩
    rw [← hvdef]
    have hv : v ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
        (fun _ => True) := hvdef ▸ GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfint u hu
    have hpiece : ∀ c : AE D, finPart D c ∈ intAE D → c • v ∈ depLat G (.chi i 0) := fun c hc => by
      rw [hvdef, smul_smul, mul_comm, ← smul_smul]
      exact hdep _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ c hc u hu)
    have hadd : ∀ a b : AE D, W.ψ (symplO _ _ w (a • v)) = 1 → W.ψ (symplO _ _ w (b • v)) = 1 →
        W.ψ (symplO _ _ w ((a + b) • v)) = 1 := fun a b ha hb => by
      rw [add_smul, symplO_add_right, AddChar.map_add_eq_mul, ha, hb, one_mul]
    have hsplit : ∀ e₁, IsSplitIdem D e₁ → W.ψ (symplO _ _ w (e₁ • v)) = 1 := fun e₁ h₁ =>
      hw.2 e₁ h₁ _ (hpiece _ (GlobalTheory.SplitHomLattice.idem_int h₁))
        (fun a b => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h₁.1])
    have hQ := GlobalTheory.FinPl.FlatFix.finite_two (D := D) (fun _ => True)
    have hmemQ : ∀ x, x ∈ hQ.toFinset ↔ True ∧ (2 : 𝓞 D.host.F) ∈ x.asIdeal := fun x => hQ.mem_toFinset
    have hch : ∀ x, x ∈ hQ.toFinset → ∃ e₁ ε, IsSplitIdem D e₁ ∧ IsPlaceIdem D x ε ∧
        e₁ + cA D e₁ = algebraMap (AF D.host.F) (AE D) ε := by
      intro x hx
      rcases (GlobalTheory.T.isTameFinitePlaceHermitian_all D x).2 with h | h
      · exact absurd ((hmemQ x).1 hx).2 h
      · exact h
    choose! es εs hes hεs hsum using hch
    have hdec := GlobalTheory.FinPl.FlatFix.indicatorIdempotent_eq_add_sum (fun _ => True) hQ.toFinset hmemQ εs hεs
    have hvc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (fun _ => True)) • v = v := by
      ext a b
      rw [Matrix.smul_apply, smul_eq_mul]
      exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hv a b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hvc, hdec, map_add (f := _), map_sum]
    refine hadd _ _ ?_ ?_
    · have hβ := GlobalTheory.FinPl.FlatFix.int_alg_pair (D := D) (GlobalTheory.FinPl.FlatFix.halfOff_int (D := D) fun _ => True)
      have e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.FinPl.FlatFix.halfOff (fun _ => True) +
          GlobalTheory.FinPl.FlatFix.halfOff (D := D) (fun _ => True))) • v =
          2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.FinPl.FlatFix.halfOff (D := D) (fun _ => True))) • v) := by
        rw [GlobalTheory.FinPl.FlatFix.pair_add, map_add (f := _), add_smul, two_nsmul]
      rw [e2]
      exact hw.1 _ (hpiece _ hβ)
    · refine Finset.sum_induction _ (fun c => W.ψ (symplO _ _ w (c • v)) = 1) hadd ?_ ?_
      · have h0 := symplO_add_right (G.pS (.chi i 0)) (G.pT (.chi i 0)) w 0 0
        rw [add_zero] at h0
        have h0' : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w 0 = 0 := by linear_combination -h0
        show W.ψ (symplO _ _ w ((0 : AE D) • v)) = 1
        rw [zero_smul, h0', AddChar.map_zero_eq_one]
      · intro x hx
        rw [← hsum x hx]
        exact hadd _ _ (hsplit _ (hes x hx)) (hsplit _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (hes x hx)))
  have hfin' : ((1 - e - cA D e) • w).map (infPart D) = 0 := by
    ext a b
    have := congrFun (congrFun hinf a) b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.zero_apply] at this ⊢
    rw [this, mul_zero]
  have hmem : (1 - e - cA D e) • w ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _)
      (G.latT (.chi i 0) : Set _) (fun _ => True) :=
    (h1 _ hfin').2 fun u' hu' => by rw [symplO_smul_comm _ _ hfc]; exact key u' hu'
  obtain ⟨ε, -, hε⟩ := h3 _ hlat _ hmem
  exact ⟨ε, hε _ hlat⟩

end GlobalTheory.CommVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOffPartVacuumCommutantActsByScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_offPart_vacuumCommutant_acts_by_scalar : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) ((1 - e - cA D e) • w) (W.vac i) = c • W.vac i := by
  first | exact @GlobalTheory.CommVac.heisO_offPart_vac | exact GlobalTheory.CommVac.heisO_offPart_vac | (intros; apply GlobalTheory.CommVac.heisO_offPart_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOffIdempotentPartOrthogonalHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOffIdempotentPartOrthogonalHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdemOffOrth

theorem symplO_compl_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  intro D S T P e he w x hx
  have h1 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have h2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hz : symplO S T (0 : WO S T) x = 0 := by
    have := GlobalTheory.BigDat.symplO_cA_smul S T (0 : AE D) w x
    rw [map_zero, zero_smul, zero_smul, GlobalTheory.BigDat.symplO_zero_right'] at this
    exact this.symm
  rcases hx with hx | hx
  · have hxe : x = cA D (cA D e) • x := by
      rw [GlobalTheory.DualPairCheck.cA_cA]; exact (GlobalTheory.BigDat.smul_of_isHalf hx).symm
    rw [hxe, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : cA D e * (1 - e - cA D e) = 0 := by linear_combination -c1 - (mul_comm e (cA D e) ▸ h2 : cA D e * e = 0)
    rw [this, zero_smul]; exact hz
  · rw [← GlobalTheory.BigDat.smul_of_isHalf hx, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : e * (1 - e - cA D e) = 0 := by linear_combination -h1 - h2
    rw [this, zero_smul]; exact hz

end GlobalTheory.IdemOffOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOffIdempotentPartOrthogonalHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  first | exact @GlobalTheory.IdemOffOrth.symplO_compl_half | exact GlobalTheory.IdemOffOrth.symplO_compl_half | (intros; apply GlobalTheory.IdemOffOrth.symplO_compl_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorEigenOfThetaVectorAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorEigenOfThetaVectorAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ThetaEigen

variable {D : D7}

def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext x; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem heisLin_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisLin ψ S T w f = heisO ψ S T w f := rfl

theorem heisO_smul_comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (k : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (k • f) = k • heisO ψ S T w f := (heisLin ψ S T w).map_smul k f

theorem addChar_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := AddChar.map_zero_eq_one ψ
  rw [← add_neg_cancel a, AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem eq_zero_of_heisO_eq_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ)
    (h : heisO ψ S T w g = 0) : g = 0 := by
  funext x
  have h1 := congrFun h (x - w)
  simp only [heisO, sub_add_cancel, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left (addChar_ne_zero ψ _)

theorem heisO_eigen_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (w : WO S T) (c : ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ x : WO S T, IsHalf e x → symplO S T w x = 0) → (∀ y : WO S T, IsHalf (cA D e) y → symplO S T w y = 0) → heisO ψ S T w f₀ = c • f₀ → ∃ c' : ℂ, heisO ψ S T w f = c' • f := by
  intro D ψ S T e Λ f₀ Φ f w c hθ hx hy hc
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hθ
  have hψ0 : ψ 0 = 1 := AddChar.map_zero_eq_one ψ
  have key : ∀ k : ℂ, k • heisO ψ S T w f₀ = f₀ → f = k • heisO ψ S T w f := by
    intro k hk
    have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ (k • (heisLin ψ S T w ∘ₗ T₀)) := by
      refine ⟨fun Φ' hΦ' x hxe => ?_, fun Φ' hΦ' y hye => ?_, ?_⟩
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.trans Φ' hΦ' x hxe, GlobalTheory.Asc.heisO_comm, hx x hxe, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.modul Φ' hΦ' y hye, GlobalTheory.Asc.heisO_comm, hy y hye, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.vac, hk]
    have h2 : f = (k • (heisLin ψ S T w ∘ₗ T₀)) Φ := hall _ hT'
    have h3 : f = T₀ Φ := hall T₀ hT₀
    rw [show (k • (heisLin ψ S T w ∘ₗ T₀)) Φ = k • heisO ψ S T w (T₀ Φ) from rfl, ← h3] at h2
    exact h2
  by_cases hc0 : c = 0
  · subst hc0
    rw [zero_smul] at hc
    have hf₀ := eq_zero_of_heisO_eq_zero ψ S T w f₀ hc
    have h1 := key 1 (by rw [one_smul, hc, hf₀])
    exact ⟨1, by rw [one_smul]; rw [one_smul] at h1; exact h1.symm⟩
  · refine ⟨c, ?_⟩
    have h1 := key c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
    calc heisO ψ S T w f = c • (c⁻¹ • heisO ψ S T w f) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      _ = c • f := by rw [← h1]

end GlobalTheory.ThetaEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorEigenOfThetaVectorAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_eigen_of_thetaVector_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (w : WO S T) (c : ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ x : WO S T, IsHalf e x → symplO S T w x = 0) → (∀ y : WO S T, IsHalf (cA D e) y → symplO S T w y = 0) → heisO ψ S T w f₀ = c • f₀ → ∃ c' : ℂ, heisO ψ S T w f = c' • f := by
  first | exact @GlobalTheory.ThetaEigen.heisO_eigen_of_isThetaAt | exact GlobalTheory.ThetaEigen.heisO_eigen_of_isThetaAt | (intros; apply GlobalTheory.ThetaEigen.heisO_eigen_of_isThetaAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutantPermutesFirstRowCosetVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosPerm

variable {D : D7}

theorem heisO_smul_fun (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (star f) = star (heisO ψ (negSp S) T w f) := by
  have h := GlobalTheory.CjNeg.heis_negS hψ S T w (star f)
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f) = f := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hc] at h
  rw [h]; funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem symplO_negSp (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.CjNeg.symplOH_negS]; ring

theorem mem_ann_negSp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Γ : AddSubgroup (WO S T)} {w : WO S T}
    (hw : w ∈ Ann ψ S T Γ) : w ∈ Ann ψ (negSp S) T Γ := by
  have key : ∀ a b : WO S T, ψ (symplO S T a b) = 1 → ψ (symplO (negSp S) T a b) = 1 := fun a b h => by
    rw [symplO_negSp, AddChar.map_neg_eq_inv, h, inv_one]
  exact ⟨fun u hu => key _ _ (hw.1 u hu), fun e he u hu hh => key _ _ (hw.2 e he u hu hh)⟩

end GlobalTheory.CosPerm


open GlobalTheory.CosPerm in
theorem GlobalTheory.CosPerm.cosVec_perm : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ)) ∧ VacG W.ψ _ _ (latRow G i) (star (W.cosVec i κ)) ∧ ∀ w ∈ Ann W.ψ _ _ (latRow G i), w.map (infPart D) = 0 → heisO W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) w (star (W.cosVec i κ)) ∈ Submodule.span ℂ (Set.range fun κ' => (star (W.cosVec i κ') : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → ℂ)) := by
  intro D hD T L μ0 hL sc G W M hM i hi κ
  obtain ⟨h1, hdep, hfock⟩ := GlobalTheory.T.coset_vectors_nonzero_depth_fock_vacua D hD T L μ0 hL sc G W M hM i hi κ
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hth := (GlobalTheory.CjNeg.theta_heis_neg D W.ψ hψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))).1 (star (W.cosVec i κ))
  have hcj : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star (W.cosVec i κ)) = W.cosVec i κ := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  rw [hcj] at hth
  refine ⟨h1, hfock, ⟨hth.2.1 hdep.1, fun u hu => ?_, fun e he u hu hh => ?_⟩, ?_⟩
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.1 u hu)
  · rw [heisO_star hψ]; exact congrArg star (hdep.2.2 e he u hu hh)
  intro w hw hfin
  have hw' : w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)) := mem_ann_negSp hw
  obtain ⟨e, he, hthe⟩ := W.cosVec_is
  have hthi := fun κ => hthe i hi κ
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.heisenberg_offPart_vacuumCommutant_acts_by_scalar D hD T L μ0 hL sc G W M hM i hi e he w hw' hfin
  obtain ⟨c₃, h₃⟩ := GlobalTheory.T.heisenbergOperator_eigen_of_thetaVector_at_place D W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) e
    (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True)
    (W.vac i) (cosInd e κ) (W.cosVec i κ) ((1 - e - cA D e) • w) c₀ (hthi κ)
    (fun x hx => GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w x (Or.inl hx))
    (fun y hy => GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half D (G.pS (.chi i 0)) (G.pT (.chi i 0)) G.pl.W0 e he w y (Or.inr hy)) hc₀
  obtain ⟨c₂, h₂⟩ := GlobalTheory.T.conjugateHalfCommutant_acts_on_cosetVector_by_scalar D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  obtain ⟨κ', h₁⟩ := GlobalTheory.T.commutant_depth_lattice_permutes_coset_vectors D hD T L μ0 hL sc G W M hM i hi e he hthi w hw' hfin κ
  have hdec : w = e • w + (cA D e • w + (1 - e - cA D e) • w) := by
    rw [← add_smul, ← add_smul, show e + (cA D e + (1 - e - cA D e)) = 1 by ring, one_smul]
  have hne : ∀ a, W.ψ a ≠ 0 := fun a h => by
    have := AddChar.map_add_eq_mul W.ψ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have e1 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (cA D e • w) ((1 - e - cA D e) • w) (W.cosVec i κ)
  rw [h₃, heisO_smul_fun, h₂, smul_smul] at e1
  have e1' : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ) =
      (W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ • ((c₃ * c₂) • W.cosVec i κ) := by
    rw [e1, inv_smul_smul₀ (hne _)]
  have e2 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := W.ψ) (S := G.pS (.chi i 0)) (T := G.pT (.chi i 0))
    (e • w) (cA D e • w + (1 - e - cA D e) • w) (W.cosVec i κ)
  rw [← hdec, e1', heisO_smul_fun, heisO_smul_fun, h₁] at e2
  have hC : heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ) =
      ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (cA D e • w + (1 - e - cA D e) • w)))⁻¹ *
        ((W.ψ (symplOH (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) ((1 - e - cA D e) • w)))⁻¹ * (c₃ * c₂))) • W.cosVec i κ' := by
    rw [← smul_smul, ← smul_smul, e2, inv_smul_smul₀ (hne _)]
  rw [heisO_star hψ]
  change star (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (W.cosVec i κ)) ∈ _
  rw [hC, star_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ', rfl⟩)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutantPermutesFirstRowCosetVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCommutant_permutes_firstRowCosetVectors : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ)) ∧ VacG W.ψ _ _ (latRow G i) (star (W.cosVec i κ)) ∧ ∀ w ∈ Ann W.ψ _ _ (latRow G i), w.map (infPart D) = 0 → heisO W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) w (star (W.cosVec i κ)) ∈ Submodule.span ℂ (Set.range fun κ' => (star (W.cosVec i κ') : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → ℂ)) := by
  first | exact @GlobalTheory.CosPerm.cosVec_perm | exact GlobalTheory.CosPerm.cosVec_perm | (intros; apply GlobalTheory.CosPerm.cosVec_perm <;> assumption)
end
