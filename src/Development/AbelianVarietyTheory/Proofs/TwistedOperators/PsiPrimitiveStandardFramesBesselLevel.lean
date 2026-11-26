module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.PrimStd

open GlobalTheory.SeeSaw (idV FI dI)
open scoped Pointwise

theorem modulBar_ne_bot {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) : P.modulBar sc ≠ ⊥ := by
  unfold Places.modulBar
  intro h
  apply P.modul_ne_bot sc
  have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
  simpa [smul_smul] using this

end GlobalTheory.AscFin.PrimStd


open GlobalTheory.SeeSaw (idV FI dI) in
open GlobalTheory.AscFin.PrimStd in
theorem GlobalTheory.AscFin.primAt_std_bessel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0,
    PrimAt W.ψ (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) v := by
  intro D _ T L μ0 _ sc G W M _ F hF ρ h v hv
  have hψ := W.ψ_std
  obtain ⟨-, f2, f3, -, f5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ hψ v
  obtain ⟨h2, he, -⟩ := hF.hB ρ h
  have hlat := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (modulBar_ne_bot G.pl sc)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hmB)
  have hAb : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hm)
  have hst : ∀ p, stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p ≠ 0 := fun p =>
    mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb))
  have hx : ∀ n : ℕ, (-D.host.xi0) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  let 𝔟 : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (p.1 + 1))⁻¹ *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)
  have hb0 : ∀ p, 𝔟 p ≠ 0 := fun p => mul_ne_zero
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (hx _)) (hst _)
  have key : ∀ (p : Fin ρ), ∀ a ∈ idAt D (· = v),
      GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) ↔ a ∈ idV (𝔟 p) v := by
    intro p a ha
    have e1 : GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a = fun k => (a * incA D ((-D.host.xi0) ^ (p.1 + 1))) *
        incA D ((G.colDec (2 * ρ + 2) (by omega) h).a k (Fin.castLE (by omega) p)) := by
      funext k
      show a * incA D ((F.dB ρ h).e k p) = _
      rw [he]
      simp only [colsOf, map_mul, mul_assoc]
    have hL1 := GlobalTheory.T.column_mem_lattice_iff_ideal (G.colDec (2 * ρ + 2) (by omega) h) (by norm_num) (G.sp.P (2 * ρ + 2)).lat
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) v (Fin.castLE (by omega) p) (a * incA D ((-D.host.xi0) ^ (p.1 + 1)))
    rw [e1]
    refine (show _ ↔ _ from hlat ▸ hL1).trans ?_
    have h3 := f3 (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)) _
      (inv_ne_zero (hx (p.1 + 1))) a
    rw [inv_inv] at h3
    exact ⟨fun h1 => h3.2 ⟨by rwa [mul_comm (incA D _) a], ha⟩, fun h1 => by rw [mul_comm a]; exact (h3.1 h1).1⟩
  intro i j hij s hs
  have key2 : (∀ a : AE D, GlobalTheory.FinPl.colMul (F.dB ρ h).jX j a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) →
      GlobalTheory.FinPl.colMul (F.dB ρ h).jX i (s * a) ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v)) ↔
      ∀ a ∈ idV (𝔟 j) v, s * a ∈ idV (𝔟 i) v := by
    constructor
    · intro h1 a ha
      have haA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ a ha
      exact (key i (s * a) (Ideal.mul_mem_left _ _ haA)).1 (h1 a ((key j a haA).2 ha))
    · intro h1 a hc
      have haA := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul (F.dB ρ h) hc
      exact (key i (s * a) (Ideal.mul_mem_left _ _ haA)).2 (h1 a ((key j a haA).1 hc))
  rw [key2, f2 _ _ (hb0 j) (hb0 i) s hs]
  have hsucc := stairId_succ (𝔞 := G.pl.stA sc) hAb (Fin.castLE (by omega) i : Fin (2 * ρ + 2 - 1)) (Fin.castLE (by omega) j)
    (by simp [Fin.coe_castLE, hij])
  have hrat : 𝔟 i * (𝔟 j)⁻¹ = FractionalIdeal.spanSingleton _ (-D.host.xi0) * (G.pl.stA sc * G.pl.stAbar sc) := by
    rw [mul_inv_eq_iff_eq_mul₀ (hb0 j)]
    have e2 : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ = -D.host.xi0 * ((-D.host.xi0) ^ (j.1 + 1))⁻¹ := by
      have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero
      rw [hij]
      field_simp
      ring
    show FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _ = _ * (FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _)
    rw [hsucc, e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    ring
  have hneg : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) = FractionalIdeal.spanSingleton _ D.host.xi0 :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
  have hsplit : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) * (G.pl.stA sc * G.pl.stAbar sc) *
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) = dI D := by
    rw [hneg]
    unfold Places.stA Places.stAbar dI
    field_simp
  have hL := GlobalTheory.T.fractionalIdealCompletion_mul_modulus_offExceptional G.pl sc v hv
  have e3 : idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) * (G.pl.stA sc * G.pl.stAbar sc)) v = idV (dI D) v := by
    rw [← hsplit, (hL _).2, (hL _).1]
  rw [hrat, e3]
  exact f5 s hs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_primitive_standardFrames_besselLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) v := by
  first | exact @GlobalTheory.AscFin.primAt_std_bessel | exact GlobalTheory.AscFin.primAt_std_bessel | (intros; apply GlobalTheory.AscFin.primAt_std_bessel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  ext i j; simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    show _ ∈ latO S T LS LT P
    rw [gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _), ← gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)

theorem latO_mul_left {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT') {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : (rat A : Mx D T'.rank T.rank) * u ∈ latO S T' LS (LT' : Set _) P :=
  GlobalTheory.OverTgt.mul_mem_latO (rat A) (fun _ hy => GlobalTheory.SeeSaw.CoreGlue.rat_mulVec_mem A hA hy) hu

theorem latO_mul_right {S S' T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LS' : Set (Fin S'.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (M : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hM : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ l, (∑ k, star (s k) * S.gram k l) * M l j = ∑ k, star (s' k) * S'.gram k j)
    {u : WO S T} (hu : u ∈ latO S T LS LT P) : u * (rat M : Mx D S.rank S'.rank) ∈ latO S' T LS' LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', hss⟩ := hM s hs
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s', hs', t, ht, ?_⟩
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← hss j, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply]
    show _ * incA D (M l j) = _
    rw [GlobalTheory.RankZeroVac.incA_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_left {m m' n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)}
    (A : Matrix (Fin m') (Fin m) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : (rat A : Mx D m' m) * x ∈ hatMx (I • homLat Λ Λ'') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I 1 A (fun y hy => by rwa [Matrix.one_mulVec]) hA x hx
  rwa [rat_one, Matrix.mul_one] at h

theorem hatMx_mul_right {m n n' : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (N : Matrix (Fin n) (Fin n') D.host.E) (hN : ∀ s ∈ Λ₁, N *ᵥ s ∈ Λ) {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : x * (rat N : Mx D n n') ∈ hatMx (I • homLat Λ₁ Λ') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I N 1 hN (fun y hy => by rwa [Matrix.one_mulVec]) x hx
  rwa [rat_one, Matrix.one_mul] at h

theorem wittEmbedding_preserves_hermitianForm {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (s : Fin S₀.rank → D.host.E) (j : Fin S₀.rank) :
    ∑ l, (∑ k, star ((d.i₀ *ᵥ s) k) * S.gram k l) * d.i₀ l j = ∑ k, star (s k) * S₀.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star (d.i₀ *ᵥ s)) S.gram) d.i₀ = Matrix.vecMul (star s) S₀.gram := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, d.iso]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem std_zA_lat {F : Asc.Frames G} (hF : Std F) : (∀ y ∈ G.Λ (.grid 0 0), F.oz.iA *ᵥ y ∈ G.Λ (.core 0)) ∧
    ∀ x ∈ G.Λ (.core 0), F.oz.qA *ᵥ x ∈ G.Λ (.grid 0 0) := by
  have hΛ : G.Λ (.core 0) = sumLat (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) (L.ΛY 0) G.sp.dec0.a (fun _ => 1) :=
    G.sp.lat0
  have hqi : F.oz.qA * F.oz.iA = 1 := rat_injective (by rw [rat_mul, rat_one]; exact F.oz.pA_jA)
  have hperp := G.sp.dec0.perp
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    change (HSpace.gram (Yc D 0))⁻¹ * (F.oz.iAᴴ * HSpace.gram (G.V (.core 0))) * G.sp.dec0.a = 0
    rw [hF.zA, Matrix.mul_assoc, Matrix.mul_assoc]
    have hp : (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ * HSpace.gram (G.sp.P 0).sp * G.sp.dec0.a = 0 := hperp
    rw [← Matrix.mul_assoc (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ, hp, Matrix.mul_zero]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · rw [hΛ]
    refine ⟨y, hy, 0, fun _ => (FractionalIdeal.mem_one_iff _).2 ⟨0, map_zero _⟩, ?_⟩
    rw [Matrix.mulVec_zero, add_zero, hF.zA]
  · rw [hΛ] at hx
    obtain ⟨y, hy, u, -, rfl⟩ := hx
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hF.zA, hqi, hqa, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
    exact hy

theorem std_aJ_lat {F : Asc.Frames G} (hF : Std F) (h : 2 * 0 + 2 ≤ D.R.m) :
    (∀ y ∈ G.Λ (.core 1), (F.dJ 0 h).i₀ *ᵥ y ∈ G.Λ (.grid 1 0)) ∧
    (∀ x ∈ G.Λ (.grid 1 0), ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y) ∧
    ∀ x ∈ G.Λ (.grid 1 0), (F.dJ 0 h).q0 *ᵥ x ∈ G.Λ (.core 1) := by
  have h1 : 1 ≤ D.R.m := by omega
  have hΛ : G.Λ (.grid 1 0) = sumLat (frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι) (G.Λ (.core 1))
      (G.colDec 1 le_rfl h1).a (stairId (G.pl.stA sc) (G.pl.stAbar sc) (1 - 1)) := G.sp.colLat 1 le_rfl h1
  have hi : (F.dJ 0 h).i₀ = frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι := hF.aJ 0 h
  have hqi : (F.dJ 0 h).q0 * (F.dJ 0 h).i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact (F.dJ 0 h).p0_j0)
  have mem : ∀ x, x ∈ G.Λ (.grid 1 0) ↔ ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y := by
    intro x
    rw [hΛ, hi]
    constructor
    · rintro ⟨y, hy, u, -, rfl⟩
      refine ⟨y, hy, ?_⟩
      have : (G.colDec 1 le_rfl h1).a *ᵥ u = 0 := by
        funext i; simp [Matrix.mulVec, dotProduct]
      rw [this, add_zero]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, 0, fun p => p.elim0, by rw [Matrix.mulVec_zero, add_zero]⟩
  refine ⟨fun y hy => (mem _).2 ⟨y, hy, rfl⟩, fun x hx => (mem x).1 hx, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem x).1 hx
  rwa [Matrix.mulVec_mulVec, hqi, Matrix.one_mulVec]

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem depthLattice_generalPosition_iff_extByZero {P₁ P₀ Y Lz S : HSp D} (o : OrthDec P₀ Y Lz) (d : HypDec S P₁ 0)
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin P₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin P₀.rank → D.host.E)}
    {ΛY : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (I : Ideal (𝓞 D.host.E)) (Q : AE D → Prop)
    (hiA : ∀ y ∈ ΛY, o.iA *ᵥ y ∈ Λ₀) (hqA : ∀ x ∈ Λ₀, o.qA *ᵥ x ∈ ΛY)
    (hi0 : ∀ y ∈ Λ₁, d.i₀ *ᵥ y ∈ ΛS) (hq0 : ∀ x ∈ ΛS, ∃ y ∈ Λ₁, x = d.i₀ *ᵥ y) (hq0' : ∀ x ∈ ΛS, d.q0 *ᵥ x ∈ Λ₁)
    (a : WO P₁ Y) :
    (o.jA * a ∈ latO (negSp P₁) P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀)) ↔
    (d.ext0 Y a ∈ latO (negSp S) Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • d.ext0 Y a ∈ hatMx (I • homLat ΛS ΛY)) := by
  have hpj : d.p0 * (rat d.i₀ : Mx D _ _) = 1 := d.p0_j0
  have hpA : (rat o.qA : Mx D _ _) * o.jA = 1 := o.pA_jA
  have cB : ∀ x : WO P₁ Y, x * d.p0 * (rat d.i₀ : Mx D _ _) = x := fun x => by
    rw [Matrix.mul_assoc, hpj, Matrix.mul_one]
  have cA : ∀ x : WO P₁ Y, (rat o.qA : Mx D _ _) * (o.jA * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hpA, Matrix.one_mul]
  have ext : d.ext0 Y a = a * d.p0 := rfl
  rw [ext, latO_negSp, latO_negSp]
  have hA1 : o.jA * a ∈ latO P₁ P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ↔
      a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      have := latO_mul_left o.qA hqA hu
      rwa [cA] at this
    · intro hu; exact latO_mul_left o.iA hiA hu
  have hB1 : a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) ↔
      a * d.p0 ∈ latO S Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      exact latO_mul_right d.q0 (fun s hs => ⟨d.i₀ *ᵥ s, hi0 s hs, fun j => GlobalTheory.RankZeroVac.wittDecomposition_gram_projection_identity d s j⟩) hu
    · intro hu
      have := latO_mul_right d.i₀ (fun s hs => by
        obtain ⟨y, hy, rfl⟩ := hq0 s hs
        exact ⟨y, hy, fun j => wittEmbedding_preserves_hermitianForm d y j⟩) hu
      rwa [cB] at this
  have hA2 : ∀ e : AE D, e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀) ↔ e • a ∈ hatMx (I • homLat Λ₁ ΛY) := by
    intro e
    rw [← Matrix.mul_smul]
    constructor
    · intro hx
      have := hatMx_mul_left I o.qA hqA hx
      rwa [cA] at this
    · intro hx; exact hatMx_mul_left I o.iA hiA hx
  have hB2 : ∀ e : AE D, e • a ∈ hatMx (I • homLat Λ₁ ΛY) ↔ e • (a * d.p0) ∈ hatMx (I • homLat ΛS ΛY) := by
    intro e
    rw [← Matrix.smul_mul]
    constructor
    · intro hx; exact hatMx_mul_right I d.q0 hq0' hx
    · intro hx
      have := hatMx_mul_right I d.i₀ hi0 hx
      rwa [cB] at this
  exact and_congr (hA1.trans hB1) (forall_congr' fun e => imp_congr_right fun _ => (hA2 e).trans (hB2 e))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jA_mem_latCore_iff : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)),
    F.oz.jA * a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  intro D _ T L _ _ sc G W M _ F hF h a
  obtain ⟨hiA, hqA⟩ := std_zA_lat hF
  obtain ⟨hi0, hq0, hq0'⟩ := std_aJ_lat hF h
  exact depthLattice_generalPosition_iff_extByZero F.oz (F.dJ 0 h) G.modul (fun e => IsIdemSum e G.pl.W0) hiA hqA hi0 hq0 hq0' a

end GlobalTheory.CoreRowLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)), F.oz.jA ⬝ a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  first | exact @GlobalTheory.CoreRowLat.jA_mem_latCore_iff | exact GlobalTheory.CoreRowLat.jA_mem_latCore_iff | (intros; apply GlobalTheory.CoreRowLat.jA_mem_latCore_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise
open GlobalTheory.AscFin


open GlobalTheory.StairLine GlobalTheory.SeeSaw in
theorem GlobalTheory.AscFin.primAt_jac_std : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h v hv
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hlat := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  let 𝔟 : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have hline : ∀ p : Fin ρ, ∀ a, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟 p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := hlat
    rw [e2]
    exact line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
      (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v a
  intro i j hij s hs
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h0
    apply G.pl.modul_ne_bot sc
    have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using h1
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hne : ∀ p, 𝔟 p ≠ 0 := fun p => mul_ne_zero
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)))
    (by
      unfold stairId
      refine mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)))
  have key : (∀ a : AE D, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX j a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) →
      GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i (s * a) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) ↔
      ∀ a ∈ idV (𝔟 j) v, s * a ∈ idV (𝔟 i) v :=
    ⟨fun H a ha => (hline i _).1 (H a ((hline j a).2 ha)), fun H a hc => (hline i _).2 (H a ((hline j a).1 hc))⟩
  rw [key, GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v _ _ (hne j) (hne i) s hs, ← DiffDual.idV_dI_iff D W.ψ W.ψ_std v s hs]
  have hid : 𝔟 i * (𝔟 j)⁻¹ * (((G.pl.modul sc * G.pl.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) = dI D := by
    have hst := stairId_succ (𝔞 := G.pl.stA sc) (c := 2 * ρ + 1 - 1) hB (Fin.castLE (by omega) i) (Fin.castLE (by omega) j)
      (by simp only [Fin.coe_castLE]; exact hij)
    have hSj : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) ≠ 0 := by
      unfold stairId
      exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))
    show FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) i) *
      (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (j.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j))⁻¹ * _ = _
    rw [hst]
    revert hSj
    generalize stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) = Sj
    intro hSj
    rw [FractionalIdeal.coeIdeal_mul, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    unfold Places.stA Places.stAbar dI
    have hx : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (-D.host.xi0) ^ (j.1 + 1) = -D.host.xi0 := by
      rw [hij, pow_succ (-D.host.xi0) (i.1 + 1), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)), one_mul]
    calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
          FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ (j.1 + 1)) * D.host.AA * D.host.AAbar *
          (Sj * Sj⁻¹) * (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) *
          (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ hSj, mul_inv_cancel₀ hN, mul_inv_cancel₀ hN', FractionalIdeal.spanSingleton_mul_spanSingleton, hx,
          mul_one, mul_one, mul_one]
        congr 2
        rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
        exact ⟨-1, by simp⟩
  constructor
  · intro hs'
    refine idV_le_of_loc (fun z hz => ?_) hs'
    obtain ⟨t, ht, htm⟩ := exists_modul G.pl sc hv
    exact ⟨t, ht, by rw [← hid, mul_comm (algebraMap _ _ _)]; exact FractionalIdeal.mul_mem_mul hz htm⟩
  · intro hs'
    refine GlobalTheory.SeeSaw.idV_mono ?_ v hs'
    rw [← hid]
    calc _ ≤ 𝔟 i * (𝔟 j)⁻¹ * 1 := by first | exact FractionalIdeal.mul_left_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_right FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  first | exact @GlobalTheory.AscFin.primAt_jac_std | exact GlobalTheory.AscFin.primAt_jac_std | (intros; apply GlobalTheory.AscFin.primAt_jac_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVector
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowLocVec

variable {D : D7}


open GlobalTheory.HalfProd GlobalTheory.ExportSeries.RestrictHalfModel in
theorem prodHalf_halfInd {m n : ℕ} {a b : AE D} (ha : a * a = a) (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) :
    prodHalf a b (halfInd b Λ) (halfInd a Λ) = halfInd (a + b) Λ := by
  classical
  funext x
  rw [prodHalf_apply]
  by_cases hx : IsHalf (a + b) x
  · have hx' : a • x + b • x = x := by rw [← add_smul]; exact (isHalf_iff' _ _).1 hx
    rw [if_pos hx, mul_one]
    unfold halfInd
    by_cases hxΛ : x ∈ Λ
    · rw [if_pos ⟨hΛ a ha x hxΛ, isHalf_smul ha x⟩, if_pos ⟨hΛ b hb x hxΛ, isHalf_smul hb x⟩, if_pos ⟨hxΛ, hx⟩, one_mul]
    · rw [if_neg (show ¬ (x ∈ Λ ∧ IsHalf (a + b) x) from fun h => hxΛ h.1)]
      by_cases h1 : a • x ∈ Λ
      · rw [if_neg (show ¬ (b • x ∈ Λ ∧ IsHalf b (b • x)) from fun h => hxΛ (hx' ▸ add_mem h1 h.1)), mul_zero]
      · rw [if_neg (show ¬ (a • x ∈ Λ ∧ IsHalf a (a • x)) from fun h => h1 h.1), zero_mul]
  · rw [if_neg hx, mul_zero]
    unfold halfInd
    rw [if_neg (show ¬ (x ∈ Λ ∧ IsHalf (a + b) x) from fun h => hx h.2)]

theorem exists_compl_idem {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)} (hsub : P₀ ⊆ P) (he : IsIdemSum e P)
    (he₀ : IsIdemSum e₀ P₀) : ∃ b, e = e₀ + b ∧ b * b = b ∧ e₀ * b = 0 := by
  classical
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := he
  obtain ⟨⟨es₀, h1₀, rfl⟩, -⟩ := he₀
  have heq : ∑ Q ∈ P₀, es₀ Q = ∑ Q ∈ P₀, es Q := Finset.sum_congr rfl fun Q hQ =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ Q Q (h1₀ Q hQ) (h1 Q (hsub hQ))).1 rfl
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' h =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ Q Q' (h1 Q hQ) (h1 Q' hQ')).2 h
  refine ⟨∑ Q ∈ P \ P₀, es Q, ?_, ?_, ?_⟩
  · rw [heq, ← Finset.sum_sdiff hsub, add_comm]
  · exact (⟨_, P \ P₀, es, fun Q hQ => (h1 Q (Finset.sdiff_subset hQ)).1,
      fun Q hQ Q' hQ' hne => horth Q (Finset.sdiff_subset hQ) Q' (Finset.sdiff_subset hQ') (Ne.symm hne), rfl⟩ :
        GlobalTheory.PlaceModelSum.IsOrthSum _) |> GlobalTheory.PlaceModelSum.IsOrthSum.idem
  · rw [heq, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun Q hQ => Finset.sum_eq_zero fun Q' hQ' =>
      horth Q (hsub hQ) Q' (Finset.sdiff_subset hQ') fun h => (Finset.mem_sdiff.1 hQ').2 (h ▸ hQ)


open GlobalTheory.HalfProd in
theorem isThetaAt_extend {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a b : AE D} {P : Finset (Pl D.host.E)} (hP : IsIdemSum (a + b) P)
    (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀)
    (hΦ : IsSBHalf a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) a
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    IsSBHalf (a + b) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
        (prodHalf a b (halfInd b (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) (a + b)
        (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀
        (prodHalf a b (halfInd b (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) Φ) f := by
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ := fun e he u hu => GlobalTheory.PlaceModelSum.idem_smul_latO he hu
  have hΨ := GlobalTheory.isSBHalf_halfInd b Λ
  refine ⟨isSBHalf_prodHalf ha hb hΛ hΨ hΦ, (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hP).exists_model hψ hS hT hP.2 hvac,
    fun T₀ hT₀ => ?_⟩
  have hm := isPlaceModel_prodHalf ha hb hab hΛ hΨ hT₀
  have key : T₀ (prodHalf a b (halfInd b Λ) (halfInd a Λ)) = f₀ := by
    rw [prodHalf_halfInd ha hb hΛ]
    have := hT₀.vac
    rwa [one_smul] at this
  rw [key] at hm
  exact hf.2 _ hm

end GlobalTheory.RowLocVec

namespace GlobalTheory.RowLocVec

theorem cosVec_isLocVec : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {_} ch => ∀ (t : T) (i : Fin D.R.m) (κ : ch.G.CosAt i), ∃ e, IsIdemSum e (locPl ch.G t) ∧ ∃ φ, IsLocVec ch.W (.chi (i : ℕ) 0) e (ch.W.vac i) φ (ch.W.cosVec i κ) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ t i κ => ?_⟩⟩
  classical
  have hL := s.core.lev
  obtain ⟨e₀, he₀, hcos⟩ := ch.W.cosVec_is
  obtain ⟨e, he⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL ch.G t
  obtain ⟨b, rfl, hb, hab⟩ := exists_compl_idem (by unfold locPl; exact Finset.subset_union_left) he he₀
  have hS : IsSelfDualC (ch.G.pS (.chi (i : ℕ) 0)) (ch.G.latS (.chi (i : ℕ) 0)) :=
    isSelfDualC_neg (node_isV ch.G hL (X := .grid ((i : ℕ) + 1) 0) ⟨i.2, Nat.zero_le _⟩).sd
  have hT : IsSelfDualC (ch.G.pT (.chi (i : ℕ) 0)) (ch.G.latT (.chi (i : ℕ) 0)) :=
    (node_isV ch.G hL (X := .grid (i : ℕ) 0) ⟨i.2.le, Nat.zero_le _⟩).sd
  have ha := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  exact ⟨e₀ + b, he, _, isThetaAt_extend ch.W.ψ_std hS hT he ha hb hab (ch.W.vac_is i i.2).2.lat
    (GlobalTheory.GridWeil.isSBHalf_cosInd hS hT (ch.G.pl.modul_ne_bot ch.sc) ha (GlobalTheory.PlaceDatum.infPart_idemSum he₀) κ)
    (hcos i i.2 κ)⟩

end GlobalTheory.RowLocVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRow_cosetVectors_isLocalThetaVector : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {_} ch => ∀ (t : T) (i : Fin D.R.m) (κ : ch.G.CosAt i), ∃ e, IsIdemSum e (locPl ch.G t) ∧ ∃ φ, IsLocVec ch.W (.chi (i : ℕ) 0) e (ch.W.vac i) φ (ch.W.cosVec i κ) := by
  first | exact @GlobalTheory.RowLocVec.cosVec_isLocVec | exact GlobalTheory.RowLocVec.cosVec_isLocVec | (intros; apply GlobalTheory.RowLocVec.cosVec_isLocVec <;> assumption)
end
end
