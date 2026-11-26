module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsCentAtScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatumFnLevPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinVecMemGLatOne
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LatRatStd

variable {D : D7}

theorem finVec_mem_gLat_one (T : HSp D) (v : Fin T.rank → D.host.E) :
    Formalism.L2.Pj.finVec T v ∈ Formalism.L2.Pj.gLat T 1 ↔ v ∈ L0c D T := by
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.mem_coe]
  obtain ⟨h1, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D T
  rw [← ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E T.rank _ hfg hsp).1 v), ← h1]
  constructor
  · rintro ⟨z, hz, e⟩
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    exact hz
  · intro h
    exact ⟨_, h, by rw [map_one, Units.val_one, Matrix.one_mulVec]; rfl⟩

theorem mem_latRat_iff_cols {S T : HSp D} (hG : S.gram = 1) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)}
    (hS : LS = (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E))) (hT : LT = L0c D T)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ GlobalTheory.LatVac.latRat S T LS LT ↔ ∀ b, (fun a => M a b) ∈ Formalism.L2.Pj.latG T 1 := by
  subst hS hT
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = star (s j) := fun s j => by
    rw [hG, Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero]) (by simp),
      Matrix.one_apply_eq, mul_one]
  constructor
  · intro hM b
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 (SetLike.mem_coe.1 hs)) b trivial)
      obtain ⟨c', hc'⟩ := GlobalTheory.DatumFourier.star_int c
      have h1 : a • t ∈ Formalism.L2.Pj.latG T 1 :=
        Submodule.subset_span ⟨a, ha, t, (finVec_mem_gLat_one T t).2 ht, rfl⟩
      convert Submodule.smul_mem _ c' h1 using 1
      funext i
      change a * t i * _ = (c' : D.host.E) * (a * t i)
      rw [hg, hc', ← hc, mul_comm]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro h
    have key : ∀ b, ∀ v ∈ Formalism.L2.Pj.latG T 1, (Matrix.of fun a j => v a * (Pi.single b 1 : Fin S.rank → D.host.E) j) ∈
        GlobalTheory.LatVac.latRat S T (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E)) (L0c D T) := by
      intro b v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hv
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single b 1, ?_, t, (finVec_mem_gLat_one T t).1 ht, ?_⟩
        · rw [SetLike.mem_coe, Formalism.L2.Pj.stdLat, Submodule.mem_pi]
          intro k _
          rw [Pi.single_apply]
          split_ifs
          · exact Submodule.mem_one.2 ⟨1, map_one _⟩
          · exact zero_mem _
        · ext i j
          simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, hg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
          split_ifs <;> simp
      | zero => convert (GlobalTheory.LatVac.latRat S T _ _).zero_mem using 1; ext i j; simp
      | add x y _ _ hx hy => convert add_mem hx hy; ext i j; simp [add_mul]
      | smul c x _ hx =>
        convert GlobalTheory.LatVac.smul_mem_latRat c hx using 1
        exact Matrix.ext fun i j => mul_assoc (c : D.host.E) (x i) _
    have e : M = ∑ b, Matrix.of fun a j => M a b * (Pi.single b 1 : Fin S.rank → D.host.E) j := by
      ext i j
      simp [Matrix.sum_apply, Pi.single_apply]
    rw [e]
    exact sum_mem fun b _ => key b _ (h b)

end GlobalTheory.LatRatStd
end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

theorem exists_split {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (l : Geo.Tor.Level H) :
    ∃ α ∈ l.Mb, ∃ β ∈ Mfr l, α + β = 1 := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by
    rw [Mfr, l.coprime]; exact Submodule.mem_top
  exact Submodule.mem_sup.1 h1

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MovedLevPoint
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.SingleDatum.MovedLevel

theorem cSep_mem {D : D7} {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) :
    cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have hex : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l := by rw [show l.Mb ⊔ Mfr l = ⊤ from l.coprime]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 this
    exact ⟨y, hy, by rw [← hxy, sub_add_cancel_right]; exact neg_mem hx⟩
  unfold cSep; rw [dite_eq_left hex]; exact hex.choose_spec

end GlobalTheory.SingleDatum.MovedLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointsTranslateMeanOfIntegralCombinat
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.ToSum

theorem exists_int_add_mul (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) (α : Af F) (hα : α ∈ intAf F) :
    ∃ ρ : 𝓞 F, ∃ β ∈ intAf F, α = algebraMap F (Af F) (ρ : F) + (M : Af F) * β := by
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.csGlob_intAdApprox F (M : 𝓞 F) (by exact_mod_cast hM.ne') α (fun v => hα v)
  refine ⟨r, y, fun v => hy v, ?_⟩
  rw [e, map_natCast]
  rfl

set_option maxHeartbeats 800000 in
theorem exists_finTens_add_nsmul {D : D7} (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (M : ℕ) (hM : 0 < M) (Y : WO V W) (hY : Y ∈ latO V W LV LW fun _ => True) :
    ∃ R ∈ GlobalTheory.LatVac.latRat V W LV LW, ∃ c ∈ latO V W LV LW (fun _ => True), Y = GlobalTheory.LatVac.finTens 1 R + M • c := by
  refine GlobalTheory.LatVac.latO_induction (p := fun Y => ∃ R ∈ GlobalTheory.LatVac.latRat V W LV LW, ∃ c ∈ latO V W LV LW (fun _ => True),
    Y = GlobalTheory.LatVac.finTens 1 R + M • c) ?_ ?_ ?_ ?_ hY
  · intro α hα R hR
    obtain ⟨ρ, β, hβ, hαe⟩ := exists_int_add_mul D.host.F M hM α hα
    refine ⟨((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ρ : 𝓞 D.host.E) : D.host.E) • R,
      GlobalTheory.LatVac.smul_mem_latRat _ hR, GlobalTheory.LatVac.finTens β R, GlobalTheory.LatVac.finTens_mem_latO hβ hR, ?_⟩
    ext i j
    simp only [GlobalTheory.LatVac.finTens, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : pairA D.host.F 0 α = (ρ : D.host.F) • pairA D.host.F 0 1 + M • pairA D.host.F 0 β := by
      rw [hαe]
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) = (ρ : D.host.F) • (0 : Ainf D.host.F) + M • (0 : Ainf D.host.F)
        simp
      · show algebraMap D.host.F (Af D.host.F) ρ + (M : Af D.host.F) * β = (ρ : D.host.F) • (1 : Af D.host.F) + M • β
        rw [Algebra.smul_def, mul_one, nsmul_eq_mul]
    have h2 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ρ : 𝓞 D.host.E) : D.host.E) * R i j =
        (ρ : D.host.F) • R i j := by
      rw [Algebra.smul_def]
      congr 1
    rw [h1, TensorProduct.add_tmul, TensorProduct.smul_tmul, h2, nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  · exact ⟨0, zero_mem _, 0, zero_mem _, by simp [GlobalTheory.LatVac.finTens_zero]⟩
  · rintro x y ⟨R, hR, c, hc, rfl⟩ ⟨R', hR', c', hc', rfl⟩
    exact ⟨R + R', add_mem hR hR', c + c', add_mem hc hc', by rw [GlobalTheory.LatVac.finTens_add, smul_add]; exact add_add_add_comm _ _ _ _⟩
  · rintro x ⟨R, hR, c, hc, rfl⟩
    exact ⟨-R, neg_mem hR, -c, neg_mem hc, by rw [GlobalTheory.LatVac.finTens_neg, smul_neg, neg_add]⟩

set_option maxHeartbeats 800000 in
theorem exists_levSum_add_of_half : ∀ (D : D7) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.gram = 1 → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ y : WO V W, IsHalf e y → l₂.M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ (x : Fin V.rank → Dw.La) (c : WO V W), c ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) ∧ y = (Matrix.of fun a b => e * incA D (ι (x b) a / (l₂.M : D.host.E)) : WO V W) + c := by
  intro D V W ΛV ΛW hV a5 a2 H Dw ι hι l₂ e he y hy hMy
  obtain ⟨P, hIS, -⟩ := he
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self hIS
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hIS
  have hMpos : 0 < l₂.M := by have := l₂.three_le; omega
  have hM0 : (l₂.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hMpos.ne'
  obtain ⟨R, hR, c, hc, hYe⟩ := exists_finTens_add_nsmul V W _ _ l₂.M hMpos _ hMy
  have hcols := (GlobalTheory.LatRatStd.mem_latRat_iff_cols hV a5 a2 R).1 hR
  have hx : ∀ b, ∃ x : Dw.La, ι x = fun a => R a b := fun b =>
    LinearMap.mem_range.1 (hι.emb.2 ▸ hcols b)
  choose x hx using hx
  have hec : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])
  refine ⟨x, e • c, GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ e hec c hc, ?_⟩
  have hyM : e • (l₂.M • y) = l₂.M • y := by
    rw [smul_comm, (GlobalTheory.SplitScalar.isHalf_iff e y).1 hy]
  have hinj : ∀ z z' : WO V W, l₂.M • z = l₂.M • z' → z = z' := fun z z' h => by
    ext a b
    have h1 := congrArg (fun m : WO V W => m a b) h
    simp only [Matrix.smul_apply, nsmul_eq_mul] at h1
    have hu : IsUnit ((l₂.M : ℕ) : AE D) := by
      rw [← map_natCast (incA D)]
      exact (IsUnit.mk0 _ hM0).map _
    exact hu.mul_left_cancel h1
  apply hinj
  rw [← hyM, hYe, smul_add, smul_add, smul_comm e l₂.M c]
  congr 1
  ext a b
  change e * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] R a b) = l₂.M • (e * incA D (ι (x b) a / (l₂.M : D.host.E)))
  have hRab : R a b = ι (x b) a := (congrFun (hx b) a).symm
  rw [hRab]
  have h2 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ι (x b) a) =
      (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] ι (x b) a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h3 : e * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = e := GlobalTheory.PlaceDatum.mul_pair_one hinf
  rw [h2, ← mul_assoc, h3, nsmul_eq_mul, ← map_natCast (incA D), mul_left_comm, ← RingHom.map_mul,
    mul_div_cancel₀ _ hM0]
  rfl

theorem sub_levPoint_mem_latO : ∀ (D : D7) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.gram = 1 → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ x : Fin V.rank → Dw.La, (Matrix.of fun a b => e * incA D (ι (x b) a / (l₂.M : D.host.E)) : WO V W) - levPoint V W l₂ ι e (fun b => Submodule.Quotient.mk (x b)) ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) := by
  intro D V W ΛV ΛW hV a5 a2 H Dw ι hι l₂ e he x
  obtain ⟨P, hIS, hPiff⟩ := he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hIS
  obtain ⟨α, hα, β, hβ, hαβ⟩ := GlobalTheory.LevPeriod.exists_split l₂
  have hM0 : (l₂.M : D.host.E) ≠ 0 := by
    have : l₂.M ≠ 0 := by have := l₂.three_le; omega
    exact_mod_cast this
  set r : Fin V.rank → Dw.La := fun b => levRep (Submodule.Quotient.mk (x b) : LevQ Dw l₂) with hr
  have hz : ∀ b, x b - cSep l₂ • r b ∈ (l₂.Mb • ⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
    intro b
    have h1 : r b - x b ∈ (l₂.Mb • ⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _
        (Submodule.Quotient.mk (x b) : LevQ Dw l₂)))
    have h2 : (cSep l₂ - 1) • r b ∈ (l₂.Mb • ⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      Submodule.smul_mem_smul (GlobalTheory.SingleDatum.MovedLevel.cSep_mem l₂).2 Submodule.mem_top
    have : x b - cSep l₂ • r b = -(r b - x b) - (cSep l₂ - 1) • r b := by rw [sub_smul, one_smul]; abel
    rw [this]
    exact sub_mem (neg_mem h1) h2
  have hw : ∀ b, ∃ w : Dw.La, β • (x b - cSep l₂ • r b) = l₂.M • w := by
    intro b
    have h1 : β • (x b - cSep l₂ • r b) ∈ (l₂.Mb * Mfr l₂) • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
      rw [mul_comm, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hβ (hz b)
    rw [Mfr, l₂.prod, Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    exact ⟨w, by rw [← hw, Nat.cast_smul_eq_nsmul]⟩
  choose w hw using hw
  by_cases hβ0 : β = 0
  · have hP0 : P = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro PP hPP
      have h1 : α ∈ PP.asIdeal := (hPiff PP).1 hPP hα
      rw [hβ0, add_zero] at hαβ
      rw [hαβ] at h1
      exact PP.isPrime.one_notMem h1
    have he0 : e = 0 := by
      obtain ⟨⟨es, -, rfl⟩, -⟩ := hIS
      rw [hP0, Finset.sum_empty]
    have h0 : (Matrix.of fun a b => e * incA D (ι (x b) a / (l₂.M : D.host.E)) : WO V W) -
        levPoint V W l₂ ι e (fun b => Submodule.Quotient.mk (x b)) = 0 := by
      ext a b
      simp [levPoint, he0]
    rw [h0]
    exact zero_mem _
  · have hβE : (β : D.host.E) ≠ 0 := fun h => hβ0 (by exact_mod_cast h)
    have hβP : ∀ PP ∈ P, β ∉ PP.asIdeal := fun PP hPP h =>
      PP.isPrime.one_notMem (hαβ ▸ add_mem ((hPiff PP).1 hPP hα) h)
    have hint := GlobalTheory.AdTh.MovedDatum.idem_div_mem hIS β hβP
    set R : Matrix (Fin W.rank) (Fin V.rank) D.host.E := Matrix.of fun a b => ι (w b) a with hRdef
    have hR : R ∈ GlobalTheory.LatVac.latRat V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) :=
      (GlobalTheory.LatRatStd.mem_latRat_iff_cols hV a5 a2 R).2 fun b => by
        rw [← hι.emb.2]
        exact ⟨w b, rfl⟩
    have hRL : GlobalTheory.LatVac.finTens 1 R ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) :=
      GlobalTheory.LatVac.finTens_mem_latO (fun v => by rw [map_one]; exact one_mem _) hR
    have hmem := GlobalTheory.LatticeStable.smul_mem_latO D V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E))
      (fun _ => True) (e * incA D ((β : D.host.E))⁻¹) hint _ hRL
    convert hmem using 1
    ext a b
    have hzb : (β : D.host.E) * ι (x b - cSep l₂ • r b) a = (l₂.M : D.host.E) * ι (w b) a := by
      have := congrFun (congrArg ι (hw b)) a
      rw [map_smul, map_nsmul, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul] at this
      exact this
    rw [map_sub, Pi.sub_apply] at hzb
    change e * incA D (ι (x b) a / (l₂.M : D.host.E)) - e * incA D (ι (cSep l₂ • r b) a / (l₂.M : D.host.E)) =
      (e * incA D ((β : D.host.E))⁻¹) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ι (w b) a)
    have h2 : (pairA D.host.F 0 1 ⊗ₜ[D.host.F] ι (w b) a) =
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] ι (w b) a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have h3 : e * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = e := GlobalTheory.PlaceDatum.mul_pair_one hinf
    rw [h2, mul_right_comm e, ← mul_assoc, h3, mul_assoc, ← mul_sub]
    change e * (incA D _ - incA D _) = e * (incA D _ * incA D _)
    rw [← RingHom.map_sub, ← RingHom.map_mul]
    congr 2
    field_simp
    linear_combination hzb

theorem heisO_add_half_lat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ x c : WO V W, IsHalf e x → c ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → IsHalf e c → heisO ψ V W (x + c) f₀ = heisO ψ V W x f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H l₂ e he x c hx hc hch
  obtain ⟨hp, -, -, -, -, -, -, -, hψ, hvac⟩ := hP
  obtain ⟨P, hIS, hPiff⟩ := he
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self hIS
  have hec : e * cA D e = 0 := hIS.2
  have hMb : ∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP =>
    (hPiff PP).1 hPP (GlobalTheory.AdTh.MovedDatum.natCast_mem_Mb l₂)
  have h2 : ∀ PP ∈ P, (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP h2
    refine PP.isPrime.one_notMem ?_
    obtain ⟨m, hm⟩ := l₂.odd
    have h1 : ((l₂.M : ℕ) : 𝓞 D.host.E) - 2 * (m : 𝓞 D.host.E) = 1 := by rw [hm]; push_cast; ring
    rw [← h1]
    exact sub_mem (hMb PP hPP) (Ideal.mul_mem_right _ _ h2)
  have ht := GlobalTheory.AdTh.MovedDatum.idem_div_mem hIS 2 h2
  have h2e : ((2 : 𝓞 D.host.E) : D.host.E) = 2 := map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2
  rw [h2e] at ht
  have hc2 : (e * incA D (2⁻¹ : D.host.E)) • c ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) :=
    GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ _ ht c hc
  have hcc : 2 • ((e * incA D (2⁻¹ : D.host.E)) • c) = c := by
    rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, Nat.cast_ofNat, mul_left_comm,
      GlobalTheory.AdTh.MovedDatum.two_mul_half, mul_one]
    exact (GlobalTheory.SplitScalar.isHalf_iff e c).1 hch
  have hfix : heisO ψ V W c f₀ = f₀ := by
    rw [← hcc]
    exact hvac.lat.1 _ hc2
  have hoff : ∀ i j, cA D e * c i j = 0 := fun i j => by
    rw [← hch i j, ← mul_assoc, mul_comm (cA D e) e, hec, zero_mul]
  have hs : symplOH V W x c = 0 := by
    rw [symplOH, GlobalTheory.Hk3.symplO_half_off V W hx hoff, mul_zero]
  have hl := GlobalTheory.PlaceModel.heisL_heisL V W ψ x c f₀
  rw [hs, AddChar.map_zero_eq_one, one_smul] at hl
  change heisO ψ V W x (heisO ψ V W c f₀) = heisO ψ V W (x + c) f₀ at hl
  rw [← hl, hfix]

theorem isHalf_levPoint {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (V W : HSp D) (l₂ : Geo.Tor.Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {e : AE D} (he : IsHalfIdem l₂ e) (q : Fin V.rank → LevQ Dw l₂) :
    IsHalf e (levPoint V W l₂ ι e q) := by
  obtain ⟨P, hP, -⟩ := he
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self hP
  intro a b
  change e * (e * _) = e * _
  rw [← mul_assoc, hee]

theorem transSum_eq {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D)
    (l₂ : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D) (f₀ : WO V W → ℂ)
    [Fintype (Fin V.rank → LevQ Dw l₂)] (u : (Fin V.rank → LevQ Dw l₂) → ℂ) :
    transSum ψ V W l₂ ι e f₀ u = ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ •
      ∑ q, u q • heisO ψ V W (levPoint V W l₂ ι e q) f₀ := by
  unfold transSum
  rw [finsum_eq_sum_of_fintype]

theorem exists_transSum_of_mem_trSp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ u : (Fin V.rank → LevQ Dw l₂) → ℂ, (∀ q, u q ∈ O) ∧ f = transSum ψ V W l₂ ι e f₀ u := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw ι hι l₂ e he _hbad O f hf
  have hP' := hP
  obtain ⟨hp, -, a1, a2, -, -, a5, -, -⟩ := hP
  haveI : Finite (LevQ Dw l₂) := GlobalTheory.AdTh.MovedSum.finite_levQ Dw l₂
  letI : Fintype (Fin V.rank → LevQ Dw l₂) := Fintype.ofFinite _
  have key : ∀ y : WO V W, IsHalf e y → l₂.M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) →
      ∃ q, heisO ψ V W y f₀ = heisO ψ V W (levPoint V W l₂ ι e q) f₀ := by
    intro y hy hMy
    obtain ⟨x, c, hc, rfl⟩ := exists_levSum_add_of_half D V W ΛV ΛW hp.std a5 a2 H Dw ι hι l₂ e he y hy hMy
    have hB := sub_levPoint_mem_latO D V W ΛV ΛW hp.std a5 a2 H Dw ι hι l₂ e he x
    set q : Fin V.rank → LevQ Dw l₂ := fun b => Submodule.Quotient.mk (x b)
    refine ⟨q, ?_⟩
    set X : WO V W := Matrix.of fun a b => e * incA D (ι (x b) a / (l₂.M : D.host.E))
    have hsplit : X + c = levPoint V W l₂ ι e q + ((X - levPoint V W l₂ ι e q) + c) := by abel
    have hl := isHalf_levPoint V W l₂ ι he q
    have hc' : IsHalf e ((X - levPoint V W l₂ ι e q) + c) := by
      have hZ : (X - levPoint V W l₂ ι e q) + c = (X + c) - levPoint V W l₂ ι e q := by abel
      rw [hZ]
      intro a b
      have h1 := hy a b
      have h2 := hl a b
      rw [Matrix.sub_apply, mul_sub, h1, h2]
    rw [hsplit]
    exact heisO_add_half_lat D ψ θ V W χV χW om ΛV ΛW sW f₀ hP' H l₂ e he _ _ hl (add_mem hB hc) hc'
  have hcard : (Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  unfold trSp at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨y, hy, hMy, rfl⟩ := hg
    obtain ⟨q₀, hq₀⟩ := key y hy hMy
    refine ⟨fun q => if q = q₀ then (Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ) else 0, fun q => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact natCast_mem O _
      · exact zero_mem O
    · rw [transSum_eq, hq₀]
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul, inv_mul_cancel₀ hcard,
        one_smul]
  | zero => exact ⟨0, fun _ => zero_mem _, by rw [transSum_eq]; simp⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨u, hu, rfl⟩ := hg
    obtain ⟨u', hu', rfl⟩ := hg'
    exact ⟨u + u', fun q => add_mem (hu q) (hu' q), by
      simp only [transSum_eq, Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add]⟩
  | smul a g _ hg =>
    obtain ⟨u, hu, rfl⟩ := hg
    refine ⟨fun q => (a : ℂ) * u q, fun q => mul_mem a.2 (hu q), ?_⟩
    rw [Subring.smul_def]
    simp only [transSum_eq, Finset.smul_sum, smul_smul]
    congr 1
    ext1 q
    congr 1
    ring

end GlobalTheory.LevelSeries.ToSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointsTranslateMeanOfIntegralCombinatStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPointsTranslateMean_of_integral_combination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ u : (Fin V.rank → LevQ Dw l₂) → ℂ, (∀ q, u q ∈ O) ∧ f = transSum ψ V W l₂ ι e f₀ u := by
  first | exact @GlobalTheory.LevelSeries.ToSum.exists_transSum_of_mem_trSp | exact GlobalTheory.LevelSeries.ToSum.exists_transSum_of_mem_trSp | (intros; apply GlobalTheory.LevelSeries.ToSum.exists_transSum_of_mem_trSp <;> assumption)
end
