module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipallyPolarisedPowerUnimodularForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

def siegLamData (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := Q.B
  ab := Q.isAb
  P := abelian₂ Q.B Q.M.L
  isLB := LB.isLB_linComb Q.M.isLB _ _
  rig₁ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull Q.M.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG Q.isAb (pull_isLB (LB.isLB_linComb Q.M.isLB _ _) _) _

theorem lbIso_diag_data {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    LBIso ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left)
      (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
  have hL := Q.M.isLB
  have hT : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have hc := fun x y z => diff₃_ptCls (T := Q.B) hL hT x y z
  have hrM : Out.Rigidified Q.B Q.M.L := ⟨Q.M.rig, Q.M.rigGen⟩
  have p1 : ptCls Q.M.L Q.B 1 = 1 := ptCls_one hL hrM Q.B
  have einv : GrpObj.inv (X := Q.B) = (𝟙 Q.B)⁻¹ := by simp [Hom.inv_def]
  have key : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B) =
      ptCls Q.M.L Q.B (𝟙 Q.B) * ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹ := by
    have a := diff₂_mul_right hc (𝟙 Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹
    rw [mul_inv_cancel] at a
    have b : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) 1 = 1 := by
      simp only [diff₂, _root_.mul_one, p1, inv_one, mul_inv_cancel]
    have c : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹ =
        1 * (ptCls Q.M.L Q.B (𝟙 Q.B))⁻¹ * (ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹)⁻¹ * 1 := by
      rw [diff₂, mul_inv_cancel, p1]
    rw [b, c] at a
    exact GlobalTheory.AdjPolLocal.le_val_one_add_pow_sub a
  refine lbIso_nested hL _ _ _ _ _ _ ?_
  rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_two]
  refine (prod_lam _ _ (cls Q.M.L)).trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one]
  refine key.trans ?_
  rw [einv]
  rfl

theorem relAmple_diag {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : Data R)
    (hD : ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left).IsLB) :
    RelAmple Q.B ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left) := by
  have := Q.isAb.proper
  have hMa : IsAmpleLB Q.M.L := isAmpleLB_of_relAmple_of_isAffine Q.B Q.M.isLB Q.ample
  have hN : IsAmpleLB (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
    have := GlobalTheory.GraphVolume.isAmpleLB_graph hMa (GrpObj.inv (X := Q.B)).left (N := 1) le_rfl
    rwa [Nat.cast_one] at this
  have hDa := hN.of_lbIso hD (lbIso_diag_data Q)
  refine relAmple_of_isAmpleLB Q.B hD fun U hU => ?_
  have : CompactSpace (Q.B.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := Q.B.hom) _ U.isOpen hU.isCompact)
  exact hDa.pull_of_isOpenImmersion _

end GlobalTheory.MumFam.TensPol

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

end GlobalTheory.MumFam.TensPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipallyPolarisedPowerUnimodularForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPow

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower GlobalTheory.MumFam GlobalTheory.MumFam.TensPol

theorem exists_pow_data_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ LBIso P'.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ Q r W hpd hdet
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLamData hG Q
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hamp : RelAmple c.A c.diag := relAmple_diag Q hD
  let G := Out.powObj Q.B r
  let pr : Fin r → (G ⟶ Q.B) := Out.powPr Q.B
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ Q.B)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit Q.B r).lift (Fan.mk T y), fun u => (Out.powIsLimit Q.B r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit Q.B r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme Q.B Q.isAb r
            g := r * Q.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r Q.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (GlobalTheory.Mum.PowPol.det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam Q.M.isLB Q.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit Q.B r⟩, ?_⟩
  refine lbIso_nested Q.M.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls Q.M.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls Q.M.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.TensPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipallyPolarisedPowerUnimodularFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principally_polarised_power_unimodular_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ LBIso P'.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)) := by
  first | exact @GlobalTheory.Mum.TensPow.exists_pow_data_polAV | exact GlobalTheory.Mum.TensPow.exists_pow_data_polAV | (intros; apply GlobalTheory.Mum.TensPow.exists_pow_data_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePointCongrOneOfInvConjCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePointCongrOneOfInvConjCongr
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth.Cong

theorem count_coe_ne_zero_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {J : Ideal (𝓞 E)}
    (hJ : J ≠ ⊥) : FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 ↔ J ≤ w.asIdeal := by
  rw [FractionalIdeal.count_coe E w hJ, Nat.cast_ne_zero, Associates.count_ne_zero_iff_dvd hJ w.irreducible,
    Ideal.dvd_iff_le]

theorem val_le_one_of_mul_eq_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) K) (hHG : H * G = 1) (hH : ∀ i j, v ((1 - H) i j) < 1) (i j : Fin n) : v (G i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun k => v (G k j)) ⟨i, Finset.mem_univ _⟩
  refine (hp i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : v (G p j) ≠ 0 := (zero_lt_one.trans hlt).ne'
  have e : G = 1 + (1 - H) * G := by rw [sub_mul, hHG, one_mul]; abel
  have e2 : G p j = (1 : Matrix (Fin n) (Fin n) K) p j + ∑ k, (1 - H) p k * G k j := by
    conv_lhs => rw [e]
    rw [Matrix.add_apply, Matrix.mul_apply]
  have h1 : v ((1 : Matrix (Fin n) (Fin n) K) p j) < v (G p j) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : v (∑ k, (1 - H) p k * G k j) < v (G p j) := by
    refine v.map_sum_lt h0 fun k _ => ?_
    rw [map_mul]
    calc v ((1 - H) p k) * v (G k j) ≤ v ((1 - H) p k) * v (G p j) := by
          gcongr; exact hp k (Finset.mem_univ _)
      _ < 1 * v (G p j) := mul_lt_mul_of_pos_right (hH p k) (zero_lt_one.trans hlt)
      _ = _ := one_mul _
  have := v.map_add_lt h1 h2
  rw [← e2] at this
  exact lt_irrefl _ this

variable {D : D7}

def evAt (w : HeightOneSpectrum (𝓞 D.host.E)) : FA D →+* w.adicCompletion D.host.E where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem inv_apply {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (i j : Fin n) :
    (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j =
      Formalism.MainNotions.StandardLatticesGL3.sgA D (((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) j i) := by
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * y.1 = 1 := by
    have h2 := y.2
    change Formalism.UG.cT _ (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_left hh]
  rfl

theorem finMat_inv_mul {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : finMat y⁻¹ * finMat y = 1 := by
  unfold finMat
  have := (Matrix.map_mul (f := GlobalTheory.BotFormula.toFinE D)
    (L := (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (M := ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))).symm
  rw [this, Subgroup.coe_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem val_one_le {n : ℕ} (i j : Fin n) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v ((1 : Matrix (Fin n) (Fin n) (FA D)) i j w) ≤ 1 := by
  change Valued.v (evAt w ((1 : Matrix (Fin n) (Fin n) (FA D)) i j)) ≤ 1
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem val_sub_le {x y : FA D} {w : HeightOneSpectrum (𝓞 D.host.E)} (hx : Valued.v (x w) ≤ 1) (hy : Valued.v (y w) ≤ 1) :
    Valued.v ((x - y) w) ≤ 1 := by
  change Valued.v (evAt w (x - y)) ≤ 1
  rw [map_sub]
  exact (Valued.v.map_sub _ _).trans (max_le hx hy)

theorem integral_of_cong {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : ∀ i j, Valued.v ((1 - finMat y⁻¹) i j w) < 1) (i j : Fin n) :
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  constructor
  · refine val_le_one_of_mul_eq_one Valued.v ((finMat y).map (evAt w)) ((finMat y⁻¹).map (evAt w)) ?_ (fun a b => ?_) i j
    · rw [← Matrix.map_mul, finMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have : (1 - (finMat y⁻¹).map (evAt w)) a b = evAt w ((1 - finMat y⁻¹) a b) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [this]; exact h a b
  · have : finMat y⁻¹ i j = (1 : Matrix (Fin n) (Fin n) (FA D)) i j - (1 - finMat y⁻¹) i j := by
      rw [Matrix.sub_apply, sub_sub_cancel]
    rw [this]
    exact val_sub_le (val_one_le i j w) (h i j).le

theorem inHat_of_inv_cong : ∀ {D : D7}, (∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w') →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1) →
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
    Valued.v ((1 - finMat y⁻¹) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)))) →
  ∀ i j, InHat 1 (finMat y i j) ∧ InHat 1 (finMat y⁻¹ i j) ∧
    InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ((finMat y - 1) i j) := by
  intro D hc 𝔪 Sf hG n y hoff hcong
  obtain ⟨h0, hsup, -, hS⟩ := hG
  have h0' : D.host.conj • 𝔪 ≠ ⊥ := fun h => h0 (by
    have := congrArg (fun I => D.host.conj⁻¹ • I) h
    simpa using this)
  have hb : ∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
      Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
    intro w hw
    refine integral_of_cong y w fun i j => (hcong w hw i j).trans_lt ?_
    have h1 := (count_coe_ne_zero_iff w h0').2 hw
    have h2 := FractionalIdeal.count_coe_nonneg D.host.E w (D.host.conj • 𝔪)
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∀ i j, Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 ∧
      Valued.v ((finMat y - 1) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
        (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))) := by
    intro w i j
    by_cases hw : 𝔪 ≤ w.asIdeal
    · obtain ⟨w', e', hv, hcnt, -⟩ := hc w
      have hw' : D.host.conj • 𝔪 ≤ w'.asIdeal := by
        rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw
      have t : ∀ (z : Formalism.MainNotions.StandardLatticesGL3.GA D n) (a b : Fin n), Valued.v (finMat z a b w) = Valued.v (finMat z⁻¹ b a w') := by
        intro z a b
        unfold finMat
        rw [Matrix.map_apply, Matrix.map_apply, inv_apply, hv]
      refine ⟨(t y i j).trans_le (hb w' hw' j i).2, (t y⁻¹ i j).trans_le (by rw [inv_inv]; exact (hb w' hw' j i).1), ?_⟩
      rw [← hcnt 𝔪 h0]
      refine le_of_eq_of_le ?_ (hcong w' hw' j i)
      have e1 : (finMat y - 1) i j = GlobalTheory.BotFormula.toFinE D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      have e2 : (1 - finMat y⁻¹) j i = -GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j)) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub, Matrix.map_apply, inv_apply, neg_sub, Matrix.one_apply,
          Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (Ne.symm hij)]; simp
      rw [e1, e2, ← hv]
      exact (Valuation.map_neg _ _).symm
    · have hint : Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
        by_cases hu : w.under (𝓞 D.host.F) ∈ Sf
        · obtain ⟨w₀, hw₀, e₀⟩ := (hS _).1 hu
          obtain ⟨w', e', -, -, hun⟩ := hc w₀
          rcases (hun w).1 e₀.symm with rfl | rfl
          · exact absurd hw₀ hw
          · exact hb _ (by rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw₀) i j
        · exact hoff w hu i j
      refine ⟨hint.1, hint.2, ?_⟩
      have hz : FractionalIdeal.count D.host.E w (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
        by_contra h; exact hw ((count_coe_ne_zero_iff w h0).1 h)
      rw [hz, neg_zero, WithZero.exp_zero, Matrix.sub_apply]
      exact val_sub_le hint.1 (val_one_le i j w)
  exact fun i j => ⟨(inHat_one_iff _).2 fun w => (key w i j).1, (inHat_one_iff _).2 fun w => (key w i j).2.1,
    fun w => (key w i j).2.2⟩

end GlobalTheory.CosetOrth.Cong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePointCongrOneOfInvConjCongrStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFinitePoint_congr_one_of_inv_conj_congr : ∀ {D : D7}, (∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w') →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1) →
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
    Valued.v ((1 - finMat y⁻¹) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)))) →
  ∀ i j, InHat 1 (finMat y i j) ∧ InHat 1 (finMat y⁻¹ i j) ∧
    InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ((finMat y - 1) i j) := by
  first | exact @GlobalTheory.CosetOrth.Cong.inHat_of_inv_cong | exact GlobalTheory.CosetOrth.Cong.inHat_of_inv_cong | (intros; apply GlobalTheory.CosetOrth.Cong.inHat_of_inv_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharTraceUnitBlockTrivialOfMoves
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharTraceUnitBlockTrivialOfMoves
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CosetOrth.Pairing

variable {D : D7}

theorem cA_fin_mul (e : D.host.E) (σ : AE D) (hσ : infPart D σ = 0) :
    cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) * σ = incA D (star e) * σ := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hσ, mul_zero, mul_zero, sub_self]
  · have e1 : finPart D (cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e)) = finPart D (incA D (star e)) := rfl
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, e1, sub_self]

theorem hO_of_gram_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (x y : WO S T) :
    hO S T x y = ∑ a, ∑ c, cA D (y c a) * x c a := by
  unfold hO
  rw [hS, hT, inv_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, one_mul, mul_one]
    · intro d _ hd
      rw [Matrix.one_apply_ne (Ne.symm hd), RingHom.map_zero, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.one_apply_ne (Ne.symm hb), RingHom.map_zero, zero_mul, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

def rowMat (S T : HSp D) (p : Fin T.rank) (f : Fin S.rank → AE D) : WO S T :=
  Matrix.of fun c a => if c = p then f a else 0

theorem hO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    hO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      -(incA D (star r⁻¹) * f j) := by
  rw [hO_of_gram_one S T hS hT]
  have h1 : ∀ a, (∑ c, cA D (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank) c a) * rowMat S T p f c a) =
      incA D (star (-(r⁻¹ * if p.1 = o + a.1 then 1 else 0))) * f a := by
    intro a
    rw [Finset.sum_eq_single p]
    · have : rowMat S T p f p a = f a := if_pos rfl
      rw [this]
      exact cA_fin_mul _ _ (hf a)
    · intro c _ hc
      have : rowMat S T p f c a = 0 := if_neg hc
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_eq_single j]
  · rw [if_pos hp, mul_one, star_neg, RingHom.map_neg, neg_mul]
  · intro a _ ha
    have : ¬ p.1 = o + a.1 := fun h => ha (Fin.ext (by omega))
    rw [if_neg this, mul_zero, neg_zero, star_zero, RingHom.map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem actO_rowMat (S T : HSp D) (g : GA D S) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    actO S T g 1 (rowMat S T p (Pi.single i σ)) = rowMat S T p fun a => σ * mt S g⁻¹ i a := by
  have h1 : mt T 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [MonoidHom.map_one]; rfl
  unfold actO
  rw [h1, Matrix.one_mul]
  funext c a
  rw [Matrix.mul_apply]
  by_cases hc : c = p
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = (Pi.single i σ : Fin S.rank → AE D) k := fun k => if_pos hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = σ * mt S g⁻¹ i a := if_pos hc
    rw [e', Finset.sum_eq_single i]
    · rw [e, Pi.single_eq_same]
    · intro k _ hk
      rw [e, Pi.single_eq_of_ne hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = 0 := fun k => if_neg hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = 0 := if_neg hc
    rw [e']
    exact Finset.sum_eq_zero fun k _ => by rw [e, zero_mul]

theorem two_smul_rowMat (S T : HSp D) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    2 • rowMat S T p (Pi.single i σ) = rowMat S T p (Pi.single i (2 * σ)) := by
  funext c a
  show 2 • (if c = p then (Pi.single i σ : Fin S.rank → AE D) a else 0) =
    if c = p then (Pi.single i (2 * σ) : Fin S.rank → AE D) a else 0
  by_cases hc : c = p
  · rw [if_pos hc, if_pos hc]
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same, Pi.single_eq_same, two_nsmul, two_mul]
    · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha, nsmul_zero]
  · rw [if_neg hc, if_neg hc, nsmul_zero]

theorem hatPt_rowMat (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (f : Fin S.rank → AE D) (h0 : ∀ a, infPart D (f a) = 0) (h1 : ∀ a, InHat I (algebraMap D.host.E (FA D) r * fe D (f a))) :
    HatPt r I (rowMat S T p f) := by
  refine ⟨?_, fun c a => ?_⟩
  · funext c a
    show infPart D (if c = p then f a else 0) = 0
    split_ifs
    · exact h0 a
    · exact RingHom.map_zero _
  · show InHat I (algebraMap D.host.E (FA D) r * fe D (if c = p then f a else 0))
    split_ifs
    · exact h1 a
    · rw [RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] (x y s a b : R) : x * (y * (s * (a - b))) = x * -(y * (s * b)) + -(x * -(y * (s * a))) := by
  ring

theorem addChar_linearMap_neg_add_eq_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : AddChar R ℂ) (t : M →ₗ[R] R) (A B : M)
    (h : ψ (t A) = ψ (t B)) : ψ (t (B + -A)) = 1 := by
  rw [map_add (f := _), map_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem symplO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    symplO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * -(incA D (star r⁻¹) * f j)) :=
  congrArg (fun z => Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z)) (hO_rowMat S T hS hT r o j p hp f hf)

theorem single_inf {n : ℕ} (i : Fin n) (s : AE D) (hs : infPart D s = 0) (a : Fin n) :
    infPart D ((Pi.single i s : Fin n → AE D) a) = 0 := by
  by_cases ha : a = i
  · rw [ha, Pi.single_eq_same]; exact hs
  · rw [Pi.single_eq_of_ne ha]; exact RingHom.map_zero _

theorem hatPt_single (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0) (h1 : InHat I (algebraMap D.host.E (FA D) r * fe D σ)) :
    HatPt r I (rowMat S T p (Pi.single i σ)) :=
  hatPt_rowMat S T r I p _ (single_inf i σ hσ) fun a => by
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne ha, RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem hatPt_act (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank) (g : GA D S)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0)
    (h2 : ∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) :
    HatPt r I (actO S T g 1 (rowMat S T p (Pi.single i σ))) := by
  rw [actO_rowMat]
  refine hatPt_rowMat S T r I p _ (fun a => by rw [RingHom.map_mul, hσ, zero_mul]) fun a => ?_
  rw [RingHom.map_mul, ← mul_assoc]; exact h2 a

theorem single_eq_mul_one {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (s : R) :
    (Pi.single i s : Fin n → R) j = s * (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases ha : j = i
  · rw [ha, Pi.single_eq_same, Matrix.one_apply_eq, mul_one]
  · rw [Pi.single_eq_of_ne ha, Matrix.one_apply_ne (Ne.symm ha), mul_zero]

theorem degree_lower_bound_of_rank_split {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ψ : AddChar R ℂ) {n : ℕ} (x y s : M) (i j : Fin n)
    (N : Matrix (Fin n) (Fin n) M)
    (h : ψ (Algebra.trace R M (x * -(y * (Pi.single i s : Fin n → M) j))) = ψ (Algebra.trace R M (x * -(y * (s * N i j))))) :
    ψ (Algebra.trace R M (x * (y * (s * (1 - N) i j)))) = 1 := by
  rw [single_eq_mul_one] at h
  rw [Matrix.sub_apply, units_mul_relation_rearrange_commRing]
  exact addChar_linearMap_neg_add_eq_one ψ _ _ _ h

theorem char_trace_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
  (o : ℕ) (g : GA D S), S.gram = 1 → T.gram = 1 → o + S.rank ≤ T.rank →
  (∀ u : WO S T, HatPt r I u → HatPt r I (actO S T g 1 u) →
    ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
      ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) →
  ∀ (σ : AE D) (i j : Fin S.rank), infPart D σ = 0 → InHat I (algebraMap D.host.E (FA D) r * fe D σ) →
  (∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) →
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (2 * σ * (1 - mt S g⁻¹) i j)))) = 1 := by
  intro D ψ S T r I o g hS hT ho H σ i j hσ h1 h2
  obtain ⟨p, hp⟩ : ∃ p : Fin T.rank, p.1 = o + j.1 := ⟨⟨o + j.1, by have := j.2; omega⟩, rfl⟩
  have h2σ : infPart D (2 * σ) = 0 := by rw [RingHom.map_mul, hσ, mul_zero]
  have key := H (rowMat S T p (Pi.single i σ)) (hatPt_single S T r I p i σ hσ h1) (hatPt_act S T r I p g i σ hσ h2)
  rw [two_smul_rowMat, actO_rowMat] at key
  have a1 := symplO_rowMat S T hS hT r o j p hp _ (single_inf i _ h2σ)
  have a2 := symplO_rowMat S T hS hT r o j p hp (fun a => 2 * σ * mt S g⁻¹ i a)
    (fun a => by rw [RingHom.map_mul, h2σ, zero_mul])
  exact degree_lower_bound_of_rank_split ψ _ _ _ i j _ ((congrArg ψ a1).symm.trans (key.trans (congrArg ψ a2)))

end GlobalTheory.CosetOrth.Pairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharTraceUnitBlockTrivialOfMovesStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_trace_unitBlock_trivial_of_moves : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
  (o : ℕ) (g : GA D S), S.gram = 1 → T.gram = 1 → o + S.rank ≤ T.rank →
  (∀ u : WO S T, HatPt r I u → HatPt r I (actO S T g 1 u) →
    ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
      ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) →
  ∀ (σ : AE D) (i j : Fin S.rank), infPart D σ = 0 → InHat I (algebraMap D.host.E (FA D) r * fe D σ) →
  (∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) →
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (2 * σ * (1 - mt S g⁻¹) i j)))) = 1 := by
  first | exact @GlobalTheory.CosetOrth.Pairing.char_trace_eq_one | exact GlobalTheory.CosetOrth.Pairing.char_trace_eq_one | (intros; apply GlobalTheory.CosetOrth.Pairing.char_trace_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingsSharedBaseTowerStage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base HasExp SplitsFully Chars)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spW spW₁ alpha beta)

private theorem standing_of_rec {D : D7} {large₂ : SizeData₂ D} (hR : Rec large₂) {T : Type} {Lc : LevCh D T} {μ₀ : T} (hL : Lc.Is μ₀)
    {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) : SquareStanding G t := by
  classical
  have hx : 11 ≤ D.host.splitBound := hR.size.2.1.eleven_le
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact GlobalTheory.SquareConv.natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

section

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {μ₀ : T}

private theorem rank_weight_component_eq (hL : Lc.Is μ₀) (i j : Fin D.R.m) : (spW G i j).rank = rankV D (i + 1) (j + 1) :=
  (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩).rank

private theorem rank_W₁ (hL : Lc.Is μ₀) (i j : Fin D.R.m) : (spW₁ G i j).rank = rankV D i j :=
  (node_isV G hL (X := .grid i j) ⟨by omega, by omega⟩).rank

private theorem chs_α (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) : (GlobalTheory.SqStep.chs G i j t).α = alpha G t i j := by
  unfold alpha GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [rank_W₁ hL]
  rfl

private theorem chs_β (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) : (GlobalTheory.SqStep.chs G i j t).β = beta G i j := by
  unfold beta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [rank_W₁ hL]
  rfl

private theorem exps (hL : Lc.Is μ₀) (i j : Fin D.R.m) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding) :
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      (∀ t, HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα) ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) < mα w - mβ w := by
  choose mα hα eα using fun t => GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ) τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ) τf hτf
  refine ⟨mα μ₀, mβ, fun t => ?_, hβ, fun w => ?_⟩
  · have e : mα μ₀ = mα t := funext fun w => by
      have := (eα μ₀ w).trans (eα t w).symm
      exact_mod_cast this
    rw [e]
    exact hα t
  · have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2
    have h1 := eα μ₀ w
    have h2 := eβ w
    have : (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα μ₀ w - mβ w : ℤ) : ℚ) := by
      push_cast at h1 h2 key ⊢
      rw [h1, h2]
      linarith
    exact_mod_cast this

private theorem under_notMem (hL : Lc.Is μ₀) (t : T) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ twPl G t) :
    P ∈ Lc.Q t ∧ P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hP
  refine ⟨(Finset.mem_union.1 h1).resolve_left h2, fun h => h2 ?_⟩
  have hw : G.pl.w (P.under (𝓞 D.host.F)) ∈ G.pl.W0 := Finset.mem_image_of_mem _ h
  have hw' : G.pl.w (P.under (𝓞 D.host.F)) ∈ locPl G t := Finset.mem_union_left _ hw
  have e := GlobalTheory.FunObj.Good.under_injOn hL G t hw' h1 (G.pl.under_w h)
  rw [← e]
  exact hw

private theorem chars_good (hL : Lc.Is μ₀) (t : T) (i j : Fin D.R.m) (B : Base D.host.F D.host.E)
    (hsub : (GlobalTheory.SqStep.chs G i j t).T ⊆ B.P) (hv₁ : B.v₁ ∉ (GlobalTheory.SqStep.chs G i j t).T) (hsp : SplitsFully D.host.E B.v₁)
    (hα : HasExp B.emb (alpha G t i j) B.mα) (hβ : HasExp B.emb (beta G i j) B.mβ) :
    (GlobalTheory.SqStep.chs G i j t).IsGood B (rankV D (i + 1) (j + 1)) (rankV D i j) := by
  classical
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank (G := G) hL t i j
  rw [rank_W₁ hL] at rα
  rw [rank_weight_component_eq hL] at rβ
  have eα := chs_α (G := G) hL i j t
  have eβ := chs_β (G := G) hL i j t
  have eν : (GlobalTheory.SqStep.chs G i j t).ν = alpha G t i j / beta G i j := by
    unfold Chars.ν
    rw [eα, eβ]
  refine ⟨?_, ?_, eα ▸ GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rα, eβ ▸ GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rβ, eα ▸ hα, eβ ▸ hβ, ?_, hsub, ?_, ?_, ?_,
    ⟨hv₁, hsp⟩⟩
  · have hm := (hL.mu0 j).1
    have hx := (hL.xi t).1
    have he := hL.eta.1
    refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
    have e1 := hm.2 x
    have e2 := hx.2 x
    have e3 := he.2 x
    show Lc.mu0 ((j : ℕ) + 1) _ * Lc.xi t _ * (Lc.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply]
    rw [e1, e2, e3]
    simp
  · have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
    have he := hL.eta.1
    refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
    have e1 := hc.2 x
    have e3 := he.2 x
    show G.ch.chi (D.R.m - (i : ℕ)) _ * (Lc.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply, e1, e3]
    simp
  · refine Finset.disjoint_right.2 fun v hv hv0 => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hv
    exact (under_notMem hL t hP).2 hv0
  · intro w hw
    rw [eν]
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases (G.pl.mem_S0_of_sum_eq).1 hw with h | h
      · exact GlobalTheory.T.not_unrAt_of_under_eq_v0 hL t i j w h
      · exact GlobalTheory.T.alpha_div_beta_ramified_first hL t i j w h
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hw
      obtain ⟨h1, h2⟩ := under_notMem hL t hP
      exact GlobalTheory.T.alpha_div_beta_ramified_at_level hL t i j w P h1 e (e ▸ h2)
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ (GlobalTheory.SqStep.chs G i j t).T := hw
    rw [eα]
    have h0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (Finset.mem_union_left _ h)
    refine GlobalTheory.T.alpha_unramified_outside hL t i j w h0 fun P hP e => hw' ?_
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨P, Finset.mem_filter.2 ⟨Finset.mem_union_right _ hP, fun h => ?_⟩, e⟩)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    rw [G.pl.under_w hv] at e
    exact h0 (e ▸ hv)
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ (GlobalTheory.SqStep.chs G i j t).T := hw
    rw [eβ]
    exact GlobalTheory.T.beta_unramified_outside hL i j w (fun h => hw' (Finset.mem_union_left _ h))

end

private theorem fit_down_left_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a' : ℕ} :
    ∀ (k b : ℕ), Fit G W i j t μ₀ Bs (b + 2 * k) a' → Fit G W i j t μ₀ Bs b a'
  | 0, _, h => by simpa using h
  | k + 1, b, h => fit_down_left_mul k b (Fit.down_left (by rw [show b + 2 * k + 2 = b + 2 * (k + 1) by ring]; exact h))

private theorem fit_down_right_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a : ℕ} :
    ∀ (k b : ℕ), Fit G W i j t μ₀ Bs a (b + 2 * k) → Fit G W i j t μ₀ Bs a b
  | 0, _, h => by simpa using h
  | k + 1, b, h => fit_down_right_mul k b (Fit.down_right (by rw [show b + 2 * k + 2 = b + 2 * (k + 1) by ring]; exact h))

theorem _root_.GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w, ∀ t : T,
        ∃ Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E, Bs.emb = emb ∧ GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank := by
  classical
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ he hx hR T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j p q A A' WW X hX
  choose τf hτf using (GlobalTheory.T.exists_conj_tauE_comp_algebraMap_eq_embedding (D := D))
  refine ⟨fun w => ⟨_, hτf w⟩, fun t => ?_⟩
  have hst := standing_of_rec hR hL G t
  obtain ⟨mα, mβ, hα, hβ, hκ⟩ := exps (G := G) hL i j τf hτf
  have hloc : ∀ v ∈ (GlobalTheory.SqStep.chs G i j t).T, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv), G.pl.under_w hv⟩
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hv
      exact ⟨P, (Finset.mem_filter.1 hP).1, e⟩
  have hτ := fun v : ((GlobalTheory.SqStep.chs G i j t).T : Finset (HeightOneSpectrum (𝓞 D.host.F))) =>
    GlobalTheory.LocPlTau.exists_splitPrime_locPl hL t v.1 (hloc v.1 v.2)
  choose τP hτP using hτ
  obtain ⟨v₁, hv₁P, hv₁s, -, ⟨τ₁⟩⟩ := GlobalTheory.T.exists_splitCompletely_auxiliary_place_outside_finset (G := G) hL t (GlobalTheory.SqStep.chs G i j t).T
  let B : Base D.host.F D.host.E := ⟨W.ψ, fun w => ⟨_, hτf w⟩, mα, mβ, (GlobalTheory.SqStep.chs G i j t).T, τP, v₁, τ₁⟩
  have hB : B.IsGood D.sp.cm.sig := GlobalTheory.T.isAdmissibleCMBaseData_of_squareTupleStanding hL W t hst B rfl hloc
  have hsub₀ : (GlobalTheory.SqStep.chs G i j μ₀).T ⊆ (GlobalTheory.SqStep.chs G i j t).T := by
    rw [GlobalTheory.SqStepArith.chs_T_base G hL i j]
    exact Finset.subset_union_left
  have hfit : Fit G W i j t μ₀ B (rankV D (i + 1) (j + 1)) (rankV D i j) := by
    refine ⟨⟨rfl, subset_rfl, hB.psiP, fun v hv => ?_⟩, hB, fun w => ⟨τf w, fun _ => rfl⟩,
      chars_good hL t i j B subset_rfl hv₁P hv₁s (hα t) hβ,
      chars_good hL μ₀ i j B hsub₀ (fun h => hv₁P (hsub₀ h)) hv₁s (hα μ₀) hβ, hκ⟩
    obtain ⟨w, hw, e⟩ := hloc v.1 hv
    rw [hτP v w hw e]
    exact hw
  refine ⟨B, rfl, ?_⟩
  obtain ⟨hp, hq, hA, hA', -⟩ := hX
  have e1 : rankV D (i + 1) (j + 1) = A.rank + 2 * (pp D j - p) := by omega
  have e2 : rankV D i j = A'.rank + 2 * (qq D j - q) := by omega
  rw [e1, e2] at hfit
  exact fit_down_right_mul _ _ (fit_down_left_mul _ _ hfit)

end GlobalTheory.SqStepBig

end
end
