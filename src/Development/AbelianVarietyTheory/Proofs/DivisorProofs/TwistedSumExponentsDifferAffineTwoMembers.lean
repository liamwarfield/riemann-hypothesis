module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationExponentOfFrameExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.TorLabel

theorem exists_torus_char : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) :=
  fun I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 => GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing I X₁ z₁ act V ev X t δ 𝔪

end GlobalTheory.GSep.TorLabel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_killed_char_of_torus_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  first | exact @GlobalTheory.GSep.TorLabel.exists_torus_char | exact GlobalTheory.GSep.TorLabel.exists_torus_char | (intros; apply GlobalTheory.GSep.TorLabel.exists_torus_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusTranslationExponentAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusCharacterUniqueStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusCharacterUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.GSep.TorCharUnique


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem equiv_of_qkToAkU {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} (hB : AdmBase R J) {D : DegData R J}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif J D A G) {k : ℕ} (hk : 1 ≤ k) (p p' : QkPt D.toPre (FractionRing R) k)
    (x : TFK (R := R) (FractionRing R) ⟶ A.A) (h : QkToAkU U.toUnifPre (FractionRing R) k p x)
    (h' : QkToAkU U.toUnifPre (FractionRing R) k p' x) : QkPt.Equiv D.toPre (FractionRing R) p p' := by
  have hL : Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  let F := AlgebraicClosure (FractionRing R)
  have hf : (algebraMap (FractionRing R) F).comp (algebraMap (FractionRing R) (FractionRing R)) =
      algebraMap (FractionRing R) F := RingHom.ext fun _ => rfl
  refine (GlobalTheory.ArcExt.equiv_qkExt_iff (algebraMap (FractionRing R) F) hf D.tau_bimult p p').1 ?_
  refine GlobalTheory.TorsionMapInj.qkToAk_injective_closed R J hB D A G hG U F k hk _ _
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ?_ ?_
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p _).2 rfl) x).1 h
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p' _).2 rfl) x).1 h'



attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem torChar_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 τ χ χ' h h'
  obtain ⟨p, x, hy, hg, hq, hx⟩ := h.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ))
  obtain ⟨p', x', hy', hg', hq', hx'⟩ := h'.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ'))
  obtain rfl : x = x' := by
    apply Over.OverMorphism.ext
    refine 𝔪.cart.1.hom_ext (hx.trans hx'.symm) ?_
    rw [Over.w, Over.w]
  have hB : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨z, hz, he⟩ := (GlobalTheory.TorusExt.equiv_iff 𝔪.D.tau_bimult _ _).1
    (equiv_of_qkToAkU hB 𝔪.semi 𝔪.U hn p p' x hq hq')
  rw [hy, hy', zero_add] at hz
  have hz0 : z = 0 := by
    have : ((X₁.S.r * X₁.S.N : ℕ) : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hz.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast (by omega))
  rw [hz0, map_zero, add_zero, hg, hg'] at he
  exact (Additive.ofMul.injective (GlobalTheory.TorusExt.torusPt_injective he)).symm

end GlobalTheory.GSep.TorCharUnique
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_torus_character_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  first | exact @GlobalTheory.GSep.TorCharUnique.torChar_unique | exact GlobalTheory.GSep.TorCharUnique.torChar_unique | (intros; apply GlobalTheory.GSep.TorCharUnique.torChar_unique <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberLiesOverRescaleFramesStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberLiesOverRescaleFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep

theorem over_rescale : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ g w w' x e e' l hl he hw H k hk wk' hwk' hgen s s' v hs hv
  have hlk : l ^ k ≠ 0 := pow_ne_zero k hl
  obtain ⟨wk, hwkg, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale wk' hgen hlk
  have h₁ : ValAt s x e (l ^ k * v) := fun z J hJ => by
    rw [hv z J hJ]
    have r₁ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    have r₂ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e' (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e' (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    rw [r₁, r₂, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, GlobalTheory.Poinc.TorsRatio.cst_eq_cstK, map_mul, map_pow]
    ring
  have h₂ := H k hk wk (fun z J hJ => Units.ext (by
    rw [hwk z J hJ, hwk' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, map_pow])) hwkg s s' _ hs h₁
  have h₃ := GlobalTheory.Poinc.Sep.sumF_const_mul (l ^ k)⁻¹ h₂
  simpa only [GlobalTheory.UT.TorsionValue.coef_scale hgen hwk, inv_mul_cancel_left₀ hlk] using h₃

end GlobalTheory.GSep
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_lies_over_rescale_frames : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  first | exact @GlobalTheory.GSep.over_rescale | exact GlobalTheory.GSep.over_rescale | (intros; apply GlobalTheory.GSep.over_rescale <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.Poinc.TorsRatio

theorem torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V))) (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' → ∃ l : FractionRing V, l ^ (N ^ 2) = 1 ∧ ∀ z J, Good A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  intro V _ _ A ρA _ N _ x e e' H H'
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'
  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J →
      Geo.Tor.val α r z J = Geo.Tor.val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    have hu : IsUnit ((Geo.Tor.val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
    have h1 : cstK z (l ^ (N ^ 2)) = cstK z 1 := by
      rw [map_one]
      exact hu.mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
    exact (cstK z).injective h1
  exact ⟨l, hlN, hl⟩

end GlobalTheory.GSep.FrameExpEx

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.GSep.TwistTranslate


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a ha τ hτ
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V ev Y t δ 𝔪 a ha
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, -⟩ := hT
  obtain ⟨χ₀, hχ₀, hyp⟩ := GlobalTheory.T.exists_level_killed_char_of_torus_label I X₁ z₁ act V ev Y t δ 𝔪 τ hτ
  have hT₀ : GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ₀ := ⟨hχ₀, hyp⟩
  obtain ⟨ρA, hρA, htors⟩ := exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ₀ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ₀)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' ()) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w₂, hw₂g, hw₂v⟩ : ∃ w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b,
      w₂.IsGen ∧ ∀ z J, val w₂ (𝟙 _) z J = val (w ()) (𝟙 _) z J := by
    revert hb
    generalize (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b = b
    rintro rfl
    exact ⟨w (), (hc ()).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := over_translate 𝔪 w₀ hw₀ ρA hρA (x a) (fr a) (htors _)
    (g' ()) (w ()) (hc ()).1 (hc ()).2.1 (hc ()).2.2 χ₀ hχ₀ _ hg₀ p xτ hpy hpg hq _ hadd w₂ (fun z J _ => hw₂v z J)
    (x (a + τ)) (x_add 𝔪 x hx a τ xτ hxτ)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  obtain ⟨l, hl, hlv⟩ := torsFrame_ratio V 𝔪.A ρA hρA _ hN _ _ _ he₂ (htors (a + τ))
  obtain ⟨e, he⟩ := eq_yK_zeta_pow 𝔪 l hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hl
    exact zero_ne_one hl
  refine ⟨e, ⟨χ₀, hT₀⟩, x, fr, th, w₀, s, g' (), w (), hx, hfr, hth, hw₀, hs, (hc ()).1, (hc ()).2.1, (hc ()).2.2, ?_⟩
  intro χ hχ g₀ hg₀' g'' hadd'' w'' _ hval
  obtain rfl : χ₀ = χ := GlobalTheory.T.thetaMember_torus_character_unique I X₁ z₁ act V ev Y t δ 𝔪 τ χ₀ χ hT₀ hχ
  obtain rfl : g₀ = GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀) :=
    (GlobalTheory.TorusExt.isTorusPtF_iff_eq g₀ χ₀).1 ((isTor_iff _ _).1 hg₀')
  obtain rfl := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd''
  refine GlobalTheory.T.thetaMember_lies_over_rescale_frames I X₁ z₁ act V ev Y t δ 𝔪 w₀ _ w₂ w'' (x (a + τ)) e₂ (fr (a + τ)) l hl0 hlv (fun z J hJ => ?_) hov
  rw [hw₂v, hval z J hJ, he]

end GlobalTheory.GSep.FrameExpEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsFrameExponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_exists_frame_exponent : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e := by
  first | exact @GlobalTheory.GSep.FrameExpEx.exists_frExp | exact GlobalTheory.GSep.FrameExpEx.exists_frExp | (intros; apply GlobalTheory.GSep.FrameExpEx.exists_frExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentsAffineTwoMembers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentSecondDifferenceConstantMembers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentSecondDifferenceConstantMembers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.GSep.FrExpCube
open GlobalTheory.UT.TorsionValue GlobalTheory.Poinc.Tors GlobalTheory.Poinc.CubeConst

theorem frame_cube_const : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  intro I X₁ z₁ act
  have := X₁.ar.ded
  have : IsNoetherianRing X₁.S.R := isNoetherianRing_of_fg X₁.S.fg
  have : IsLocallyNoetherian (Sp X₁.S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.S.R)))
  have := X₁.ρ.P.isAb.comm
  obtain ⟨c₀⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp X₁.S.R) X₁.ρ.P ⟨X₁.ρ.P.L, X₁.ρ.rig, X₁.ρ.P.isLB, X₁.ρ.rig_gen⟩ rfl).1
  choose k hk using exists_cube_const c₀ X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.fr (fun a => (X₁.ρ.fr_tors a).2.1)
  refine ⟨fun a a' a'' => (Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''), fun a a' a'' => ?_, ?_⟩
  · rw [← map_pow]
    refine Eq.trans (congrArg _ (fn_ext (b := 1) fun y _ => ?_)) (map_one _)
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB y
    have e := hk a a' a'' _ (𝟙 _) y J hJ
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at e
    have e' := congrArg Units.val (cube_torsFrame_pow GlobalTheory.firstFiveLaws.1.globalFns X₁.ρ.P c₀ X₁.ρ.pt X₁.ρ.pt_add
      X₁.ρ.fr X₁.ρ.fr_tors a a' a'' y J hJ)
    have e'' := (congrArg (· ^ ((X₁.S.r * X₁.S.N) ^ 2)) e).symm.trans ((Units.val_pow_eq_pow_val _ _).symm.trans e')
    rw [gs_eq _ y ⊤ trivial, ← map_pow, ← map_pow] at e''
    rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_one, map_one]
    exact e''
  intro V _ _ _ ev X _ t δ 𝔪 x fr hx hfr ρ hρ c a a' a'' z JA hJA
  have := 𝔪.A.isAb.comm
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB z
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have hp : ∀ b, pushHom 𝔪.cart (TFK (R := V) (FractionRing V)) (x b) = U ≫ X₁.ρ.pt b := fun b =>
    Over.OverMorphism.ext (hx b)
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx b b' (x b') (hx b')
  have h0 : x 0 = 1 := mul_eq_left.1 ((hadd 0 0).symm.trans (by rw [add_zero]))
  have e₁ := cubV_through GlobalTheory.firstFiveLaws.1.globalFns 𝔪.A.isAb 𝔪.cart c₀ c 𝔪.wl 𝔪.wl_gen
    (T := TFK (R := V) (FractionRing V)) z hJ hJA (x a) (x a') (x a'')
  rw [hp, hp, hp, ← hadd, ← hadd, ← hadd, ← hadd, ← h0] at e₁
  have e₂ := hk a a' a'' _ U z J hJ
  have e₃ : gs U.left z ⊤ (k a a' a'') = GlobalTheory.UT.cst (FractionRing V) z
      (𝔪.yK ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom.hom (k a a' a''))) := by
    refine Eq.trans ?_ (Geo.Tor.cst_comp (𝟙 _) 𝔪.yK z _)
    rw [Category.id_comp]
    exact congrArg (gs (spMap 𝔪.yK) z ⊤) ((Scheme.ΓSpecIso (CommRingCat.of X₁.S.R)).hom_inv_id_apply _).symm
  have alg : ∀ {R : Type} [CommRing R] {κ : R} {c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ : Rˣ},
      c₀ = w₁ * w₂⁻¹ * w₃⁻¹ * w₄⁻¹ * w₅ * w₆ * w₇ * w₈⁻¹ * c →
      (c₀ * ((g₂ * g₃ * g₄ * g₈) * (g₁ * g₅ * g₆ * g₇)⁻¹)).val = κ →
      w₁ * f₁ = g₁ → w₂ * f₂ = g₂ → w₃ * f₃ = g₃ → w₄ * f₄ = g₄ → w₅ * f₅ = g₅ → w₆ * f₆ = g₆ → w₇ * f₇ = g₇ →
      w₈ * f₈ = g₈ → (c * (f₂ * f₃ * f₄ * f₈)).val = κ * (f₁ * f₅ * f₆ * f₇).val := by
    rintro R _ κ c c₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
    rw [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact alg e₁ (e₂.trans e₃) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA) ((hfr _).2 z J JA hJ hJA)
    ((hfr _).2 z J JA hJ hJA)

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem cube_alg {S : Type} [CommRing S] {A C D B₀ B₁ B₂ B₃ B₁₂ B₁₃ B₂₃ B₁₂₃ : Sˣ} {k v₀ v₁ v₂ v₁₂ : S}
    (E : A * (B₁₂₃ * B₁ * B₂ * B₃) * C = D * (B₁₂ * B₁₃ * B₂₃ * B₀)) (K : D.val = k * A.val)
    (h₀ : B₃.val = v₀ * B₀.val) (h₁ : B₁₃.val = v₁ * B₁.val) (h₂ : B₂₃.val = v₂ * B₂.val)
    (h₁₂ : B₁₂₃.val = v₁₂ * B₁₂.val) : v₁₂ * v₀ * C.val = k * v₁ * v₂ := by
  have E' := congrArg Units.val E
  simp only [Units.val_mul, K, h₀, h₁, h₂, h₁₂] at E'
  refine (A * B₀ * B₁ * B₂ * B₁₂).mul_right_inj.1 ?_
  simp only [Units.val_mul]
  linear_combination E'

theorem cube_rel (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R}
    {x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)}
    {fr : ∀ a, FrAt (x a)} (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) (hfr : ∀ a, (fr a).IsGen)
    {ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))} {hρ : ρ.IsGen} (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩)
    (hκ : ∀ (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val)
    {w₀ : W0 𝔪.U.toUnifPre} (hw₀ : w₀.IsGen) {H : AddSubgroup X₁.S.Gam} {τ : X₁.S.Gam}
    {g₁ g₂ : H → GtPtF 𝔪.D.toPre (FractionRing V)} {w₁ : ∀ b, Frm 𝔪.D.toPre (FractionRing V) 1 (g₁ b).b}
    {w₂ : ∀ b, Frm 𝔪.D.toPre (FractionRing V) 1 (g₂ b).b} {v : H → FractionRing V}
    (h₁ : ∀ b, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g₁ b) o ∧ o.IsZero) ∧ (w₁ b).IsGen ∧
      𝔪.Over' w₀ (g₁ b) (w₁ b) (x b) (fr b))
    (h₂ : ∀ b, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g₂ b) o ∧ o.IsZero) ∧ (w₂ b).IsGen ∧
      𝔪.Over' w₀ (g₂ b) (w₂ b) (x (b + τ)) (fr (b + τ)))
    (hb : ∀ b, (g₂ b).b = (g₁ b).b)
    (hv : ∀ b z J, Good 𝔪.D.toPre.P.L z J → (val (w₂ b) (𝟙 _) z J).val = cstH z (v b) * (val (w₁ b) (𝟙 _) z J).val)
    (a a' : H) (z : (TF (R := V) (FractionRing V)).left) {JB} (hJB : Good 𝔪.D.toPre.P.L z JB) :
    cstH z (v (a + a') * v 0) * (cubV 𝔪.D.toPre.cub z JB (g₁ a).b (g₁ a').b (g₁ 0).b).val =
      cstH z (𝔪.yK (κ a a' τ) * v a * v a') := by
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx b b' (x b') (hx b')
  have hx0 : x 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  obtain ⟨JA, hJA⟩ := exists_good' 𝔪.A.isLB z
  let P : (X₁.S.Gam × Σ g' : GtPtF 𝔪.D.toPre (FractionRing V), Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) → Prop := fun q =>
    (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) q.2.1 o ∧ o.IsZero) ∧ q.2.2.IsGen ∧ (fr q.1).IsGen ∧
      LiesOver 𝔪.U.toUnifPre w₀ q.2.1 q.2.2 (x q.1) (fr q.1)
  have p₁ : ∀ b : H, P ⟨b, g₁ b, w₁ b⟩ := fun b => ⟨(h₁ b).1, (h₁ b).2.1, hfr _, (h₁ b).2.2⟩
  have p₂ : ∀ b : H, P ⟨b + τ, g₂ b, w₂ b⟩ := fun b => ⟨(h₂ b).1, (h₂ b).2.1, hfr _, (h₂ b).2.2⟩
  have p₃ : P ⟨τ, g₂ 0, w₂ 0⟩ := by
    have := p₂ 0
    rwa [AddSubgroup.coe_zero, zero_add] at this
  obtain ⟨f, hP, f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇⟩ : ∃ f : Finset (Fin 3) →
      (X₁.S.Gam × Σ g' : GtPtF 𝔪.D.toPre (FractionRing V), Frm 𝔪.D.toPre (FractionRing V) 1 g'.b), (∀ S, P (f S)) ∧
      f ∅ = ⟨0, g₁ 0, w₁ 0⟩ ∧ f {0} = ⟨a, g₁ a, w₁ a⟩ ∧ f {1} = ⟨a', g₁ a', w₁ a'⟩ ∧ f {2} = ⟨τ, g₂ 0, w₂ 0⟩ ∧
      f {0, 1} = ⟨a + a', g₁ (a + a'), w₁ (a + a')⟩ ∧ f {0, 2} = ⟨a + τ, g₂ a, w₂ a⟩ ∧
      f {1, 2} = ⟨a' + τ, g₂ a', w₂ a'⟩ ∧ f {0, 1, 2} = ⟨a + a' + τ, g₂ (a + a'), w₂ (a + a')⟩ := by
    refine ⟨fun S => if 2 ∈ S then
        (if 0 ∈ S then (if 1 ∈ S then ⟨a + a' + τ, g₂ (a + a'), w₂ (a + a')⟩ else ⟨a + τ, g₂ a, w₂ a⟩)
          else if 1 ∈ S then ⟨a' + τ, g₂ a', w₂ a'⟩ else ⟨τ, g₂ 0, w₂ 0⟩)
      else (if 0 ∈ S then (if 1 ∈ S then ⟨a + a', g₁ (a + a'), w₁ (a + a')⟩ else ⟨a, g₁ a, w₁ a⟩)
          else if 1 ∈ S then ⟨a', g₁ a', w₁ a'⟩ else ⟨0, g₁ 0, w₁ 0⟩), fun S => ?_, ?_⟩
    · dsimp only
      split_ifs
      exacts [p₂ (a + a'), p₂ a, p₂ a', p₃, p₁ (a + a'), p₁ a, p₁ a', p₁ 0]
    · simp
  have E := GlobalTheory.T.framed_torsion_torus_extension_respect_cubical V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk ρ hρ c (fun S => (f S).2.1) (fun S => (f S).2.2)
    (fun S => x (f S).1) (fun S => fr (f S).1) (by simp only [f₀, hx0]) (by simp only [f₁, f₂, f₄, hadd])
    (by simp only [f₁, f₃, f₅, hadd]) (by simp only [f₂, f₃, f₆, hadd]) (by simp only [f₁, f₂, f₃, f₇, hadd]) hP
    z JA JB hJA hJB
  beta_reduce at E
  rw [f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇] at E
  dsimp only at E
  have := cube_alg E (hκ a a' τ z JA hJA) (hv 0 z JB hJB) (hv a z JB hJB) (hv a' z JB hJB) (hv (a + a') z JB hJB)
  rw [hb 0, cst_eq] at this
  rw [map_mul, map_mul, map_mul, this]

theorem prim_ring : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ((X₁.S.r * X₁.S.N) ^ 2) := by
  refine X₁.S.prim.map_of_injective fun a b hab => X₁.ar.inj ?_
  simpa using congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab

theorem prim_member (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) :
    IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) ((X₁.S.r * X₁.S.N) ^ 2) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have h := ((prim_ring (X₁ := X₁)).isRoot_cyclotomic hk).map (f := 𝔪.yK)
  rw [Polynomial.map_cyclotomic] at h
  haveI : NeZero ((((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) : FractionRing V) := ⟨by exact_mod_cast hk.ne'⟩
  exact Polynomial.isRoot_cyclotomic_iff.1 h

theorem exp_eq (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {p q : ℕ}
    (h : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ p) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ q)) :
    (p : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = q := by
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have hp := prim_member 𝔪
  rw [map_pow, map_pow, (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hk, hp.pow_eq_one⟩).pow_eq_pow_iff_modEq, ← hp.eq_orderOf] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem lifts_of_frExp (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
    {x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)} {fr : ∀ a, FrAt (x a)}
    (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J)
    {w₀ : W0 𝔪.U.toUnifPre} (hw₀ : w₀.IsGen) {a τ : X₁.S.Gam} {e : ℕ} (H : GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e) :
    ∃ (g₁ g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b)
      (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
      ((∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) ∧ w₁.IsGen ∧ 𝔪.Over' w₀ g₁ w₁ (x a) (fr a)) ∧
      ((∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) ∧ w₂.IsGen ∧ 𝔪.Over' w₀ g₂ w₂ (x (a + τ)) (fr (a + τ))) ∧
      g₂.b = g₁.b ∧ ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w₂ (𝟙 _) z J).val =
        cstH z (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ^ e)⁻¹ * (val w₁ (𝟙 _) z J).val := by
  obtain ⟨⟨χ, hχ⟩, x', fr', th, w₀', s, g₁, w, hx', hfr', -, hw₀', -, htor, hw, hov, htr⟩ := H
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (𝔪.cart.1.hom_ext ((hx a).trans (hx' a).symm) ((Over.w (x a)).trans (Over.w (x' a)).symm))
  have hf : ∀ a z J, Good 𝔪.A.L z J → val (fr a) (𝟙 _) z J = val (fr' a) (𝟙 _) z J := fun a z J hJ => by
    obtain ⟨J₀, hJ₀⟩ := exists_good' X₁.ρ.P.isLB z
    exact mul_left_cancel (((hfr a).2 z J₀ J hJ₀ hJ).trans ((hfr' a).2 z J₀ J hJ₀ hJ).symm)
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.Poinc.Sep.TermsCompare.exists_expandsF_pow 𝔪.U.toUnifPre (FractionRing V) hw₀' hw₀
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have hu : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ^ e ≠ 0 := pow_ne_zero _ ((prim_member 𝔪).ne_zero hk.ne')
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (GlobalTheory.UT.isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq g₁ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w', hw'g, hw'v⟩ : ∃ w' : Frm 𝔪.D.toPre (FractionRing V) 1
      (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w'.IsGen ∧ ∀ z J, val w' (𝟙 _) z J = val w (𝟙 _) z J := by
    revert hb
    generalize (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w, hw, fun _ _ => rfl⟩
  obtain ⟨w'', hw''g, hw''v⟩ := exists_frm_scale w' hw'g (inv_ne_zero hu)
  have hov₂ := htr χ hχ _ hg₀ _ hadd w'' hw''g (fun z J hJ => by
    rw [hw''v z J hJ, hw'v, cst_eq, ← _root_.mul_assoc, ← map_mul, map_pow, map_pow, mul_inv_cancel₀ hu, map_one,
      _root_.one_mul])
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_frm_scale w hw hd0
  obtain ⟨w₂, hw₂, hv₂⟩ := exists_frm_scale w'' hw''g hd0
  refine ⟨g₁, _, w₁, w₂, ⟨htor, hw₁, GlobalTheory.Poinc.Sep.TermsCompare.liesOver_change hd hw hv₁ (hf _) hov⟩,
    ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₂,
      GlobalTheory.Poinc.Sep.TermsCompare.liesOver_change hd hw''g hv₂ (hf _) hov₂⟩, hb, fun z J hJ => ?_⟩
  · obtain ⟨o, ho, ho'⟩ := htor
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
      ← ofMul_pow, hχ.1, ofMul_one, map_zero, add_zero]
  · rw [hv₂ z J hJ, hw''v z J hJ, hw'v, hv₁ z J hJ, cst_eq, cst_eq]
    ring

theorem frExp_second_diff : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ c : X₁.S.Gam → X₁.S.Gam → ZMod ((X₁.S.r * X₁.S.N) ^ 2), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (E : X₁.S.Gam → ℕ), (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ (E a)) → ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ b ∈ X₁.S.HH X₁.M z₁, ((E (a + b) : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E b : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) + ((E 0 : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = c a b := by
  intro I X₁ z₁ act x₀ _ τ _
  obtain ⟨κ, hκ1, hκ⟩ := frame_cube_const I X₁ z₁ act
  haveI : NeZero ((X₁.S.r * X₁.S.N) ^ 2) :=
    ⟨(pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2).ne'⟩
  choose k hk' hk using fun a a' a'' => (prim_ring (X₁ := X₁)).eq_pow_of_pow_eq_one (hκ1 a a' a'')
  refine ⟨fun a b => (k a b 0 : ZMod _) - (k a b τ : ZMod _), ?_⟩
  intro V _ _ _ ev Y _ t δ 𝔪 E hE a ha a' ha'
  obtain ⟨-, x, fr, -, w₀, -, -, -, hx, hfr, -, hw₀, -⟩ := hE a ha
  choose g₁ g₂ w₁ w₂ h₁ h₂ hb hv using fun b : X₁.S.HH X₁.M z₁ => lifts_of_frExp 𝔪 hx hfr hw₀ (hE b b.2)
  obtain ⟨ρA, hρA, -⟩ := GlobalTheory.GSep.TwistTranslate.exists_rig_torsFrame 𝔪 x fr hx hfr
  obtain ⟨z⟩ : Nonempty (TF (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' 𝔪.D.toPre.P.isLB z
  obtain ⟨c⟩ := (GlobalTheory.firstFiveLaws.1.cube _ 𝔪.A ⟨𝔪.A.L, ρA, 𝔪.A.isLB, hρA⟩ rfl).1
  have K := hκ V ev Y t δ 𝔪 x fr hx hfr ρA hρA c
  have E₁ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ h₁ h₂ hb hv ⟨a, ha⟩ ⟨a', ha'⟩ z hJ
  have E₀ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ (τ := 0) (v := fun _ => 1) h₁
    (fun b => by rw [add_zero]; exact h₁ b) (fun _ => rfl) (fun b z J _ => by rw [map_one, _root_.one_mul])
    ⟨a, ha⟩ ⟨a', ha'⟩ z hJ
  simp only [_root_.mul_one, map_one, _root_.one_mul] at E₀
  rw [E₀, ← map_mul] at E₁
  have E' := cstH_inj z E₁
  have hu : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ≠ 0 := (prim_member 𝔪).ne_zero (NeZero.ne _)
  rw [← hk, ← hk] at E'
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_zero, map_pow] at E'
  have q : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (k a a' 0 + E a + E a')) =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (k a a' τ + E (a + a') + E 0)) := by
    simp only [map_mul, map_pow, pow_add]
    generalize 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) = y at hu E' ⊢
    have fin : ∀ p q r s k₀ k₁ : FractionRing V, p ≠ 0 → q ≠ 0 → r ≠ 0 → s ≠ 0 →
        r⁻¹ * s⁻¹ * k₀ = k₁ * p⁻¹ * q⁻¹ → k₀ * p * q = k₁ * r * s := fun p q r s k₀ k₁ hp hq hr hs h => by
      field_simp at h
      linear_combination h
    exact fin _ _ _ _ _ _ (pow_ne_zero _ hu) (pow_ne_zero _ hu) (pow_ne_zero _ hu) (pow_ne_zero _ hu) E'
  have b₁ := exp_eq 𝔪 q
  push_cast at b₁
  linear_combination -b₁

end GlobalTheory.GSep.FrExpCube
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentSecondDifferenceConstantMembersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameExponent_second_difference_constant_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ c : X₁.S.Gam → X₁.S.Gam → ZMod ((X₁.S.r * X₁.S.N) ^ 2), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (E : X₁.S.Gam → ℕ), (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ (E a)) → ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ b ∈ X₁.S.HH X₁.M z₁, ((E (a + b) : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E b : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) + ((E 0 : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = c a b := by
  first | exact @GlobalTheory.GSep.FrExpCube.frExp_second_diff | exact GlobalTheory.GSep.FrExpCube.frExp_second_diff | (intros; apply GlobalTheory.GSep.FrExpCube.frExp_second_diff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentsAffineTwoMembers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

theorem affine_on_subgroup_of_second_diff {G : Type*} [AddCommGroup G] (H : AddSubgroup G) {R : Type*} [AddCommGroup R]
    (D : G → R) (hD : ∀ a ∈ H, ∀ b ∈ H, D (a + b) - D a - D b + D 0 = 0) :
    ∃ (κ : R) (h : H →+ R), ∀ (a : G) (ha : a ∈ H), D a = κ + h ⟨a, ha⟩ := by
  refine ⟨D 0, AddMonoidHom.mk' (fun x : H => D x - D 0) ?_, ?_⟩
  · intro x y
    have := hD x x.2 y y.2
    simp only [AddSubgroup.coe_add]
    rw [← sub_eq_zero]
    rw [← this]; abel
  · intro a ha
    simp

theorem frExp_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1), ∀ (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ E1 E2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪1 a τ (E1 a)) → (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪2 a τ (E2 a)) → ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro I X₁ z₁ act x₀ hdiv V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ E1 E2 h1 h2
  obtain ⟨c, hc⟩ := GlobalTheory.T.frameExponent_second_difference_constant_members I X₁ z₁ act x₀ hdiv τ hτ
  have k1 := hc V1 ev1 Y1 t1 δ1 𝔪1 E1 h1
  have k2 := hc V2 ev2 Y2 t2 δ2 𝔪2 E2 h2
  refine affine_on_subgroup_of_second_diff (X₁.S.HH X₁.M z₁)
    (fun a => ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2))) ?_
  intro a ha b hb
  have e1 := k1 a ha b hb
  have e2 := k2 a ha b hb
  rw [← sub_eq_zero.mpr (e1.trans e2.symm)]
  abel

end GlobalTheory.GSep.TransTerms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentsAffineTwoMembersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameExponents_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1), ∀ (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ E1 E2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪1 a τ (E1 a)) → (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪2 a τ (E2 a)) → ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.GSep.TransTerms.frExp_affine_two_members | exact GlobalTheory.GSep.TransTerms.frExp_affine_two_members | (intros; apply GlobalTheory.GSep.TransTerms.frExp_affine_two_members <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusTranslationExponentAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

theorem trans_exp_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  classical
  intro I X₁ z₁ act x₀ hd V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ
  let E1 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ) else 0
  let E2 : X₁.S.Gam → ℕ := fun a => if ha : a ∈ X₁.S.HH X₁.M z₁ then
    Classical.choose (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ) else 0
  have h1 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪1 a τ (E1 a) := fun a ha => by
    simp only [E1, dif_pos ha]
    exact Classical.choose_spec (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ)
  have h2 : ∀ a ∈ X₁.S.HH X₁.M z₁, FrExp 𝔪2 a τ (E2 a) := fun a ha => by
    simp only [E2, dif_pos ha]
    exact Classical.choose_spec (GlobalTheory.T.thetaMember_exists_frame_exponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ)
  exact ⟨E1, E2, fun a ha => GlobalTheory.T.translationExponent_of_frameExponent I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 a ha τ hτ _ (h1 a ha),
    fun a ha => GlobalTheory.T.translationExponent_of_frameExponent I X₁ z₁ act x₀ hd V2 ev2 Y2 t2 δ2 𝔪2 a ha τ hτ _ (h2 a ha),
    GlobalTheory.T.frameExponents_affine_two_members I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 V2 ev2 Y2 t2 δ2 𝔪2 τ hτ E1 E2 h1 h2⟩

end GlobalTheory.GSep.TransTerms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusTranslationExponentAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_torus_translation_exponent_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.GSep.TransTerms.trans_exp_affine | exact GlobalTheory.GSep.TransTerms.trans_exp_affine | (intros; apply GlobalTheory.GSep.TransTerms.trans_exp_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsTorusTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsTorusTranslate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TermsExt
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

theorem exists_frAt_ratio {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {K : Type} [Field K] [Algebra (FractionRing R) K] {x : TFK (R := R) K ⟶ A.A} {e e' : FrAt x} (he : e.IsGen)
    (he' : e'.IsGen) : ∃ c : K, c ≠ 0 ∧ ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := R) K).left.presheaf.stalk z) (cstH (R := R) z c) * (val e (𝟙 _) z J).val := by
  obtain ⟨z⟩ : Nonempty (TFK (R := R) K).left := exists_pt (R := R) (F := K)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB z
  obtain ⟨c, hc⟩ := cstH_surj (R := R) (F := K) z (val e' (𝟙 _) z J' * (val e (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl : z = z' := pt_eq (R := R) (F := K) z z'
    rw [hc, val_tr he (𝟙 _) hJ hJ', val_tr he' (𝟙 _) hJ hJ']
    refine Eq.trans ?_ (Units.val_mul _ _)
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem over_scale {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {w₀ : W0 𝔪.U.toUnifPre} {g' : GtPtF 𝔪.D.toPre (FractionRing V)}
    {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b} (hw : w.IsGen) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {e e' : FrAt x} {c : FractionRing V} (hc : c ≠ 0)
    (he : ∀ z J, Good 𝔪.A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) * (val e (𝟙 _) z J).val)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w' (𝟙 _) z J).val = cst (FractionRing V) z c⁻¹ * (val w (𝟙 _) z J).val)
    (h : 𝔪.Over' w₀ g' w x e) : 𝔪.Over' w₀ g' w' x e' := by
  intro k hk wk' hwk' _ s s' v hs hval
  obtain ⟨wk, hwk, hwkv⟩ := exists_frm_pow w hw k
  have pf : ∀ (e : FrAt x) z J, val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = val e (𝟙 _) z J ^ k :=
    fun e z J => (map_zpow _ _ _).trans (zpow_natCast _ _)
  have hval' : ValAt s x e (c ^ k * v) := fun z J hJ => by
    have cm : @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z (c ^ k * v)) =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) ^ k *
          @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z v) :=
      (cst_eq (R := V) z _).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (map_pow _ _ _) (cst_eq (R := V) z _).symm))
    rw [hval z J hJ, pf, pf, cm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    ring
  have S := sumF_const_mul (c⁻¹ ^ k) (h k hk wk hwkv hwk s s' _ hs hval')
  have sc := coef_scale (w' := wk') hwk (c := c⁻¹ ^ k) (fun z J hJ => by
    rw [hwk' z J hJ, hwkv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      cst_eq, cst_eq, map_pow]) s'
  rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, _root_.one_mul] at S
  simpa only [← sc] using S


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_terms_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : X → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  intro I X₁ z₁ act x₀ _ V _ _ _ ev X _ t δ 𝔪 C lab _ T hT c τ hτ
  obtain ⟨χ, hχ, hyp⟩ := GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.GSep.TwistTranslate.exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.GSep.TwistTranslate.over_translate 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, huv⟩ := exists_frAt_ratio he₂.2.1 (htors (lab c + τ)).2.1
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hu1 : u ^ ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) = 1 := by
    obtain ⟨z⟩ : Nonempty (TFK (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J, hJ⟩ := exists_good' 𝔪.A.isLB z
    have q := GlobalTheory.Poinc.DivDeep.torsFrame_two_levels 𝔪.A (htors (lab c + τ)) he₂ hJ
    rw [div_self', one_pow] at q
    have q' := congrArg Units.val q
    have e : (val (fr (lab c + τ)) (𝟙 _) z J / val e₂ (𝟙 _) z J).val =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z u) := by
      rw [div_eq_mul_inv, Units.val_mul, huv z J hJ, Units.mul_inv_cancel_right]
    rw [Units.val_pow_eq_pow_val, e] at q'
    exact cstH_inj (R := V) z ((map_pow _ _ _).trans (q'.trans (map_one _).symm))
  obtain ⟨w₃, hw₃, hw₃v⟩ := exists_frm_scale w'' hw''g (inv_ne_zero hu)
  have hov' := over_scale 𝔪 hw''g hu huv hw₃v hov
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w₃ χ' =
      u⁻¹ * ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' =>
    GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (fun z J hJ => by rw [hw₃v z J hJ, hw''v, cst_eq]) s χ'
  haveI : IsIntegrallyClosed V := 𝔪.cn.2.1
  have hint : ∀ mu : X, ∃ a : V, algebraMap V (FractionRing V) a =
      u⁻¹ * ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) := fun mu => by
    refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.mul ?_ ?_)
    · refine IsIntegral.of_pow (n := (X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) (by positivity) ?_
      rw [inv_pow, hu1, inv_one]
      exact isIntegral_one
    · refine IsIntegral.of_pow hk ?_
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχ, MonoidHom.one_apply, Units.val_one]
      exact isIntegral_one
  choose a ha using hint
  refine ⟨fun mu _ => a mu * T mu c, x, fr, th, w₀, s, fun _ => _, fun _ => w₃, hx, hfr, hth, hw₀, hs,
    fun _ => ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₃, hov'⟩,
    fun mu _ => ?_⟩
  · obtain ⟨o, ho, ho'⟩ := (hc c).1
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
      ← ofMul_pow, hχ, ofMul_one, map_zero, add_zero]
  · rw [hco, map_mul, ha, ← hTc, _root_.mul_assoc]

end GlobalTheory.GSep.TermsExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsTorusTranslateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_exists_terms_torus_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : X → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  first | exact @GlobalTheory.GSep.TermsExt.exists_terms_translate | exact GlobalTheory.GSep.TermsExt.exists_terms_translate | (intros; apply GlobalTheory.GSep.TermsExt.exists_terms_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TransTerms

theorem sum_terms {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ)
    {C : Type} (lab : C → X₁.S.Gam) (T : X → C → V) (hT : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V) (fun mu : X => algebraMap V (FractionRing V) (T mu c) *
      𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem (lab c)⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hexp, hg', hTe⟩ := hT
  have hO := (hg' c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hg' c).2.1 th s _ hexp (hth (lab c))
  have := sumF_comp_equiv 𝔪.e₈.toEquiv hO
  convert this using 1
  funext mu
  exact hTe mu c

theorem twistSum_of_transExp {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (sg : ℤˣ)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ)
    (hW : ∀ (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), TorChar 𝔪 τ χ →
      ∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))
    {C : Type} (lab : C → X₁.S.Gam) (hlab : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁) (T : X → C → V)
    (hT : 𝔪.Terms x₀ lab T) (c : C) (τ : X₁.S.Gam) (hτ : τ ∈ X₁.S.TT X₁.M z₁) (e : ℕ)
    (hE : TransExp 𝔪 x₀ (lab c) τ e) : TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  obtain ⟨χ, hχ1, hχ2⟩ := GlobalTheory.T.exists_level_killed_char_of_torus_label I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨T', hT'⟩ := GlobalTheory.T.thetaMember_exists_terms_torus_translate I X₁ z₁ act x₀ hd V ev X t δ 𝔪 C lab hlab T hT c τ hτ
  have hprop := hE χ ⟨hχ1, hχ2⟩ C lab T hT c rfl Unit _ T' hT' () rfl
  have hsum := sumF_const_mul (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)))
    (sum_terms 𝔪 (fun _ : Unit => lab c + τ) T' hT' ())
  refine GlobalTheory.T.twistedAdicSum_terms_of_fractionField_sum I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hd) (GlobalTheory.GSep.TwistModel.exists_yy 𝔪) (hW τ χ ⟨hχ1, hχ2⟩) ?_
  convert hsum using 1
  funext mu
  rw [← _root_.mul_assoc, hprop mu, _root_.mul_assoc]

end GlobalTheory.GSep.TransTerms

namespace GlobalTheory.GSep
open GlobalTheory.GSep.TransTerms

theorem twistSum_exp_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro I X₁ z₁ act x₀ hd sg _ hW V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2
  classical
  have hA := GlobalTheory.T.thetaMember_torus_translation_exponent_affine I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 V2 ev2 Y2 t2 δ2 𝔪2
  choose! F1 F2 hF1 hF2 hAff using hA
  refine ⟨fun a τ => F1 τ a, fun a τ => F2 τ a, ?_, ?_, fun τ hτ => hAff τ hτ⟩
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪1 (fun τ χ hχ => hW V1 ev1 Y1 t1 δ1 𝔪1 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF1 τ hτ (lab c) (hlab c))
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪2 (fun τ χ hχ => hW V2 ev2 Y2 t2 δ2 𝔪2 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF2 τ hτ (lab c) (hlab c))

end GlobalTheory.GSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSum_exponents_differ_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.GSep.twistSum_exp_affine | exact GlobalTheory.GSep.twistSum_exp_affine | (intros; apply GlobalTheory.GSep.twistSum_exp_affine <;> assumption)
end
