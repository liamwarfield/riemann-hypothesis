module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymplecticBasesMatched
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryOfISupIntertwinerRange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulFunEqOneOfEqOneOnMaxCompact
namespace GlobalTheory.FrameEquiv

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem mulFun_eq_one_of_eq_one_on_maxCompact : ∀ (D : D7) (T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) → ∀ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') → (∀ k ∈ GinfC T, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) → χ k = 1) → ∀ u ∈ GinfC T, χ u = 1 :=
  fun D T θ hθ s hs χ hm hK =>
    GlobalTheory.UnitaryChar.char_eq_one D θ T hθ s hs χ hm fun k hk h => hK k hk fun τ => (h τ).symm

end GlobalTheory.FrameEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPointMovesAdelicThetaByDetCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPointMovesAdelicThetaByDetCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RealMove

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem root_eq {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D T} {x x' : (AE D)ˣ}
    (hx : IsDetRoot T g x) (hx' : IsDetRoot T g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D T).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem om_compact (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {s : Fam T} (hs : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {k : GA D T} (hk : k ∈ GinfC T)
    (hc : ∀ τ, s τ * compAt C.θ τ (Formalism.L2.Theta.mt T k) = compAt C.θ τ (Formalism.L2.Theta.mt T k) * s τ)
    {y : (AE D)ˣ} (hy : IsDetRoot T k y) {f : WO S T → ℂ} (hf : IsThetaFunO C.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO C.ψ S T) C.θ τ (cplxO 1 (s τ)) f) :
    om (1, k) f = (((χS y : Circle) : ℂ) * vacChar C.θ T s S.rank (fun _ => 0) k) • f := by
  have hdet : ∀ τ, (gramAt D T τ).det ≠ 0 := fun τ => by
    have := (hs τ).2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨y₀, hy₀, hv₀⟩ := GlobalTheory.OneMapRef.RealMove.exists_root C.inf T hdet k hk
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by
    have e : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [e]
    exact ⟨one_mul _, by simp, by rw [one_mul]; exact Matrix.PosDef.one⟩
  have h1 : IsDetRoot S 1 1 := by simp [IsDetRoot]
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D C.ψ hW.std S T C.θ C.inf χS χT om η hη hW (fun _ => 1) s hS hs 1 (one_mem _) k hk
    (fun τ => by rw [one_mul, mul_one]) hc 1 y₀ h1 hy₀ f hf hv, root_eq hW.resS C.even hy₀ hy]
  congr 1
  obtain ⟨m, hm⟩ := C.even
  have e1 := hv₀ (η * (η ^ (S.rank + 1))⁻¹) (fun _ => -(m : ℤ)) fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hη.2.2.2 τ) (hη.2.2.2 τ) (S.rank + 1)
    convert this using 1
    rw [hm]
    push_cast
    ring
  have e2 : ((χT * (η ^ T.rank)⁻¹) 1)⁻¹ * (χS * (η ^ S.rank)⁻¹) y₀ = χS y₀ * (η * (η ^ (S.rank + 1))⁻¹) y₀ := by
    simp only [map_one, inv_one, one_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_succ,
      mul_inv]
    rw [mul_left_comm (η y₀), mul_inv_cancel, mul_one]
  rw [e2, Circle.coe_mul, e1, mul_assoc, ← Finset.prod_mul_distrib, vacChar]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, -, hd⟩ := GlobalTheory.OneMapRef.RealMove.detPlus_one (n := S.rank) (s τ) (hs τ).1
  obtain ⟨d1, d2⟩ := hd (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)) (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (hc τ)
  have e3 : (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)).det = 1 := by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, inv_one]
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have e4 : (compAt C.θ τ (Formalism.L2.Theta.mt T k)).det ≠ 0 := by
    intro h0
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k)
    rw [det_mul, h0, mul_zero] at h2
    exact hdet τ h2.symm
  have hc' := hc τ
  rw [d1, e3]
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T k) = b at *
  have p1 : detPos (s τ) b = ((1 / 2 : ℂ) • (1 + s τ) * b + (1 / 2 : ℂ) • (1 - s τ)).det := by
    rw [detPos, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, hc', one_mul, mul_one]
  have p2 : detNeg (s τ) b = ((1 / 2 : ℂ) • (1 - s τ) * b + (1 / 2 : ℂ) • (1 + s τ)).det := by
    rw [detNeg, detPos, Matrix.mul_smul, Matrix.smul_mul, ← sub_eq_add_neg, sub_neg_eq_add, mul_sub, sub_mul, hc',
      one_mul, mul_one]
  rw [← p1, ← p2] at d2
  rw [← p1, d2]
  rw [d2] at e4
  have h0 := left_ne_zero_of_mul e4
  have e5 : S.rank / 2 = m := by omega
  rw [e5, zero_add, zero_sub, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, hm,
    one_pow, mul_one, mul_pow, pow_add, mul_inv]
  have := pow_ne_zero m h0
  field_simp

theorem th_ne_zero (C : GlobalTheory.Ker.Ctx S T) {x : Frame C.X.Ψ T.rank}
    (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem th_zero (C : GlobalTheory.Ker.Ctx S T) {x : Frame C.X.Ψ T.rank}
    (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem om_real (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {a : GA D T} (ha : a ∈ GinfC T) {y : (AE D)ˣ} (hy : IsDetRoot T a y) {B : C.Bas} (hB : C.IsB B)
    {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ) :
    om (1, a) (C.Th (C.xB B) φ) = ((χS y : Circle) : ℂ) • C.Th (C.xB (C.mvB a B)) φ := by
  obtain ⟨χ, -, χmul, hχ⟩ := GlobalTheory.FrameEquiv.exists_real_character D S T C om (GlobalTheory.Ker.isWeak_of_datum hW)
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  by_cases h0 : φ = 0
  · rw [hχ a ha B hB φ hφ, h0, th_zero C
      (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 a).1), smul_zero, smul_zero]
  obtain ⟨hex, -, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D T
  choose rt hrt using hex
  have hne : ∀ g, ((χS (rt g) : Circle) : ℂ) ≠ 0 := fun g => Circle.coe_ne_zero _
  have key := GlobalTheory.FrameEquiv.mulFun_eq_one_of_eq_one_on_maxCompact D T C.θ C.inf (C.sB B)
    (fun τ => ((hJ B hB).2.2.1 τ).1) (fun u => χ u / (χS (rt u) : Circle))
    (fun u hu u' hu' => by
      simp only [χmul u hu u' hu']
      rw [root_eq hW.resS C.even (hmul _ _ _ _ (hrt u) (hrt u')) (hrt (u * u')), map_mul, Circle.coe_mul,
        mul_div_mul_comm])
    (fun k hk hc => by
      have e1 := om_compact C hW hη (fun τ => ((hJ B hB).2.2.1 τ).1) hk (fun τ => (hc τ).symm) (hrt k)
        (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).1.1 ((GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ).1
      have e2 := hχ k hk B hB φ hφ
      have e3 := GlobalTheory.FrameEquiv.CompactMove.Th_mvB D S T C B hB k hk hc φ hφ
      rw [← smul_smul, ← e3, e2] at e1
      have e4 := smul_left_injective ℂ (th_ne_zero C
        (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 k).1) hφ h0) e1
      show χ k / (χS (rt k) : Circle) = 1
      rw [e4, div_self (hne k)]) a ha
  rw [hχ a ha B hB φ hφ, (div_eq_one_iff_eq (hne a)).1 key, root_eq hW.resS C.even hy (hrt a)]


set_option maxHeartbeats 1000000 in
theorem zak_om_real : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (_hS : IsSet ψ θ S T hr X eT bas), ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ a ∈ GinfC T, ∀ y : (AE D)ˣ, IsDetRoot T a y → ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ a Z)) (((χS y : Circle) : ℂ) • φ) (om (1, a) f) := by
  intro D S T r g hr ψ θ X eT bas idx hS χS χT om hW ⟨η, hη⟩ Z hZ a ha y hy φ hφ f hf
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, -, H⟩ := GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T r g hr ψ θ X eT bas idx hS (r - X.p0)
    (Nat.add_sub_cancel' X.p0_le)
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  have hB := (H Z).1.1 hZ
  have em : (fun ρ => (mvZ θ a Z ρ).submatrix id π) = C.mvB a fun ρ => (Z ρ).submatrix id π := by
    funext ρ
    ext i j
    rfl
  have hB' := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 _ hB).2.2.2.2.2 a).1
  have hZ' : IsONeg T X.p0 (mvZ θ a Z) := (H _).1.2 (em ▸ hB')
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  have hd' := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB'
  have e1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).2 f ((((H Z).2 hZ).2.1 φ f).2 hf)
  refine (((H _).2 hZ').2.1 _ _).1 ?_
  have hφ' : GlobalTheory.SW.IsSB (((χS y : Circle) : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 _
  rw [em, e1, om_real C hW hη ha hy hB hφ, ← (GlobalTheory.Ker.Ctx.th_laws D S T C _ hd' φ hφ).2.1]
  exact (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd' _ hφ').1

end GlobalTheory.OneMapRef.RealMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPointMovesAdelicThetaByDetCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_point_moves_adelic_theta_by_det_character : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ a ∈ GinfC T, ∀ y : (AE D)ˣ, IsDetRoot T a y → ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ a Z)) (((χS y : Circle) : ℂ) • φ) (om (1, a) f) := by
  first | exact @GlobalTheory.OneMapRef.RealMove.zak_om_real | exact GlobalTheory.OneMapRef.RealMove.zak_om_real | (intros; apply GlobalTheory.OneMapRef.RealMove.zak_om_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSqGaussProd
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VacUnit

section Mean
open MeasureTheory Measure
open scoped ENNReal Pointwise

theorem lintegral_sub {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] {μ : Measure V}
    [μ.IsAddLeftInvariant] {Γ B : AddSubgroup V} [Countable B] (h : Γ ≤ B) {Fd F : Set V}
    (hFd : IsAddFundamentalDomain Γ Fd μ) (hF : IsAddFundamentalDomain B F μ) (Φ : V → ℝ≥0∞)
    (hΦ : ∀ b ∈ B, ∀ v, Φ (b + v) = Φ v) :
    ∫⁻ v in Fd, Φ v ∂μ = ∑' _ : B ⧸ Γ.addSubgroupOf B, ∫⁻ v in F, Φ v ∂μ := by
  have : Countable Γ := (AddSubgroup.inclusion_injective h).countable
  have hb : Function.Bijective fun p : (B ⧸ Γ.addSubgroupOf B) × Γ => p.1.out + AddSubgroup.inclusion h p.2 := by
    have hm : ∀ (b : B) (γ : Γ), ((b + AddSubgroup.inclusion h γ : B) : B ⧸ Γ.addSubgroupOf B) = b := fun b γ =>
      QuotientAddGroup.mk_add_of_mem b γ.2
    constructor
    · rintro ⟨q, γ⟩ ⟨q', γ'⟩ e
      have e' := congrArg (fun b : B => (b : B ⧸ Γ.addSubgroupOf B)) e
      simp only [hm, QuotientAddGroup.out_eq'] at e'
      subst e'
      exact Prod.ext rfl (AddSubgroup.inclusion_injective h (add_left_cancel e))
    · intro b
      obtain ⟨γ, hγ⟩ := QuotientAddGroup.mk_out_eq_add (Γ.addSubgroupOf B) b
      refine ⟨(b, -⟨γ.1, γ.2⟩), ?_⟩
      simp only [hγ, map_neg]
      exact add_neg_cancel_right _ _
  rw [hF.setLIntegral_eq_tsum, ← (Equiv.ofBijective _ hb).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  rw [hF.setLIntegral_eq (hF.vadd_of_comm q.out) Φ (fun b v => hΦ b b.2 v), hFd.setLIntegral_eq_tsum']
  refine tsum_congr fun γ => ?_
  have e : (γ +ᵥ (q.out +ᵥ F)) = (q.out + AddSubgroup.inclusion h γ) +ᵥ F := by
    rw [add_comm, add_vadd]; rfl
  rw [Set.inter_comm, e]
  exact lintegral_congr fun v => (hΦ _ (h (-γ).2) v).symm

theorem isFD_pi {Y : Type} [AddCommGroup Y] [MeasureSpace Y] [SigmaFinite (volume : Measure Y)] {A : AddSubgroup Y}
    {F : Set Y} (hF : IsAddFundamentalDomain A F volume) (n : ℕ) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : Fin n => A) (Set.univ.pi fun _ : Fin n => F) volume := by
  have hq (i : Fin n) := quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure Y)) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (volume : Measure (Fin n → Y)))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

theorem integral_prod_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {g n : ℕ}
    (e : V ≃L[ℝ] (Fin n → Fin g → ℂ)) {A : AddSubgroup (Fin g → ℂ)} [Countable A] {F : Set (Fin g → ℂ)}
    (hF : IsAddFundamentalDomain A F volume) {φ : (Fin g → ℂ) → ℝ} (hc : Continuous φ) (h0 : ∀ z, 0 ≤ φ z)
    (hp : ∀ a ∈ A, ∀ z, φ (a + z) = φ z) (hm : (∫ z in F, φ z) / (volume F).toReal = 1)
    {Γ : AddSubgroup V} (hΓ : ∀ v ∈ Γ, ∀ b, e v b ∈ A) {Fd : Set V} (hFd : IsAddFundamentalDomain Γ Fd μ) :
    ∫ v in Fd, ∏ b, φ (e v b) ∂μ = (μ Fd).toReal := by
  have hV : (volume F).toReal ≠ 0 := fun h => by simp [h] at hm
  rw [div_eq_one_iff_eq hV] at hm
  have hi : Integrable φ (volume.restrict F) := Integrable.of_integral_ne_zero (hm ▸ hV)
  set P : Set (Fin n → Fin g → ℂ) := Set.univ.pi fun _ : Fin n => F with hP
  let Φ : (Fin n → Fin g → ℂ) → ℝ := fun z => ∏ b, φ (z b)
  have hΦc : Continuous Φ := by fun_prop
  have hΦ0 : ∀ z, 0 ≤ Φ z := fun z => Finset.prod_nonneg fun b _ => h0 _
  have h1 : ∫⁻ z in P, ENNReal.ofReal (Φ z) = volume P := by
    have e1 : volume.restrict P = Measure.pi fun _ : Fin n => volume.restrict F := restrict_pi_pi _ _
    have e2 : volume P = volume F ^ n := by
      rw [hP, volume_pi_pi]; simp
    rw [← ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall hΦ0), e1, e2]
    · rw [integral_fintype_prod_eq_pow, hm, Fintype.card_fin, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal]
      exact ENNReal.pow_ne_top fun h => hV (by simp [h])
    · rw [e1]; exact Integrable.fintype_prod fun _ => hi
  have hH := e.isAddHaarMeasure_map μ
  have : (volume : Measure (Fin g → ℂ)).IsAddHaarMeasure := pi.isAddHaarMeasure _
  have : (volume : Measure (Fin n → Fin g → ℂ)).IsAddHaarMeasure := pi.isAddHaarMeasure _
  obtain ⟨c, hc'⟩ : ∃ c : NNReal, μ.map e = c • volume := ⟨_, isAddLeftInvariant_eq_smul _ _⟩
  have hme := e.toHomeomorph.measurableEmbedding
  have hq : QuasiMeasurePreserving e μ volume := ⟨e.continuous.measurable.aemeasurable, by
    rw [hc']; exact smul_absolutelyContinuous⟩
  let Bn := AddSubgroup.pi Set.univ fun _ : Fin n => A
  let B : AddSubgroup V := Bn.comap e.toLinearEquiv.toAddEquiv.toAddMonoidHom
  let k : B ≃ Bn := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  have : Countable Bn := Function.Injective.countable (f := fun (a : Bn) (i : Fin n) => (⟨a.1 i, a.2 i trivial⟩ : A))
    fun a b h => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  have : Countable B := k.injective.countable
  have hB : IsAddFundamentalDomain B (e ⁻¹' P) μ :=
    (isFD_pi hF n).preimage_of_equiv hq k.symm.bijective fun a v => by
      change e (e.symm a + v) = a + e v
      simp
  have hle : Γ ≤ B := fun v hv i _ => hΓ v hv i
  have h2 := lintegral_sub hle hFd hB (fun v => ENNReal.ofReal (Φ (e v))) fun b hb v => by
    simp only [Φ, map_add (f := _), Pi.add_apply]
    exact congrArg _ (Finset.prod_congr rfl fun i _ => hp _ (hb i trivial) _)
  have h3 := lintegral_sub hle hFd hB (fun _ => 1) fun _ _ _ => rfl
  have h4 : ∀ Ψ : (Fin n → Fin g → ℂ) → ℝ≥0∞, ∫⁻ v in e ⁻¹' P, Ψ (e v) ∂μ = c * ∫⁻ z in P, Ψ z := fun Ψ => by
    have := hme.lintegral_map (μ := μ.restrict (e ⁻¹' P)) Ψ
    have e3 := hme.restrict_map μ P
    simp only [ContinuousLinearEquiv.coe_toHomeomorph] at this e3
    rw [← this, ← e3, hc', restrict_smul, lintegral_smul_measure]
    rfl
  rw [h4 fun z => ENNReal.ofReal (Φ z), h1] at h2
  rw [h4 fun _ => 1, setLIntegral_one, setLIntegral_one, ← h2] at h3
  rw [h3]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun v => hΦ0 _)
    (hΦc.comp e.continuous).aestronglyMeasurable

end Mean

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r}

theorem norm_periodic (hs : IsSympl X bas) (hx' : x ∈ X.dom) {w : E} {L : Lt E r} {th : (Fin g → ℂ) → ℂ}
    (h : IsTheta1 X bas idx w x L th) {u : Fin r → E} (hu : u ∈ L) (z : Fin g → ℂ) :
    ‖th (pv X idx x u + z)‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x (pv X idx x u + z) (pv X idx x u + z)).re) =
      ‖th z‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x z z).re) := by
  have hc := (hx_laws E r X g bas idx 0 hs Even.zero x hx').1
  have hp : _ = th z := congrFun (h.2 u hu) z
  have hε : ‖eps1 X w u‖ = 1 := by
    rw [eps1, Complex.norm_exp]
    simp
  generalize pv X idx x u = p at hp
  simp only [Pi.smul_apply, smul_eq_mul, fock] at hp
  rw [← hp, add_comm p z, norm_mul, norm_mul, hε, _root_.one_mul, mul_pow, Complex.norm_exp,
    ← Real.exp_nat_mul, mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
  congr 2
  have e1 : (hx X bas idx x (z + p) (z + p)).re =
      (hx X bas idx x z z).re + 2 * (hx X bas idx x z p).re + (hx X bas idx x p p).re := by
    have := congrArg Complex.re (hc z p)
    rw [Complex.conj_re] at this
    simp only [hx, mulVec_add, star_add, add_dotProduct, dotProduct_add, Complex.add_re] at this ⊢
    linarith
  have e2 : hx X bas idx x (z + (1 / 2 : ℂ) • p) p = hx X bas idx x z p + (1 / 2 : ℝ) * hx X bas idx x p p := by
    simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
    push_cast; ring
  rw [e1, e2]
  simp only [Nat.cast_one, _root_.one_mul, Complex.neg_re, Complex.re_ofReal_mul, Complex.add_re]
  push_cast; ring

theorem norm_sq_gauss_prod (th : (Fin g → ℂ) → ℂ) (z : Fin n → Fin g → ℂ) :
    ‖Ker.gaussR X bas idx x z * ∏ b, th (z b)‖ ^ 2 =
      ∏ b, ‖th (z b)‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x (z b) (z b)).re) := by
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, norm_mul, mul_pow, norm_prod, Finset.prod_pow, mul_comm, Ker.gaussR,
    Complex.norm_exp, ← Real.exp_nat_mul, ← Finset.mul_sum]
  congr 2
  have : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.neg_re, Complex.re_ofReal_mul, Complex.re_sum]
  push_cast; ring

theorem exists_nsmul_mem {Λ L : Lt E r} (hΛ : Λ.FG) (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ Λ, N • v ∈ L := by
  obtain ⟨s, rfl⟩ := hΛ
  choose k hk hk' using GlobalTheory.LatFin.exists_int_smul_mem L hL
  refine ⟨(∏ v ∈ s, k v).natAbs, Int.natAbs_pos.2 (Finset.prod_ne_zero_iff.2 fun v _ => hk v), fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨c, hc⟩ := Int.dvd_natAbs.2 (Finset.dvd_prod_of_mem k hv)
    rw [← natCast_zsmul, hc, mul_comm, mul_smul]
    exact zsmul_mem (hk' v) c
  | zero => simp
  | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
  | smul a u _ hu => rw [smul_comm]; exact L.smul_mem a hu

end Classical

theorem frOf_mem_dom {D : D7} {T : HSp D} {X : Data D.host.E T.rank} {eT : D.what₂.Tau ≃ X.Ψ} (hm : ModelW T rfl X)
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) : frOf rfl eT Z ∈ X.dom := by
  refine Ker.ONBasis.mem_dom X fun σ => ?_
  obtain ⟨ρ, rfl⟩ := eT.surjective σ
  ext a b
  have h := congrFun (congrFun (hZ ρ) b) a
  have hs : sgnM X a b = -negM T X.p0 b a := by
    simp only [sgnM, negM, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  rw [hs, ← h]
  simp only [FD.gram, Matrix.of_apply, hermC, FD.col, FD.mat, frOf, Equiv.symm_apply_apply, he, hm.1,
    Matrix.mul_apply, Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, Fin.cast_eq_self, finCongr_refl,
    Matrix.reindex_refl_refl, Matrix.neg_apply, map_neg, ← Finset.sum_neg_distrib,
    Matrix.transpose_apply, Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

def conjPt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X X' : Data E r} (e : X.Ψ ≃ X'.Ψ) (n : ℕ) :
    Ker.WR X' n ≃ₗ[ℝ] Ker.WR X n where
  toFun v τ k a := conj (v (e τ) k a)
  invFun v σ k a := conj (v (e.symm σ) k a)
  map_add' _ _ := by funext τ k a; simp
  map_smul' _ _ := by funext τ k a; simp
  left_inv _ := by funext τ k a; simp
  right_inv _ := by funext τ k a; simp

theorem vac_eq_unit_mul : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → GlobalTheory.Ker.IdemTwo w → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ (LT : Lt D.host.E T.rank) (L : Lt D.host.E r), SelfD X L → GlobalTheory.Ker.IsAA (latW hr L) LT → ∀ f, IsVacO ψ θ S T (fun _ => 1) (cartZ T X.p0 Z) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) f → ∀ th : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w (frOf hr eT Z) L th → MeanOne X bas idx (frOf hr eT Z) L th → ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ p : WO S T, GlobalTheory.Ker.IsRealPt p → f p = a * (GlobalTheory.Ker.gaussR X bas idx (frOf hr eT Z) (GlobalTheory.Ker.zR X idx (frOf hr eT Z) (rePt θ hr eT p)) * ∏ b, th (GlobalTheory.Ker.zR X idx (frOf hr eT Z) (rePt θ hr eT p) b)) := by
  intro D S T r g hr ψ θ X eT bas idx hS w hw hw' hw2 Z hZ LT L hL hA f hf th hth hmean
  subst hr
  obtain ⟨X', m, hq', bas', idx', hs, π, hΛ, hEF, hhe, H⟩ :=
    GlobalTheory.OneMapRef.Flip.exists_flip_model D S T _ g rfl ψ θ X eT bas idx hS (T.rank - X.p0) (Nat.add_sub_cancel' X.p0_le)
  obtain ⟨hB, H⟩ := H Z
  obtain ⟨hsB, hZak, -⟩ := H hZ
  replace hB := hB.1 hZ
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  set B : C.Bas := fun ρ => (Z ρ).submatrix id π with hBd
  have hsym := hS.2.2.2.2.2.2.2
  have hev := hS.2.2.2.1
  replace hEF : ∀ u v, EF X' u v = EF X u v := hEF
  replace hΛ : X'.Λ = X.Λ := hΛ.trans (Submodule.comap_id _)
  replace hA : Ker.IsAA L LT := hA
  replace hhe : ∀ y φ, heisG X' bas' y φ = heisG X bas y φ := hhe
  have hL' : SelfD X' L := ⟨hL.1, by simpa only [hEF] using hL.2⟩
  have hx' := frOf_mem_dom hS.2.2.2.2.1 hS.2.2.2.2.2.2.1 hZ
  set x := frOf rfl eT Z with hxd
  obtain ⟨-, hv⟩ := hf
  have hstar : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := by
    have : ∀ v : Fin S.rank → D.host.E, v ∈ stdL D.host.E S.rank → star v ∈ stdL D.host.E S.rank := fun v hv =>
      (SW.Base.mem_stdL _).2 fun a => SW.Base.isIntegral_cc ((SW.Base.mem_stdL _).1 hv a)
    exact fun v => ⟨this v, fun h => by simpa using this _ h⟩
  have hV := SW.Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  obtain ⟨v, hvac⟩ := (TensVac.vacua _ _ X g bas idx S.rank hsym hev w hw hw' L hL 1 _ hV).1
  have hvac' : IsVac X' bas' w (tens (stdL D.host.E S.rank) L) v :=
    ⟨hvac.1, hvac.2.1, fun y hy => by simpa only [SW.epsW, hEF, hhe] using hvac.2.2 y hy⟩
  obtain ⟨t, ht⟩ := (Ker.latVac_th_line D S T C w hw hw' hw2 1 _ hV L hL').2 B hB v hvac' f hv.theta
    (fun τ => by rw [hsB]; exact hv.fock τ) (by rw [← Ker.LatTens.latO_eq_hatA D S T C _ _ LT _ hstar hA]; exact hv.lat)
  have hz := ((hZak v _).1 (Ker.ZakEx.isZak_Th D S T C _ (Ker.ONBasis.mem_dom _ (Ker.ONBasis.isONFr_xB C hB)) v
    hvac.1).1).2
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA _ _ X g bas idx S.rank hsym hev w hw hw' L hL v hvac x hx' th hth
  obtain ⟨A, F, hAm, hF, hm⟩ := hmean
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ : ∃ z, th z ≠ 0 := by
      by_contra! h0
      simp [h0] at hm
    exact Finset.prod_ne_zero_iff.2 (fun _ _ => hz) ((hκ fun _ => z).trans (zero_mul _))
  have hfp : ∀ p : WO S T, Ker.IsRealPt p → f p = t / κ * (Ker.gaussR X bas idx x (Ker.zR X idx x (rePt θ rfl eT p)) *
      ∏ b, th (Ker.zR X idx x (rePt θ rfl eT p) b)) := fun p hp => by
    rw [ht, Pi.smul_apply, hz p hp, hκ, Ker.thR, smul_eq_mul]
    field_simp
  refine ⟨t / κ, ?_, hfp⟩
  generalize t / κ = a at hfp
  obtain ⟨⟨⟨μ, 𝓕⟩, hμ⟩, hn⟩ := hv.norm
  have h1 : nrm2 μ 𝓕 f = 1 := hn _ hμ
  obtain ⟨N₀, hN₀, hN⟩ := Ker.TorusMean.ipO_eq_mean D S T C μ 𝓕 hμ f f hv.theta hv.theta
  obtain ⟨N₁, hN₁, hN'⟩ := exists_nsmul_mem X.Λ_fg (TensLat.span_of_selfD X hL)
  obtain ⟨⟨Fd, hFd⟩, hN⟩ := hN (N₀ * N₁) (Nat.mul_pos hN₀ hN₁) (Dvd.intro _ rfl)
  obtain ⟨⟨e₀, he₀⟩, -⟩ := Ker.zR_laws _ _ X g _ (Nat.add_sub_cancel' X.p0_le) bas idx S.rank hsym hev x hx'
  let J := conjPt (eT.symm.trans m.e) S.rank
  let e := J.toContinuousLinearEquiv.trans e₀
  have hJ : ∀ p : WO S T, e (C.realPt p) = Ker.zR X idx x (rePt θ rfl eT p) := fun p => by
    rw [← he₀]
    refine congrArg e₀ ?_
    funext τ k a
    change conj (conj (compAt θ (m.e.symm (m.e (eT.symm τ))) p a k)) = _
    rw [Complex.conj_conj, Equiv.symm_apply_apply]
    rfl
  have hJ' : ∀ y, e (Ker.embR X' y) = Ker.zR X idx x (Ker.embR X y) := fun y => by
    rw [← he₀]
    refine congrArg e₀ ?_
    funext τ k a
    obtain ⟨ρ, rfl⟩ := eT.surjective τ
    change conj ((m.e (eT.symm (eT ρ))).1 (y k a)) = (eT ρ).1 (y k a)
    rw [Equiv.symm_apply_apply, m.e_emb, hS.2.2.2.2.2.2.1, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  let φ : (Fin g → ℂ) → ℝ := fun z => ‖th z‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x z z).re)
  have hφ : Continuous φ := by
    have := hth.1.continuous
    simp only [φ, hx]
    fun_prop
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable A := by
    have : (A : Set (Fin g → ℂ)) ⊆ Set.range (pv X idx x) := fun z hz => by
      obtain ⟨u, -, rfl⟩ := (hAm z).1 hz
      exact ⟨u, rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : (volume : Measure (Fin T.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin S.rank → Fin T.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Ker.WR X' S.rank)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h2 := integral_prod_eq (volume : Measure (Ker.WR X' S.rank)) e hF hφ (fun z => by positivity)
    (fun p hp z => by
      obtain ⟨u, hu, rfl⟩ := (hAm p).1 hp
      exact norm_periodic hsym hx' hth hu z) hm (Γ := Ker.latR X' S.rank (N₀ * N₁)) (fun u hu => by
      induction hu using AddSubgroup.closure_induction with
      | mem u hu =>
        obtain ⟨y, hy, rfl⟩ := hu
        intro b
        have e1 : (N₀ * N₁) • Ker.embR X' y = Ker.embR X' ((N₀ * N₁) • y) := by
          funext τ k a
          simp [Ker.embR]
        rw [e1, hJ', hAm]
        refine ⟨(N₀ * N₁) • y b, ?_, rfl⟩
        rw [mul_smul]
        exact nsmul_mem (hN' _ (hΛ ▸ hy b)) _
      | zero => simp
      | add u u' _ _ hu hu' => exact fun b => by simpa only [map_add, Pi.add_apply] using add_mem (hu b) (hu' b)
      | neg u _ hu => exact fun b => by rw [map_neg]; exact neg_mem (hu b)) hFd
  have h3 := hN Fd hFd (fun u => ((‖a‖ ^ 2 * ∏ b, φ (e u b) : ℝ) : ℂ)) fun p hp => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hfp p hp, norm_mul, mul_pow, norm_sq_gauss_prod, hJ]
  have h4 : Ker.ipO μ 𝓕 f f = 1 := by
    simp only [Ker.ipO, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal]
    exact_mod_cast h1
  rw [h4, integral_complex_ofReal, integral_const_mul] at h3
  erw [h2] at h3
  have h5 : (1 : ℝ) = (volume Fd).toReal⁻¹ * (‖a‖ ^ 2 * (volume Fd).toReal) := by exact_mod_cast h3
  have h6 : (volume Fd).toReal ≠ 0 := fun h => by simp [h] at h5
  rw [mul_comm, _root_.mul_assoc, mul_inv_cancel₀ h6, _root_.mul_one] at h5
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 h5.symm

end GlobalTheory.OneMapRef.VacUnit

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FrameConst

variable {D : D7} {S T : HSp D} {r : ℕ}

theorem le_of_isAA {k : ℕ} {Λ L L' : Lt D.host.E k} (h : GlobalTheory.Ker.IsAA Λ L) (h' : GlobalTheory.Ker.IsAA Λ L') : L ≤ L' := by
  intro u hu
  have hA := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have key : ∀ b ∈ D.host.AA⁻¹, ∀ x ∈ Λ, b • x ∈ L' := by
    intro b hb x hx
    have hx' := (h' x).1 hx
    clear hx
    induction hx' using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hv
      have : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
        rw [← inv_mul_cancel₀ hA]; exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 this
      rw [smul_smul, ← hz, algebraMap_smul]
      exact L'.smul_mem z hw
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | neg v _ hv => rw [smul_neg]; exact neg_mem hv
  have h1 : (1 : D.host.E) ∈ D.host.AA⁻¹ * D.host.AA := by
    rw [inv_mul_cancel₀ hA]; exact FractionalIdeal.one_mem_one _
  have : ∀ c ∈ D.host.AA⁻¹ * D.host.AA, c • u ∈ L' := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc (C := fun c => c • u ∈ L') ?_ ?_
    · intro b hb a ha
      rw [mul_smul]
      exact key b hb _ ((h _).2 (AddSubgroup.subset_closure ⟨a, ha, u, hu, rfl⟩))
    · intro x y hx hy
      rw [add_smul]; exact add_mem hx hy
  simpa using this 1 h1

theorem fmt_mul (g h : GA D T) : GlobalTheory.Ker.fmt T (g * h) = GlobalTheory.Ker.fmt T g * GlobalTheory.Ker.fmt T h := by
  change (finHom T (g * h)).1 = (finHom T g).1 * (finHom T h).1
  rw [map_mul, Units.val_mul]

theorem fmt_real {a : GA D T} (ha : a ∈ GinfC T) : GlobalTheory.Ker.fmt T a = 1 :=
  congrArg Units.val (show finHom T a = 1 from ha)

theorem isMov_one (L : Lt D.host.E T.rank) : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T 1) L L := by
  intro u
  rw [fmt_real (one_mem _)]
  simp only [Matrix.one_mulVec, exists_eq_right']

theorem isMov_quot {g g' a : GA D T} (ha : a ∈ GinfC T) {L L' : Lt D.host.E T.rank}
    (h : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g) L L') (h' : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g') L L') :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T ((a * g)⁻¹ * g')) L L := by
  have e1 : GlobalTheory.Ker.fmt T g⁻¹ * GlobalTheory.Ker.fmt T g = 1 := by rw [← fmt_mul, inv_mul_cancel, fmt_real (one_mem _)]
  intro u
  rw [_root_.mul_inv_rev, fmt_mul, fmt_mul, fmt_real (inv_mem ha), mul_one]
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h' _).1 ((h _).2 ⟨u, hu, rfl⟩)
    refine ⟨u₀, h0, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← e, Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · rintro ⟨u₀, h0, rfl⟩
    obtain ⟨u₁, h1, e⟩ := (h _).1 ((h' _).2 ⟨u₀, h0, rfl⟩)
    rw [← Matrix.mulVec_mulVec, e, Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
    exact h1

theorem eq_one_of_rat {θ : InfFam D} (hθ : IsInfFam θ) {δ : GA D T} (h1 : δ ∈ GQ T) (h2 : δ ∈ GfC T) : δ = 1 := by
  obtain ⟨ga, hga, hδ'⟩ := id h1
  have hm : Formalism.L2.Theta.mt T δ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) :=
    (congrArg Units.val hδ').symm
  have h3 : (Formalism.L2.Theta.mt T δ).map (infPart D) = 1 := congrArg Units.val (show infHom T δ = 1 from h2)
  have ρ : D.what₂.Tau := D.eTau.symm 1
  have h4 : (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E) = 1 := by
    refine Matrix.ext fun i j => (tauE D ρ).injective ?_
    have h5 := congrArg (θ ρ) (congrFun (congrFun h3 i) j)
    rw [hm] at h5
    refine ((hθ ρ).1 _).symm.trans (h5.trans ?_)
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine Subtype.ext (Units.ext ?_)
  change Formalism.L2.Theta.mt T δ = 1
  rw [hm, h4, Matrix.map_one _ (map_zero _) (map_one _)]

theorem frOf_injective (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) {Z Z' : Fam T}
    (h : frOf hr eT Z = frOf hr eT Z') : Z = Z' := by
  subst hr
  funext ρ
  have := congrFun h (eT ρ)
  unfold frOf at this
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem thR_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g) (x : Frame X.Ψ r)
    (p : GlobalTheory.Ker.WR X n) : GlobalTheory.Ker.thR X bas idx (a • φ) x p = a * GlobalTheory.Ker.thR X bas idx φ x p := by
  simp only [GlobalTheory.Ker.thR, thA, SW.thS, show ∀ y, (a • φ) y = a * φ y from fun _ => rfl, _root_.mul_assoc, tsum_mul_left]
  ring

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  rw [map_add (f := _), map_one] at this
  exact (congrArg _ (H.bar_eq _).symm).trans this

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    GlobalTheory.Ker.IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := hostHalfRoot_add_conj_eq_one H
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

theorem finUnit_one : FinUnit (1 : (AE D)ˣ) := by
  have : finPart D (1 : AE D) ∈ intAE D := by
    rw [map_one]
    exact AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩
  exact ⟨map_one _, this, this⟩

theorem isDetRoot_one : IsDetRoot S 1 1 := by
  unfold IsDetRoot
  simp

open scoped ComplexOrder in
theorem isCartanInv_one (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩

theorem om_vac_move {g : ℕ} {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hS : IsSet ψ θ S T hr X eT bas) (sS : S.SigOK) (sT : T.SigOK) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hη : ∃ η, IsEtaTilde D η)
    (hun : ∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) {Z₀ : Fam T} (hZ : IsONeg T X.p0 Z₀)
    {ΛS : Lt D.host.E S.rank} {ΛT : Lt D.host.E T.rank} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    {f₀ : WO S T → ℂ} (hf : IsVacO ψ θ S T (fun _ => 1) (cartZ T X.p0 Z₀) (ΛS : Set _) (ΛT : Set _) f₀)
    {mu : GA D T → ℂ} (hmu : MuVal T χS mu) {g₀ g₁ : GA D T} {L : Lt D.host.E T.rank}
    (m₀ : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g₀) ΛT L) (m₁ : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g₁) ΛT L)
    {φ : TF S.rank g} (hφ : GlobalTheory.SW.IsSB φ) (hz : Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ g₀ Z₀)) φ (om (1, g₀) f₀))
    (w : WO S T) (hw : GlobalTheory.Ker.IsRealPt w) :
    om (1, g₁) f₀ w = mu g₁ / mu g₀ * GlobalTheory.Ker.thR X bas idx φ (frOf hr eT (mvZ θ g₁ Z₀)) (rePt θ hr eT w) := by
  obtain ⟨-, -, -, hc, hF⟩ := oneg_frames D S T r g hr ψ θ X eT bas idx hS Z₀ hZ
  have h0 := (hF g₀).1
  obtain ⟨a, ha, hae⟩ := ((oneg_frames D S T r g hr ψ θ X eT bas idx hS _ h0).2.2.2.2 1).2.2.2.2.2 _ (hF g₁).1
  have hk : (a * g₀)⁻¹ * g₁ ∈ GfC T := by
    apply (hF _).2.2.2.2.1
    rw [(hF g₁).2.2.1, hae, ← (hF g₀).2.2.1, ← (hF _).2.2.1, inv_mul_cancel]
    exact (hF 1).2.2.2.1 (one_mem _)
  have hmov := isMov_quot ha m₀ m₁
  obtain ⟨k, hke⟩ : ∃ k, k = (a * g₀)⁻¹ * g₁ := ⟨_, rfl⟩
  rw [← hke] at hk hmov
  have e1 : g₁ = a * g₀ * k := by rw [hke, mul_inv_cancel_left]
  obtain ⟨y, hy, hyk⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D T ΛT dT k hk hmov
  have h1 := GlobalTheory.T.weil_vacuum_finite_selfDualLattice_splitting D S T ψ θ hS.2.1 sS sT χS χT om hW hη hun (fun _ => 1) _ (isCartanInv_one hS.2.2.1) hc
    ΛS ΛT dS dT f₀ hf 1 (one_mem _) k hk (isMov_one _) hmov 1 y finUnit_one hy isDetRoot_one hyk
  obtain ⟨ya, hya⟩ := hmu.1 a
  obtain ⟨y₀, hy₀⟩ := hmu.1 g₀
  have h2 := (GlobalTheory.T.real_point_moves_adelic_theta_by_det_character D S T r g hr ψ θ X eT bas idx hS χS χT om hW hη _ h0 a ha ya hya φ hφ _ hz).2 w hw
  have h3 : om (1, g₁) f₀ = om (1, a) (om (1, g₀) (om (1, k) f₀)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, e1]
    simp
  have h4 : mu g₁ = (χS ya : ℂ) * mu g₀ * χS y := by
    rw [hmu.2 g₀ y₀ hy₀, hmu.2 g₁ (ya * y₀ * y)
      (e1 ▸ detRootMul_holds T _ _ _ _ (detRootMul_holds T _ _ _ _ hya hy₀) hyk)]
    simp
  have h5 : mu g₀ ≠ 0 := norm_ne_zero_iff.1 (by rw [hmu.norm]; exact one_ne_zero)
  rw [h3, h1, map_smul, map_smul, Pi.smul_apply, h2, thR_smul, ← hae, h4, map_one, inv_one, one_mul, smul_eq_mul]
  field_simp

section Geo

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

theorem exists_const (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) (k : U.Comp)
    {t : ℝ} (ht : ∀ τ, (U.X k).c τ = t) (hsd : SelfD (U.X k) (U.X k).Λ) {n : ℕ} (hn : Even n) {g : ℕ}
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas) (hm : Matched c σ (U.X k) idx e) :
    ∃ φ : TF n g, GlobalTheory.SW.IsSB φ ∧ ∀ (x : Frame (U.X k).Ψ r) (hx : x ∈ (U.X k).dom), (U.X k).IsOrtho x →
      ∀ (g' : ℕ) (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx' : Fin g' ≃ (U.X k).Ψ × Fin r)
        (e' : Fin g' ≃ Lt1 Dw), IsSympl (U.X k) bas' → Matched c σ (U.X k) idx' e' →
      letI : Algebra c.F ℂ := σ.toAlgebra
      ∀ (A : AnFib (U.X k) bas' idx' e' x (U.X k).Λ (ptC U k ⟨x, hx⟩)) (th : (Fin g' → ℂ) → ℂ),
        A.Reads 1 (ptC U k ⟨x, hx⟩).s th → ∀ p : GlobalTheory.Ker.WR (U.X k) n,
          GlobalTheory.Ker.gaussR (U.X k) bas' idx' x (GlobalTheory.Ker.zR (U.X k) idx' x p) * ∏ b, th (GlobalTheory.Ker.zR (U.X k) idx' x p b) =
            GlobalTheory.Ker.thR (U.X k) bas idx φ x p := by
  obtain ⟨v, hv⟩ := (TensVac.vacua _ _ _ _ bas idx n hs hn _ H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H) _ hsd 1 _
    (Base.stdL_mem_Vset n 1)).1
  obtain ⟨C, hC⟩ := exists_const_ortho D H Dw l Xo c σ r U hσ hU hr1 hA k t ht n hn g bas idx e hs hm v hv
  refine ⟨C • v, TensVac.sb_smul _ hv.1, fun x hx ho g' bas' idx' e' hs' hm' A th hth p => ?_⟩
  have key := anFib_move_renum D H Dw l Xo c σ r g g' (U.X k) (U.X k) ⟨rfl, rfl, rfl, rfl, rfl⟩ bas' idx' e' bas idx e
    hs' hs hm' hm x hx _ hsd 1 (fun a b => by simp) _ A th hth
  have e1 : lact (1 : GL (Fin r) D.host.E) (castFr (rfl : (U.X k).Ψ = (U.X k).Ψ) x) = x := by
    funext τ
    simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    rfl
  have e2 : mapL (1 : GL (Fin r) D.host.E) (U.X k).Λ = (U.X k).Λ := by
    simp [mapL]
  rw [e1, e2] at key
  obtain ⟨A₁, th₁, h1, -, h2⟩ := key
  rw [← h2 n p p fun τ j => by simp, hC ⟨x, hx⟩ ho A₁ th₁ h1, thR_smul, GlobalTheory.Ker.thR]
  ring

def IsPt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S : HSp D) (hr : T.rank = r) (U : Unf Xo c σ r) (q : ℕ)
    (Z₀ : Fam T) (k : U.Comp) (x : Frame (U.X k).Ψ r) (h : GA D T) : Prop :=
  ∃ γ ∈ GQ T, ∃ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X k).Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
    (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (hx : x ∈ (U.X k).dom),
    IsSet ψ θ S T hr (U.X k) eT bas ∧ Matched c σ (U.X k) idx e ∧ (U.X k).p0 = q ∧ SelfD (U.X k) (U.X k).Λ ∧
    GlobalTheory.OneMapRef.latW hr (U.X k).Λ = latG T (γ * h) ∧ x = frOf hr eT (mvZ θ (γ * h) Z₀) ∧
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∃ (A : AnFib (U.X k) bas idx e x (U.X k).Λ (ptC U k ⟨x, hx⟩)) (th : (Fin g → ℂ) → ℂ),
      A.Reads 1 (ptC U k ⟨x, hx⟩).s th ∧ MeanOne (U.X k) bas idx x (U.X k).Λ th

theorem exists_frConst {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (sS : S.SigOK) (sT : T.SigOK) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hη : ∃ η, IsEtaTilde D η)
    (hun : ∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) {q : ℕ} {Z₀ : Fam T} (hZ : IsONeg T q Z₀)
    {ΛT : Lt D.host.E T.rank} (dS : IsSelfDualC S (stdL D.host.E S.rank)) (dT : IsSelfDualC T ΛT)
    {f₀ : WO S T → ℂ} (hf : IsVacO ψ θ S T (fun _ => 1) (cartZ T q Z₀) (stdL D.host.E S.rank : Set _) (ΛT : Set _) f₀)
    {mu : GA D T → ℂ} (hmu : MuVal T χS mu) (hQ : ∀ γ ∈ GQ T, ∀ h, mu (γ * h) = mu h)
    (hlat : ∀ h : GA D T, ∃ LT : Lt D.host.E T.rank, GlobalTheory.Ker.IsAA (latG T h) LT ∧
      GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T h) ΛT LT ∧ ∀ u : WO S T,
        u ∈ (latO S T (stdL D.host.E S.rank : Set _) (LT : Set _) fun _ => True) ↔
          ∃ u₀ ∈ (latO S T (stdL D.host.E S.rank : Set _) (ΛT : Set _) fun _ => True), u = actO S T 1 h u₀)
    (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) {t : ℝ}
    (ht : ∀ k τ, (U.X k).c τ = t) (dict : GA D T → Σ k, Frame (U.X k).Ψ r)
    (hpt : ∀ h, IsPt ψ θ S hr U q Z₀ (dict h).1 (dict h).2 h) :
    ∃ cc : U.Comp → ℂ, CUnit cc ∧ FrConst ψ θ S hr om f₀ U dict mu Z₀ cc := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have key : ∀ k : U.Comp, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (x : Frame (U.X k).Ψ r) (h : GA D T), IsPt ψ θ S hr U q Z₀ k x h →
      ∀ γ ∈ GQ T, ∀ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X k).Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
        (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSet ψ θ S T hr (U.X k) eT bas →
        Matched c σ (U.X k) idx e → x = frOf hr eT (mvZ θ (γ * h) Z₀) → ∀ (hx : x ∈ (U.X k).dom)
        (A : AnFib (U.X k) bas idx e x (U.X k).Λ (ptC U k ⟨x, hx⟩)) (th : (Fin g → ℂ) → ℂ),
        A.Reads 1 (ptC U k ⟨x, hx⟩).s th → ∀ w : WO S T, Ker.IsRealPt w →
          om (1, γ * h) f₀ w = a * mu h *
            (Ker.gaussR (U.X k) bas idx x (Ker.zR (U.X k) idx x (rePt θ hr eT w)) *
              ∏ b, th (Ker.zR (U.X k) idx x (rePt θ hr eT w) b)) := by
    intro k
    by_cases hk : ∃ x h, IsPt ψ θ S hr U q Z₀ k x h
    swap
    · exact ⟨1, norm_one, fun x h hp => absurd ⟨x, h, hp⟩ hk⟩
    obtain ⟨x₀, h₀, γ₀, hγ₀, g₀, eT, bas₀, idx₀, e₀, hx₀, hS, hm₀, rfl, hsd, hL₀, rfl, A₀, th₀, hr₀, hmean⟩ := hk
    obtain ⟨-, -, -, -, hF⟩ := oneg_frames D S T r g₀ hr ψ θ _ eT bas₀ idx₀ hS Z₀ hZ
    have hortho := fun h => (oneg_frames D S T r g₀ hr ψ θ _ eT bas₀ idx₀ hS _ (hF h).1).2.2.1
    have hs₀ := hS.2.2.2.2.2.2.2
    obtain ⟨L₀, a₀, m₀, l₀⟩ := hlat (γ₀ * h₀)
    have hv := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hS.2.1 (fun _ => 1) (fun _ => 1) _ _ _ _ _ _ 1 (γ₀ * h₀)
      (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (hF _).2.1 l₀ f₀ hf
    obtain ⟨a, ha, hval⟩ := VacUnit.vac_eq_unit_mul D S T r g₀ hr ψ θ _ eT bas₀ idx₀ hS _ H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H)
      (isRelTraceOneIdempotentModTwo_hostElement H) _ (hF (γ₀ * h₀)).1 L₀ _ hsd (hL₀ ▸ a₀) _ hv th₀
      (isTheta1_of_reads_generator _ H Dw l Xo c r g₀ _ bas₀ idx₀ e₀ _ _ _ A₀ hs₀ hx₀ hsd th₀ hr₀) hmean
    obtain ⟨φ, hφ, hall⟩ := exists_const U hσ hU hr1 hA k (ht k) hsd hS.2.2.2.1 bas₀ idx₀ e₀ hs₀ hm₀
    have hz : Zak ψ θ hr eT bas₀ idx₀ (frOf hr eT (mvZ θ (γ₀ * h₀) Z₀)) (a • φ) (om (1, γ₀ * h₀) f₀) :=
      ⟨hv.2.theta, fun w hw => by
        rw [hval w hw, thR_smul, hall _ hx₀ (hortho _) g₀ bas₀ idx₀ e₀ hs₀ hm₀ A₀ th₀ hr₀]⟩
    refine ⟨a / mu h₀, by rw [norm_div, ha, hmu.norm, div_one], ?_⟩
    rintro x h ⟨γ₁, hγ₁, g₁, eT₁, bas₁, -, -, -, hS₁, -, -, -, hL₁, hx₁, -⟩ γ hγ g eT₂ bas idx e hS₂ hm hx₂ hx A th hth w hw
    have he : ∀ {g' : ℕ} {eT' : D.what₂.Tau ≃ (U.X k).Ψ} {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ},
        IsSet ψ θ S T hr (U.X k) eT' bas' → eT = eT' := fun h' =>
      Equiv.ext fun ρ => Subtype.ext ((hS.2.2.2.2.2.2.1 ρ).trans (h'.2.2.2.2.2.2.1 ρ).symm)
    obtain rfl := he hS₁
    obtain rfl := he hS₂
    have e1 := frOf_injective hr eT (hx₁.symm.trans hx₂)
    have hfin : (γ * h)⁻¹ * (γ₁ * h) ∈ GfC T := by
      apply (hF _).2.2.2.2.1
      rw [(hF (γ₁ * h)).2.2.1, e1, ← (hF _).2.2.1, inv_mul_cancel]
      exact (hF 1).2.2.2.1 (one_mem _)
    have e2 : γ⁻¹ * γ₁ = 1 := by
      refine eq_one_of_rat hS.2.1 (mul_mem (inv_mem hγ) hγ₁) ?_
      have := (MonoidHom.normal_ker (infHom T)).conj_mem _ hfin h
      rwa [show h * ((γ * h)⁻¹ * (γ₁ * h)) * h⁻¹ = γ⁻¹ * γ₁ by group] at this
    obtain rfl : γ = γ₁ := inv_mul_eq_one.1 e2
    obtain ⟨L₁, a₁, m₁, -⟩ := hlat (γ * h)
    rw [← hL₁] at a₁
    rw [← hL₀] at a₀
    obtain rfl : L₀ = L₁ := le_antisymm (le_of_isAA a₀ a₁) (le_of_isAA a₁ a₀)
    subst hx₂
    rw [om_vac_move idx₀ hS sS sT hW hη hun hZ dS dT hf hmu m₀ m₁ (TensVac.sb_smul a hφ) hz w hw, thR_smul,
      hall _ hx (hortho _) g bas idx e hS₂.2.2.2.2.2.2.2 hm A th hth, hQ _ hγ, hQ _ hγ₀]
    ring
  choose cc hcc hkey using key
  exact ⟨cc, hcc, fun h γ hγ => hkey _ _ h (hpt h) γ hγ⟩

end Geo

theorem mu_rat_cast {V W : HSp D} (hV : V = W) {mu : GA D V → ℂ} (h : ∀ γ ∈ GQ V, ∀ h, mu (γ * h) = mu h) :
    ∀ γ ∈ GQ W, ∀ h, castDict hV mu (γ * h) = castDict hV mu h := by
  subst hV; exact h

end GlobalTheory.OneMapRef.FrameConst

end
