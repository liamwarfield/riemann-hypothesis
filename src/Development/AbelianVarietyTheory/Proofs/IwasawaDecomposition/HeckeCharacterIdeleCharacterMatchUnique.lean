module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLevelFormsIffStdGroupTypeSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrEqUnique

theorem eq_one_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} (h : ChrEq c 1) (x : (AE D)ˣ) : c x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D c h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) c 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

noncomputable def phase : ℂˣ →* Circle where
  toFun z := ⟨(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)])⟩
  map_one' := Circle.ext (by
    change ((1 : ℂˣ) : ℂ) / ((‖((1 : ℂˣ) : ℂ)‖ : ℝ) : ℂ) = 1
    simp)
  map_mul' x y := Circle.ext (by
    change ((x * y : ℂˣ) : ℂ) / ((‖((x * y : ℂˣ) : ℂ)‖ : ℝ) : ℂ) =
      (x : ℂ) / ((‖(x : ℂ)‖ : ℝ) : ℂ) * ((y : ℂ) / ((‖(y : ℂ)‖ : ℝ) : ℂ))
    rw [Units.val_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])

theorem continuous_phase : Continuous phase :=
  Continuous.subtype_mk (Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)) _

noncomputable def normPow (t : ℝ) : ℂˣ →* Circle where
  toFun z := Circle.exp (t * Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), mul_add,
      Circle.exp_add]

theorem continuous_normPow (t : ℝ) : Continuous (normPow t) :=
  Circle.exp.continuous.comp (continuous_const.mul
    (Units.continuous_val.norm.log fun z => norm_ne_zero_iff.2 z.ne_zero))

theorem eq_one_of_forall {z : ℂˣ} (h : ∀ φ : ℂˣ →* Circle, Continuous φ → φ z = 1) : z = 1 := by
  have hn : ‖(z : ℂ)‖ = 1 := by
    by_contra hne
    have hl : Real.log ‖(z : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 z.ne_zero) hne
    have h1 := h _ (continuous_normPow (Real.pi / Real.log ‖(z : ℂ)‖))
    change Circle.exp (_ * _) = 1 at h1
    rw [div_mul_cancel₀ _ hl] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp only [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h2
    norm_num at h2
  have h2 := congrArg (fun w : Circle => (w : ℂ)) (h _ continuous_phase)
  change (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) = 1 at h2
  rw [hn, Complex.ofReal_one, div_one] at h2
  exact Units.ext h2

theorem hchar_eq_one (D : D7) (ξ : HChar D.host.E) (h : ∀ P k, ξ.locK P k = 1) : ξ = 1 := by
  obtain ⟨Φ, hΦ, -, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Φ.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  refine Subtype.ext (MonoidHom.ext fun y => eq_one_of_forall fun φ hφ => ?_)
  have hc : ChrEq (φ.comp (ξ.1.comp u)) (1 : HChar D.host.E) := by
    refine ⟨⟨hφ.comp (ξ.2.1.comp hu), fun k => ?_⟩, fun P e he k x hx => ?_⟩
    · have : u (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (h1 k)
      change φ (ξ.1 (u _)) = 1
      rw [this, ξ.2.2, map_one]
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Φ (x : AE D) = _
        rw [hx, h2 P e he]
      have h3 : ξ.1 (localIdele D.host.E P (atFin P k)) = 1 := h P k
      change ((φ (ξ.1 (u x)) : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [this, h3, map_one]
      rfl
  have hy : u (Units.map Φ.symm.toRingHom.toMonoidHom y) = y := Units.ext (Φ.apply_symm_apply _)
  have := eq_one_of_chrEq hc (Units.map Φ.symm.toRingHom.toMonoidHom y)
  change φ (ξ.1 (u _)) = 1 at this
  rwa [hy] at this

theorem hchar_unique (D : D7) (c : IdC D) (χ χ' : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c χ') : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine hchar_eq_one D _ fun P k => ?_
  obtain ⟨Φ, -, -, -, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := PlaceIdem.exists_isPlIdem D j j1 j2 j3 P
  let x : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (localIdele D.host.E P (atFin P k))
  have hx : (x : AE D) = locE D e (k : D.host.E) := Φ.symm_apply_eq.2 (h2 P e he k).symm
  change χ.locK P k * (χ'.locK P k)⁻¹ = 1
  rw [mul_inv_eq_one]
  exact Units.ext ((h.2 P e he k x hx).symm.trans (h'.2 P e he k x hx))

theorem idc_unique (D : D7) (c c' : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c' χ) : c = c' := by
  have hc : ChrEq (c * c'⁻¹ : (AE D)ˣ →* Circle) (1 : HChar D.host.E) := by
    refine ⟨⟨h.1.1.mul h'.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.1.2, h'.1.2, inv_one, one_mul]
    · change ((c x * (c' x)⁻¹ : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, h.2 P e he k x hx, h'.2 P e he k x hx, mul_inv_cancel₀ (Units.ne_zero _)]
      rfl
  exact MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_chrEq hc x)

theorem isUnitary_of_chrEq (D : D7) (c : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) : χ.IsUnitary := by
  have hc := h.1
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (hc.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨hc, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [hchar_unique D c χ χ' h h']
  exact fun x => Circle.norm_coe (c (u x))

theorem chrEq_unique : ∀ (D : D7), (∀ (c : IdC D) (χ χ' : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c χ' → χ = χ') ∧ (∀ (c c' : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c' χ → c = c') ∧ ∀ (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → χ.IsUnitary :=
  fun D => ⟨hchar_unique D, idc_unique D, isUnitary_of_chrEq D⟩

end GlobalTheory.ChrEqUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_ideleCharacter_match_unique : ∀ (D : D7), (∀ (c : IdC D) (χ χ' : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c χ' → χ = χ') ∧ (∀ (c c' : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c' χ → c = c') ∧ ∀ (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → χ.IsUnitary := by
  first | exact @GlobalTheory.ChrEqUnique.chrEq_unique | exact GlobalTheory.ChrEqUnique.chrEq_unique | (intros; apply GlobalTheory.ChrEqUnique.chrEq_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp


set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfQ_of_hasInfExp (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : D.what₂.Tau → ℚ)
    (hc : ChrEq c χ) (h : ∀ τ, HasInfExp D c τ (e τ)) : χ.HasInfQ (tauE D) e := by
  classical
  choose n hn hx using h
  refine ⟨n, hn, fun k => ?_⟩
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨θ, hθ⟩ : ∃ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ := ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((c (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro z
    have h1 : c (T.toHomUnits z) = ∏ τ, c (T.toHomUnits (Pi.mulSingle τ (z τ))) := by
      conv_lhs => rw [← Finset.univ_prod_mulSingle z]
      rw [map_prod, map_prod]
    have h2 := congrArg Circle.coeHom h1
    rw [map_prod] at h2
    refine h2.trans (Finset.prod_congr rfl fun τ _ => ?_)
    have h3 := (hx τ).2 θ hθ (T.toHomUnits (Pi.mulSingle τ (z τ))) (tf _) fun τ' hτ' =>
      (ti _ τ').trans (by rw [Pi.mulSingle_eq_of_ne hτ', Units.val_one])
    have h4 : θ τ (infPart D ((T.toHomUnits (Pi.mulSingle τ (z τ)) : (AE D)ˣ) : AE D)) = z τ :=
      (ti _ τ).trans (by rw [Pi.mulSingle_eq_same])
    rw [h4] at h3
    exact h3
  rw [← eq_inf D c χ hc k _ _ (hab _) (hb _).1 (hb _).2, hT _ (ha (Units.map (incA D).toMonoidHom k)).2, key]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h5 : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom (a (Units.map (incA D).toMonoidHom k)) : ℂˣ) : ℂ) =
      tauE D τ (k : D.host.E) :=
    (congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)
  rw [h5]

theorem hasInfExp_iff_hasInfQ : ∀ (D : D7) (c : GlobalTheory.Mem.Th.IdC D) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ),
    Formalism.IndefR.Links.ChrEq c χ → ((∀ τ, HasInfExp D c τ (a τ)) ↔ χ.HasInfQ (Formalism.L2.Host.embTau D) a) :=
  fun D c χ a hc => ⟨hasInfQ_of_hasInfExp D c χ a hc, hasInfExp_of_chrEq D c χ a hc⟩

end GlobalTheory.HeckeInfExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TupChar

theorem chrEq_mul {D : D7} {c c' : IdC D} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => (congrArg₂ (· * ·) (h.1.2 x) (h'.1.2 x)).trans (mul_one _)⟩,
    fun P e he k x hx => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
  rfl

theorem unramEverywhere {D : D7} {c : IdC D} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hu : ∀ P, χ.UnrAt P) :
    UnramEverywhere D c := fun x hx h4 h5 => by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

end GlobalTheory.Mem.TupChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VecP


open scoped ComplexOrder in
theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hε1 : ∀ a, ε a = 1 := fun a =>
    ((hε a).resolve_right fun h' => absurd h'.2 (not_le.mpr a.2)).1
  have hB1 : Bᴴ * G * B = 1 := by simpa [hε1] using hB
  have hBC : B * (Bᴴ * G) = 1 := mul_eq_one_comm.mp hB1
  have hGB : G * B = (Bᴴ * G)ᴴ := by
    calc G * B = (B * (Bᴴ * G))ᴴ * (G * B) := by rw [hBC, conjTranspose_one, Matrix.one_mul]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ := by rw [hB1, Matrix.mul_one]
  have hG : G = (Bᴴ * G)ᴴ * (Bᴴ * G) := by
    calc G = G * (B * (Bᴴ * G)) := by rw [hBC, Matrix.mul_one]
      _ = G * B * (Bᴴ * G) := by rw [Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G) := by rw [hGB]
  have hinj : Function.Injective (Bᴴ * G).mulVec := by
    intro v w hvw
    have h2 := congrArg (fun x => B *ᵥ x) hvw
    simpa only [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec] using h2
  unfold IsCartanInv
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

end GlobalTheory.OneMapRef.VecP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FinDatum

theorem isRoots_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {r n N : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (ε : ℤˣ) (hN : l.M ∣ N)
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (h : IsRoots l L ((ε : ℤ) • mk) N Y) :
    IsRoots l L mk l.M fun q => (ε : ℤ) • Y q := by
  intro q b
  obtain ⟨⟨a, ha, h1, h2⟩, j, hj⟩ := h q b
  obtain ⟨m, rfl⟩ := hN
  refine ⟨⟨a, ha, h1, ?_⟩, j, fun s hs => ?_⟩
  · have h3 := zsmul_mem h2 (ε : ℤ)
    rw [smul_sub, LinearMap.smul_apply, smul_comm (l.M : E)⁻¹, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul] at h3
    exact h3
  · obtain ⟨u, hu, e⟩ := hj s hs
    refine ⟨(ε : ℤ) • m • u, zsmul_mem (nsmul_mem hu m) _, ?_⟩
    show s • (ε : ℤ) • Y q b = _
    rw [smul_comm s, e, smul_comm (2 * l.M), smul_smul (2 * l.M), mul_assoc]

variable {D : D7}

theorem lat_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) :
    LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, h', -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatIsom V (T.Q.Dw ((i : ℕ) + 1)).EF
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
    rintro V hr rfl h h'
    exact ⟨h, h'⟩
  exact key _ hr hV h h'

theorem latR_range {E : Type} [Field E] [NumberField E] {m r : ℕ} (hr : m = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    GlobalTheory.AdTh.latR hr (LinearMap.range (LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι)) = LinearMap.range ι := by
  subst hr
  unfold GlobalTheory.AdTh.latR
  rw [← LinearMap.range_comp]
  rfl

theorem splitOffBad_one (V : HSp D) : SplitOffBad V 0 1 := by
  refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩, zero_mul _⟩,
    fun _ h => absurd h (Finset.notMem_empty _), fun i j => ?_⟩
  rw [show Formalism.L2.Theta.mt V 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]

theorem isFinOf_finR (S T : HSp D) {r : ℕ} (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) :
    GlobalTheory.AdTh.colsR hr (y.submatrix id (Fin.cast hr))ᵀ = y ∧
      GlobalTheory.AdTh.IsFinOf S T (y.submatrix id (Fin.cast hr))ᵀ (finR S hr y) := by
  subst hr
  exact ⟨rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

theorem mem_std_star (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ} (v : Fin n → D.host.E)
    (h : v ∈ Formalism.L2.Pj.stdLat D.host.E n) : (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := by
  intro j _
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j trivial)
  exact Submodule.mem_one.2 ⟨H.bar a, (H.bar_eq a).trans (congrArg star ha)⟩

theorem smul_eq_zero_of_smul_rep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (q : LevQ Dw l) (s : 𝓞 E) (z : Dw.La) (hz : s • (cSep l • levRep q) = l.M • z) :
    s • q = 0 := by
  have hrep : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  rw [← hrep, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hM : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl))
  have e : s • levRep q = (l.M : 𝓞 E) • z - (cSep l - 1) • s • levRep q := by
    rw [Nat.cast_smul_eq_nsmul, ← hz, sub_smul, one_smul, smul_comm s, sub_sub_cancel]
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul hM trivial) (Submodule.smul_mem_smul (LevelPairing.cSep_spec _).2 trivial)


end GlobalTheory.OneMapRef.FinDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem intTrace_modEq (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I)
    (hnorm : Ideal.absNorm v.asIdeal = p) (x : 𝓞 K) (b : ℤ) (hxv : x - (b : 𝓞 K) ∈ v.asIdeal) (hxI : x ∈ I) :
    ∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = v.asIdeal * I := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hpI
  have hPv : P ≤ v.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_left (I := v.asIdeal) (J := I)
  have hPI : P ≤ I.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_right (I := v.asIdeal) (J := I)
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hPv
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap hPI
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ I) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ I) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let e : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] ((𝓞 K ⧸ v.asIdeal) × (𝓞 K ⧸ I)) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientMulEquivQuotientProd v.asIdeal I hvI),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have he : e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk v.asIdeal x, Ideal.Quotient.mk I x) := rfl
  have hx2 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx1 : Ideal.Quotient.mk v.asIdeal x = algebraMap (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk P b) := by
    rw [Ideal.Quotient.eq.mpr hxv]
    show _ = Ideal.Quotient.mk v.asIdeal (algebraMap ℤ (𝓞 K) b)
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardv : Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
    rw [← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfr : Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ v.asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P b := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv e, he,
      Algebra.trace_prod_apply, hx2, map_zero, add_zero, hx1, Algebra.trace_algebraMap, hfr, one_smul]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  obtain ⟨m, hm⟩ := key
  exact ⟨m, by linear_combination hm⟩

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem integral_of_mul (w : HeightOneSpectrum (𝓞 K)) (n z s y : 𝓞 K) (hn : n ≠ 0) (hs : s ∉ w.asIdeal)
    (h : z * s = n * y) :
    algebraMap K (Af K) ((z : K) / (n : K)) w ∈ w.adicCompletionIntegers K := by
  have hs0 : (s : K) ≠ 0 := by
    intro h0; apply hs; rw [show s = 0 from by exact_mod_cast h0]; exact zero_mem _
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn
  have hq : (z : K) / (n : K) = (y : K) / (s : K) := by
    rw [div_eq_div_iff hn0 hs0]
    have := congrArg (fun t : 𝓞 K => (t : K)) h
    simp only [map_mul] at this
    push_cast at this
    linear_combination this
  rw [hq, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ((y : K) / (s : K))
  erw [e]
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, div_one]
  exact HeightOneSpectrum.intValuation_le_one w y

theorem exists_cofactor (p : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) :
    ∃ I : Ideal (𝓞 K), IsCoprime v.asIdeal I ∧ Ideal.span {(p : 𝓞 K)} = v.asIdeal * I := by
  have hpv : (p : 𝓞 K) ∈ v.asIdeal := by
    have := Ideal.absNorm_mem v.asIdeal
    rwa [hnorm] at this
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpv)
  refine ⟨I, ?_, hI⟩
  have hpr := (Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime
  rw [Ideal.isCoprime_iff_gcd, hpr.irreducible.gcd_eq_one_iff]
  rintro ⟨J, rfl⟩
  apply hsq
  have : Ideal.span {(p : 𝓞 K)} ≤ v.asIdeal ^ 2 := by
    rw [hI, pow_two, ← mul_assoc]; exact Ideal.mul_le_left (I := v.asIdeal * v.asIdeal) (J := J)
  exact this (Ideal.mem_span_singleton_self _)

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (a : 𝓞 K) (b : ℤ)
    (hab : a - (b : 𝓞 K) ∈ v.asIdeal) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((a : K) / (p : K)) -
        algebraMap K (Af K) ((x : K) / (p : K))) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp hvI
  have htv : t ∉ v.asIdeal := fun h =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hut ▸ add_mem hu h))
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmemp : ∀ z ∈ v.asIdeal * I, ∃ y, z = (p : 𝓞 K) * y := fun z hz => by
    rw [← hpI, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm]⟩
  have hxv : (b : 𝓞 K) * t - b ∈ v.asIdeal := by
    have e : (b : 𝓞 K) * t - b = -((b : 𝓞 K) * u) := by linear_combination (b : 𝓞 K) * hut
    rw [e]; exact neg_mem (Ideal.mul_mem_left _ _ hu)
  refine ⟨b * t, intTrace_modEq p hp v I hvI hpI hnorm _ b hxv (Ideal.mul_mem_left _ _ ht), fun w => ?_⟩
  have hcomp : (α * algebraMap K (Af K) ((a : K) / (p : K)) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K))) w =
      α w * algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w =
        algebraMap K (Af K) (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) w := by
      rw [show (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) =
        (a : K) / (p : K) - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) by push_cast; ring, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    have hmem : (a - (b : 𝓞 K) * t) * t ∈ w.asIdeal * I := by
      refine Ideal.mul_mem_mul ?_ ht
      have e : a - (b : 𝓞 K) * t = (a - b) - ((b : 𝓞 K) * t - b) := by ring
      rw [e]; exact sub_mem hab hxv
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact integral_of_mul w _ _ t y hp0 htv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push_neg at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul hsv (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := integral_of_mul w (p : 𝓞 K) ((b : 𝓞 K) * t) s y hp0 hsw (by rw [mul_comm]; exact hy)
    simpa using this

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

theorem stdChar_placeIdem_div : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D ψ hψ p hp v hnorm hsq ε hε a b hab
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 a b hab
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F)) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)) +
        (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F)) = ((b : ℚ) + p * m) / p := by
    have e : (x : D.host.F) / (p : D.host.F) = ((p : ℚ)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p * m) / p : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.StdCharDegOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAddChar_placeIdempotent_div_prime : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  first | exact @GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | exact GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | (intros; apply GlobalTheory.StdCharDegOne.stdChar_placeIdem_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLevelFormsIffStdGroupTypeSpaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLevelForms_iff_stdGroupTypeSpace : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → UnitFr P → RatIso P e → ∀ (G₀ : Type) [Group G₀] (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch red P₀ ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ↔ (fun g => F (toGf P g)) ∈ NG.TypeSp (wtRep c e) (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) := by
  first | exact @GlobalTheory.MtInType.cutSp_iff_typeSp | exact GlobalTheory.MtInType.cutSp_iff_typeSp | (intros; apply GlobalTheory.MtInType.cutSp_iff_typeSp <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilDatumOOfRankEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilOriented

theorem exists_isWeilDatumO_of_rank_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  intro D ψ hψ V W χ χ' om ha hw
  have hr : V.rank ≤ W.rank := ha.1.le
  obtain ⟨e, hc, hcs, he, hrat, hsm, hheis, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr
  let E : (WA V W → ℂ) ≃ₗ[ℂ] (WO V W → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv
  obtain ⟨omO, hom⟩ := exists_extend (ThS ψ V W) E om
  have hom' : ∀ p (Φ : ThS ψ V W), omO p (fun x => Φ.1 (e x)) = fun x => (om p Φ).1 (e x) := hom
  have hsurj : ∀ f, IsThetaFunO ψ V W f → ∃ Φ : ThS ψ V W, f = fun x => Φ.1 (e x) := fun f hf => by
    have e1 : f = fun x => (fun y => f (e.symm y)) (e x) := by funext x; simp
    refine ⟨⟨fun y => f (e.symm y), mem_ThS.2 ((hth ψ _).1 ?_)⟩, e1⟩
    rw [← e1]; exact hf
  have hTh : ∀ Φ : ThS ψ V W, IsThetaFunO ψ V W fun x => Φ.1 (e x) := fun Φ => (hth ψ _).2 (mem_ThS.1 Φ.2)
  have hact : ∀ g h x, e (actO V W g h x) = actHom V W g h (e x) := fun g h x => by
    rw [he, he]; exact (GlobalTheory.OrientedSmall.bridgeSmall D V W hr).2 g h x
  refine ⟨omO, ⟨hψ, ha.2.1.1, ha.2.2.1.1, ha.2.2.2.1, ha.2.2.2.2, fun p f hf => ?_, fun g h w₀ f hf => ?_,
    fun γ hγ γ' hγ' f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_,
    fun ε hε g h hg hh x y hx hy => ?_⟩, fun p Φ => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']; exact hTh _
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    let Φ' : ThS ψ V W := ⟨Heisenberg₂ ψ V W (e w₀) Φ.1,
      mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis hψ (mem_ThS.1 Φ.2) _)⟩
    rw [hheis, hom', hheis, hact, ← hw.Heisenberg₂ g h (e w₀) Φ Φ' rfl]
    exact hom' _ Φ'
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    simp only [map_zero]
    exact hw.aut γ hγ γ' hγ' Φ
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    simp only [hom']
    exact hw.cont Φ (e w)
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨j1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D V W
    have : BorelSpace (WA V W) := ⟨rfl⟩
    have : BorelSpace (WO V W) := ⟨rfl⟩
    obtain ⟨ν, hν, hF, hint⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WO V W) e.symm hcs
      (by simpa using hc) (ratL V W) (ratL W V) (fun x => by rw [← hrat, e.apply_symm_apply]) μ 𝓕 hμ h𝓕
    refine lintegral_eq_of_integral_eq (ratL W V) hK hcov (hTh _).cont (hTh _).cont (norm_periodic hψ (hTh _))
      (norm_periodic hψ (hTh _)) hμ h𝓕 ?_
    rw [← hint, ← hint]
    simp only [e.apply_symm_apply]
    exact hw.unit ν _ hν hF p Φ
  · obtain ⟨r, hr0, hℓ⟩ := hw.split ε hε g h hg hh x y hx hy
    refine ⟨r, hr0, fun ℓ hinv f hf => ?_⟩
    obtain ⟨Φ, rfl⟩ := hsurj f hf
    have := hℓ (ℓ ∘ₗ E.toLinearMap ∘ₗ (ThS ψ V W).subtype) (fun u hu Ψ Ψ' hΨ => ?_) Φ
    · rw [hom']
      unfold splitFac at this
      rw [if_pos hr] at this
      exact this
    · have hu' : cA D ε • e.symm u = e.symm u := by
        apply e.injective
        rw [hsm, e.apply_symm_apply]
        exact Matrix.ext hu
      have := hinv (e.symm u) (fun i j => congrFun (congrFun hu' i) j) _ (hTh Ψ)
      rw [hheis, e.apply_symm_apply, ← hΨ] at this
      exact this
  · simp only [← he]
    exact hom' p Φ

end GlobalTheory.Mem.WeilOriented
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameSplitPlaceEntriesOffPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplit

theorem lemB_pf : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : GA D V), L.Pg ⊆ T → L.Q ⊆ T → x ∈ GfC V → finE V x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T → x ∈ levS V β L ∧ levChi V β L x = 1 := by
  intro D V β L T x hg hq hx hK
  have h3 : ∀ PP ∈ T, Formalism.L2.DIV.redFn β PP (finE V x) = 1 := by
    have h1 : finE V x ∈ ⨅ PP ∈ T, Formalism.L2.DIV.princAt β PP := hK.2
    exact fun PP hP => (Formalism.L2.DIV.mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  refine ⟨⟨hx, Formalism.L2.DIV.Kg_le_lev hg hq hK⟩, ?_⟩
  have hr : Formalism.L2.DIV.rTup β L (finE V x) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP.1 (finE V x)) = 1
    rw [h3 PP.1 (hg PP.2)]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [hr, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · rfl
  · intro PP hP
    rw [h3 PP (hq hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem int_of_lt {D : D7} {n : ℕ} (y : Matrix (Fin n) (Fin n) (EAf D))
    (h : ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin n), Valued.v (GlobalTheory.StdFrames.cpt Q (y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b)) < 1)
    (a b : Fin n) : y a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 : y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    (GlobalTheory.AdIsom.mem_OA _).2 fun Q => le_of_lt (h Q a b)
  have := add_mem h2 h1
  rwa [sub_add_cancel] at this

set_option maxHeartbeats 2000000 in
theorem glInt_of_int {D : D7} {n : ℕ} (y : GL (Fin n) (EAf D))
    (i1 : ∀ a b, y.val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i2 : ∀ a b, (y⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.intGL D.host.F D.host.E n z = y ∧
      ∀ a b, ((z.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = y.val a b := by
  let φ : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) →+* Matrix (Fin n) (Fin n) (EAf D) :=
    RingHom.mapMatrix (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have inj : Function.Injective φ := fun M N h => Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
  let zM : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i1 a b⟩
  let zI : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i2 a b⟩
  have e1 : φ zM = y.val := by ext a b; rfl
  have e2 : φ zI = (y⁻¹).val := by ext a b; rfl
  have m1 : zM * zI = 1 := inj (show φ (zM * zI) = φ 1 by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have m2 : zI * zM = 1 := inj (show φ (zI * zM) = φ 1 by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  exact ⟨⟨zM, zI, m1, m2⟩, Units.ext e1, fun a b => rfl⟩

set_option maxHeartbeats 800000 in
theorem kg_of_cpt : ∀ (D : D7) (V : HSp D) (β x : GL (Fin V.rank) (EAf D)) (T : Finset (Formalism.L2.DIV.Pl D.host.E)), x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V β x T hU h1 h2
  have hyi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have i1 := int_of_lt (β⁻¹ * x * β).val h1
  have i2 := int_of_lt ((β⁻¹ * x * β)⁻¹).val (by rw [hyi]; exact h2)
  obtain ⟨z, hz0, hzv⟩ := glInt_of_int (β⁻¹ * x * β) i1 i2
  have hz : Formalism.L2.DIV.frGL β z = x := by
    show β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank z * β⁻¹ = x
    rw [hz0]; group
  have hS : x ∈ Formalism.L2.DIV.St β := ⟨z, hz⟩
  have hred : ∀ PP, Formalism.L2.DIV.redFn β PP x = 1 := by
    intro PP
    rw [← hz, Formalism.L2.DIV.redFn_frGL]
    apply Units.ext
    ext a b
    show Formalism.L2.DIV.resS D.host.F PP (z.val a b) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)) a b
    have h0 : Formalism.L2.DIV.resS D.host.F PP (z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b) = 0 := by
      rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
      have e3 : ((z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
          (β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b := by
        rw [← hzv a b, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e3]; exact h1 PP a b
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  exact ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun _ => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hred PP⟩⟩

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have h1 : (((x⁻¹ : Formalism.AUTREP.GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
  have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
  simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact h2

theorem lemA_pf (hC2 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ T : Finset (Formalism.L2.DIV.Pl D.host.E), finE V (P.ψ κ) ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hC2 D V n hF P β Λ N hS hβ s
  refine ⟨h, fun κ hκ hk T => ?_⟩
  have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
    have := Subgroup.inv_mem _ hk
    rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
  have e : finE V (P.ψ κ⁻¹) = (finE V (P.ψ κ))⁻¹ := by rw [map_inv, map_inv]
  refine kg_of_cpt D V β (finE V (P.ψ κ)) T (GlobalTheory.LevSplit.finE_mem_UA V _) (hh κ hκ hk) ?_
  have := hh κ⁻¹ (trivOutside_inv hκ) hk'
  rwa [e] at this

theorem stdFrame_splitPlace_entries_off_place (hA : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) (hC : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hDd : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hE : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hDd D V n hF P β hS s
  refine ⟨h, fun κ hκ hk Q a b => ?_⟩
  by_cases hQ : Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal
  · rcases hE D hF s Q hQ with rfl | rfl
    · exact hh κ hκ hk a b
    · have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
        have := Subgroup.inv_mem _ hk
        rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
      refine hC D V β Λ N hβ (P.ψ κ) s.w (fun a b => ?_) a b
      have := hh κ⁻¹ (trivOutside_inv hκ) hk' a b
      rwa [map_inv, map_inv] at this
  · rw [map_sub, hA D V n hF P β hS s κ hκ Q hQ a b, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.RowLevelSplit
end
end
