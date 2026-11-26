module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem expTw_holds : ExpTw := by
  intro E _ _ _ N φ z _ r _ hrN c hc
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨F₀, ⟨μ, 𝓕, hμ, h𝓕, hF₀⟩, F, hF, hF0, hFt⟩ := hc
  set χ := Model.absC E z
  set Y : GA E N → ℂ := fun g => (((chiDet N χ g)⁻¹ : ℂˣ) : ℂ) with hY
  have hu : ∀ (x : BlockIx N r → Ad E), chiDet N χ (unip x) = 1 := fun x => by
    change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
    rw [det_unip, map_one]
  have hct : F₀ = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 g * ((chiDet N χ g : ℂˣ) : ℂ) := by
    rw [hF₀]
    funext g
    simp only [PositivityTheory.Affgl.CT.ct]
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [mulChi_apply, map_mul, hu, one_mul]
  have hYX : ∀ g, ((chiDet N χ g : ℂˣ) : ℂ) * Y g = 1 := fun g => Units.mul_inv _
  have hYa : ∀ t : ℝ, Y (aT E N r t) = Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := fun t => by
    simp only [hY]
    rw [Units.val_inv_eq_inv_val, ExponentTwist.chiDet_aT hrN.le, ← Complex.exp_neg]
  refine ⟨PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1, ⟨μ, 𝓕, hμ, h𝓕, rfl⟩, LinearMap.mulRight ℂ Y F, ?_, ?_, ?_⟩
  · have h1 := Submodule.mem_map_of_mem (f := LinearMap.mulRight ℂ Y) hF
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have e : LinearMap.mulRight ℂ Y (fun g => F₀ (aT E N r t * g)) =
        ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ) • fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) := by
      funext g
      simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hct, map_mul, Units.val_mul]
      linear_combination (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) * ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ)) * hYX g
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro h
    apply hF0
    funext g
    have h2 := congrFun h g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.zero_apply] at h2
    have h3 : Y g ≠ 0 := Units.ne_zero _
    exact (mul_eq_zero.1 h2).resolve_right h3
  · intro t g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply]
    have hYm : ∀ a b, Y (a * b) = Y a * Y b := fun a b => by simp only [hY, map_mul, mul_inv, Units.val_mul]
    have e : Complex.exp ((c - z * r * (Module.finrank ℚ E : ℂ)) * t) =
        Complex.exp (c * t) * Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hFt, hYm, hYa, e]
    ring

end PositivityTheory.Rg.Rs
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatTw
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.LFun GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem finRep_mulChi {m : ℕ} (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin m) (w.adicCompletion E))
    (x : Sm E m) :
    finRep E m (locGL E m w g) (mulChi m χ x) =
      ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • mulChi m χ (finRep E m (locGL E m w g) x) := by
  have := act_mulChi (o := (Op.fin (locGL E m w g) : Op E m)) χ x
  rw [opAdd, zero_smul, add_zero, opMul, CuspSub.chiDet_locGL, map_smul] at this
  exact this

theorem satLike_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatLike V w B) :
    SatLike (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  intro ψ hψ hK h0
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hψ
  have hxK : ∀ k ∈ KGL w (n := m), finRep E m (locGL E m w k) x = x := fun k hk => by
    have e := hK k hk
    rw [LinearEquiv.coe_coe, finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one,
      one_smul] at e
    exact (mulChi m χ).injective e
  have hx0 : x ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hs := h x hx hxK hx0
  refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hK k hk, by rw [Multiset.card_map, hs.2.2.1],
    fun ϖ hϖ j hj => ?_⟩
  rw [LinearEquiv.coe_coe, GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← map_smul (mulChi m χ),
    ← hs.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
  have e := (mulChi m χ).toAddEquiv.map_finsum
    (fun c : _ ⧸ KGL w (n := m) => Tj ℂ m (Ov E w) ϖ j c.out • ((finRep E m).comp (locGL E m w)) c.out x)
  rw [show (mulChi m χ) _ = _ from e, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
  · simp [hc]
  · change Tj ℂ m (Ov E w) ϖ j c.out • finRep E m (locGL E m w c.out) (mulChi m χ x) = _
    rw [finRep_mulChi, GlobalTheory.SphGal.loc_det_of_Tj hχ hϖ hj hc, smul_comm]
    simp

open GlobalTheory.Mem.Chr.CharModel in
omit [_root_.NumberField.IsTotallyComplex E] in
theorem unrAt_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).UnrAt w := fun x hx => Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = 1
  rw [logNorm_local w x 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]; simp)

open GlobalTheory.Mem.Chr.CharModel in
theorem val_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).val w = qU w (-s) := Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [qU_val, logNorm_local w _ 1 (Formalism.L2.Host.unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring)

theorem satLike_tw {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatLike V w B) (z : ℂ) : SatLike (tw V z) w (B.map (· * qU w (-z))) := by
  have := satLike_map_mulChi (unrAt_absC z w) h
  rw [val_absC] at this
  exact this

end PositivityTheory.Rg.Rs.SatakeVectors

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ChordArithmetic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem mulChi_absC_cancel (a : ℕ) (z : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E z) (mulChi a (Model.absC E (-z)) ψ) = ψ := by
  refine Subtype.ext (funext fun m => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

theorem central_twist {a : ℕ} (w e : ℂ) (h : e + w * a * (Module.finrank ℚ E : ℂ) = 0) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) :
    ∀ (t : ℝ) m, (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) = (mulChi a (Model.absC E w) ψ).1 m := by
  intro t m
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
  have e1 : Complex.exp (e * t) * Complex.exp (w * a * (Module.finrank ℚ E : ℂ) * t) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    linear_combination (t : ℂ) * h
  linear_combination (ψ.1 m * ((chiDet a (Model.absC E w) m : ℂˣ) : ℂ)) * e1

theorem left_eq (c c₁ : ℂ) (r r₁ d : ℕ) (hr : r ≠ 0) (hd : d ≠ 0) :
    (c₁ - -(c / (r * d)) * r₁ * d).re = c₁.re + (r₁ : ℝ) / r * c.re := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c₁ - -(c / (r * d)) * r₁ * d = c₁ + (((r₁ : ℝ) / r : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem right_eq (c c₂ : ℂ) (s r₂ d : ℕ) (hs : s ≠ 0) (hd : d ≠ 0) :
    (c + (c₂ - -(-c / (s * d)) * r₂ * d)).re = c₂.re + ((s : ℝ) - r₂) / s * c.re := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c + (c₂ - -(-c / (s * d)) * r₂ * d) = c₂ + ((((s : ℝ) - r₂) / s : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem left_arith (r s r₁ d lam x y : ℝ) (hr : 0 < r) (h1 : 0 < r₁) (h2 : r₁ < r) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + r₁ / r * y) / d - r₁ * (r + s - r₁) / 2 ≤ -lam * (r₁ * (r + s - r₁))) :
    x / d - r₁ * (r - r₁) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + r₁ / r * y) / d = x / d + r₁ / r * (y / d) := by ring
  have e2 : r₁ / r * (r * s / 2 - lam * (r * s)) = r₁ * s / 2 - lam * (r₁ * s) := by field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

theorem right_arith (r s r₂ d lam x y : ℝ) (hs : 0 < s) (h1 : 0 < r₂) (h2 : r₂ < s) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + (s - r₂) / s * y) / d - (r + r₂) * (r + s - (r + r₂)) / 2 ≤ -lam * ((r + r₂) * (r + s - (r + r₂)))) :
    x / d - r₂ * (s - r₂) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + (s - r₂) / s * y) / d = x / d + (s - r₂) / s * (y / d) := by ring
  have e2 : (s - r₂) / s * (r * s / 2 - lam * (r * s)) = r * (s - r₂) / 2 - lam * (r * (s - r₂)) := by
    field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

end PositivityTheory.Rg.Rs.ChordArithmetic
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTensA
noncomputable section

open NumberField MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl

namespace PositivityTheory.Rg.Rs.SliceTensor

theorem interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (S : Finset K) (a : S → A), ∀ c ∈ A, c = ∑ κ : S, c κ.1 • (a κ : K → ℂ) := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.CTFin.UniSol.exists_finset_separating A
  let ev : A →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun κ => (LinearMap.proj κ.1 : (K → ℂ) →ₗ[ℂ] ℂ) ∘ₗ A.subtype
  have hinj : LinearMap.ker ev = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun c hc => Subtype.ext (hS c.1 c.2 fun κ hκ => ?_)
    exact congrFun hc ⟨κ, hκ⟩
  obtain ⟨P, hP⟩ := ev.exists_leftInverse_of_injective hinj
  refine ⟨S, fun κ => P (Pi.single κ 1), fun c hc => ?_⟩
  have h1 : P (ev ⟨c, hc⟩) = ⟨c, hc⟩ := LinearMap.congr_fun hP _
  have h2 : ev ⟨c, hc⟩ = ∑ κ : S, c κ.1 • (Pi.single κ 1 : S → ℂ) := by
    funext κ'
    simp [Finset.sum_apply, Pi.single_apply, ev]
  have h3 := congrArg Subtype.val h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum] at h3
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
  exact h3.symm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem slice_mem {r s : ℕ} {L : Subgroup (GL (Fin (r + s)) (Af E))} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) {J : Set (Module.End ℂ (Sm E (r + s)))} (hJ : J ⊆ Zalg E (r + s))
    {J₁ : Set (Module.End ℂ (Sm E r))}
    (H3 : ∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0)
    (F : Sm E (r + s)) (hN : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g)
    (hLv : ∀ k ∈ L, finRep E (r + s) k F = F)
    (hC : ∀ g : GA E (r + s), (fun k : Kinf E (r + s) => (cptRep E (r + s) k F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ)
    (hZ : ∀ z ∈ J, z F = 0) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (m₂ : GA E s) (G : Sm E r)
    (hA : IsAutForm G)
    (hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) :
    G ∈ genSpace (Slice1.levelOne s L t) (ρ.comp (Slice1.levK E r s)) J₁ := by
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (Slice1.levK E r s)) := by
    intro g
    have key := Slice1.coeff_comp ρ (Slice1.levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (Slice1.levK E r s k * κ)))
    rw [hGv, Slice1.lev_infGL_right, ← Slice1.toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]
  have hle : (Slice1.levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (Slice1.mem_levelOne.1 hk))) _
    rw [← hk', Slice1.lev_finGL_right]
  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => ?_)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (Slice1.commute_rt_of_mem_Zalg (hJ hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
    · rw [hGv]
      change _ = F.1 (lev (Ad E) r s (m, 1) * h)
      have e : (m, m₂) = ((m, 1) * (1, m₂) : GA E r × GA E s) := by simp
      rw [e, map_mul]
      simp only [h, mul_assoc]
  exact ⟨hA, fun k hk => hle hk, hcoef, hkill⟩

end PositivityTheory.Rg.Rs.SliceTensor

end
end
