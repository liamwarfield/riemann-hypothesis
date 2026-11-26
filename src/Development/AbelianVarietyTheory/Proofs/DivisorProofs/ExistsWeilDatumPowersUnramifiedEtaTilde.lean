module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionAutomorphySourceGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousProduct
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO GlobalTheory.FinWeil GlobalTheory.SplitScalar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem actO_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

theorem actO_one (u : WO S T) : actO S T 1 1 u = u := by
  unfold actO
  rw [inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_parts (p : GA D S × GA D T) : ∃ a ∈ GinfC S, ∃ b ∈ GinfC T, ∃ k ∈ GfC S, ∃ l ∈ GfC T,
    p = (a, b) * (k, l) ∧ p = (k, l) * (a, b) := by
  obtain ⟨a, ha, k, hk, e1⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 p.1
  obtain ⟨b, hb, l, hl, e2⟩ := (GlobalTheory.UnitarySplit.real_finite_split D T).1 p.2
  refine ⟨a, ha, b, hb, k, hk, l, hl, Prod.ext e1 e2, Prod.ext ?_ ?_⟩
  · exact e1.trans ((GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha k hk)
  · exact e2.trans ((GlobalTheory.UnitarySplit.real_finite_split D T).2.1 b hb l hl)

theorem fin_eq_smul (hψ : IsStdChar D ψ (-1)) (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    (hlam : GlobalTheory.FinWeil.GoodNorm (sgO D) lam) {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}
    (h : IsLatRep hψ.1 ΛS ΛT w lam Om) (p : GA D S × GA D T) :
    ∃ c : ℂ, ∀ f : thetaSub ψ S T, of p f = c • (Om p f : WO S T → ℂ) := by
  obtain ⟨a, ha, b, hb, k, hk, l, hl, -, rfl⟩ := exists_parts p
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T) Om
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => hom p ⟨f, hf⟩
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ hψ S T (of (k, l) * om (k⁻¹, l⁻¹))
    (fun f h1 => by
      rw [Module.End.mul_apply, ho _ f h1]
      exact hf.pres _ _ (Om _ ⟨f, h1⟩).2)
    (fun u f h1 => by
      obtain ⟨f', e1, e2⟩ := h.Heisenberg₂ hψ (inv_mem hk) (inv_mem hl) u ⟨f, h1⟩
      have e1' : (f' : WO S T → ℂ) = heisO ψ S T u f := e1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← e1', hom, e2, hf.Heisenberg₂ k hk l hl _ _ (Om _ ⟨f, h1⟩).2,
        ← actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one, ho _ f h1])
    (fun μ 𝓕 hμ h𝓕 f h1 => by
      rw [Module.End.mul_apply, ho _ f h1, hf.unit μ 𝓕 hμ h𝓕 _ _ (Om _ ⟨f, h1⟩).2]
      exact h.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, h1⟩)
  refine ⟨c, fun f => ?_⟩
  have e := hc _ (Om (k, l) f).2
  rw [Module.End.mul_apply, hom, ← Module.End.mul_apply, ← map_mul,
    show ((k⁻¹, l⁻¹) : GA D S × GA D T) * (k, l) = 1 from inv_mul_cancel ((k, l) : GA D S × GA D T), map_one,
    Module.End.one_apply] at e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf.triv a ha b hb _ f.2, h.real_triv ha hb, e]

theorem fin_inf_comm (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) (p q : GA D S × GA D T) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  obtain ⟨a, ha, b, hb, k, hk, l, hl, rfl, -⟩ := exists_parts q
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (oi (a, b)).restrict fun g hg => hi.pres _ g hg
  have hL : ∀ m, (L m : WO S T → ℂ) = oi (a, b) m := fun _ => rfl
  have e := congrArg Subtype.val (h.comm L (fun x v => Subtype.ext (by
    have e1 := congrArg XF.val (rhoF_real ha hb x)
    rw [coe_rhoF] at e1
    rw [hL, coe_opF, coe_opF, hL, map_smul, hi.Heisenberg₂ a ha b hb _ _ v.2, e1])) p ⟨f, h1⟩)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hi.triv k hk l hl _ h1,
    hi.triv k hk l hl _ (hf.pres _ _ h1), hc ⟨f, h1⟩, map_smul, ← hL, ← e, ← hc]
  rfl

theorem eventually_smul (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {f : WO S T → ℂ} (h1 : IsThetaFunO ψ S T f) :
    ∀ᶠ p in 𝓝 (1 : GA D S × GA D T), ∃ c : ℂ, of p f = c • f := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  filter_upwards [h.eventually_fix hS hT ⟨f, h1⟩] with p hp
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  exact ⟨c, by rw [hc ⟨f, h1⟩, hp]⟩

theorem continuous_product (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) (u : WO S T) : Continuous fun p : GA D S × GA D T => of p (oi p f) u := by
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul hψ hS hT hf h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

end GlobalTheory.WeilProduct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO

variable {D : D7}

theorem isHeckeChar_pow {η : (AE D)ˣ →* Circle} (h : IsHeckeChar D η) (n : ℕ) : IsHeckeChar D (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEta_pow {η : (AE D)ˣ →* Circle} (h : ResEta D η 1) (n : ℕ) : ResEta D (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem mem_GfC_of_supp {a : AE D} (ha : infPart D a = 0) {V : HSp D} {g : GA D V}
    (hg : ∀ i j, a * (mt V g - 1) i j = (mt V g - 1) i j) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfC_of_suppAt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfC_of_supp (h2 ▸ infPart_placeIdem h1) hg

theorem exists_weilDatum_etaTilde : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∃ om, IsWeilDatumO ψ S T (η ^ S.rank) (η ^ T.rank) om ∧ (∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε) ∧ VacCharPlus ψ θ S T om := by
  intro D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨of, hf⟩ := exists_isFinWeil D ψ hψ S T ΛS ΛT hS hT _ _ (isHeckeChar_pow hη.1 S.rank)
    (isHeckeChar_pow hη.1 T.rank) (resEta_pow hη.2.2.1 _) (resEta_pow hη.2.2.1 _)
  obtain ⟨oi, hi⟩ := GlobalTheory.RealWeil.exists_isInfWeil D ψ hψ θ hθ S T
  have hcomm := fun p q f h1 => fin_inf_comm hψ hS hT hf hi p q (f := f) h1
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T)
    ({ toFun := fun p => (of p * oi p).restrict fun f h1 => hf.pres p _ (hi.pres p f h1)
       map_one' := LinearMap.ext fun f => Subtype.ext (by
         show of 1 (oi 1 f) = f
         rw [map_one, map_one]; rfl)
       map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
         show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q f)))
         rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres q _ f.2)]) } :
      GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T))
  have ho : ∀ p f, IsThetaFunO ψ S T f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  have hfin : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = of (g, h) f := fun g hg h hh f h1 => by
    rw [ho _ f h1, hi.triv g hg h hh f h1]
  have hinf : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = oi (g, h) f :=
    fun g hg h hh f h1 => by rw [ho _ f h1, hf.triv g hg h hh _ (hi.pres _ f h1)]
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨om, ⟨hψ, isHeckeChar_pow hη.1 _, isHeckeChar_pow hη.1 _, resEta_pow hη.2.2.1 _, resEta_pow hη.2.2.1 _, hp,
    fun g h u f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 u => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩, fun v ε hv g h hg hh hst f h1 hfix => ?_,
    fun sS sT cS cT g hg h hh kS kT f h1 hv => ?_⟩
  · obtain ⟨a, ha, b, hb, k, hk, l, hl, e, -⟩ := exists_parts (g, h)
    obtain ⟨rfl, rfl⟩ : g = a * k ∧ h = b * l := Prod.ext_iff.1 e
    rw [actO_mul, e, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfin k hk l hl _ (hth u f h1),
      hf.Heisenberg₂ k hk l hl u f h1, hfin k hk l hl f h1, hinf a ha b hb _ (hth _ _ (hf.pres _ f h1)),
      hi.Heisenberg₂ a ha b hb _ _ (hf.pres _ f h1), hinf a ha b hb _ (hf.pres _ f h1)]
  · rw [show ((γ, γ') : GA D S × GA D T) = (γ, 1) * (1, γ') by simp, map_mul, Module.End.mul_apply,
      ho _ _ (hp _ f h1), GlobalTheory.T.thetaDistribution_automorphy_source_group D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ hγ _ (hp _ f h1), ho _ f h1]
    exact GlobalTheory.T.thetaDistribution_invariant_rationalTarget D ψ hψ S T θ hθ ΛS ΛT hS hT η hη of oi hf hi γ' hγ' f h1
  · simp only [ho _ f h1]
    exact continuous_product hψ hS hT hf hi h1 u
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [hfin g (mem_GfC_of_suppAt he hg) h (mem_GfC_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1
  · rw [hfin g (mem_GfC_of_supp (infPart_placeIdem hv.1) hg) h (mem_GfC_of_supp (infPart_placeIdem hv.1) hh) f h1]
    exact hf.inert v ε hv g h hg hh hst f h1 hfix
  · rw [hinf g hg h hh f h1]
    exact hi.vac sS sT cS cT g hg h hh kS kT f h1 hv

end GlobalTheory.WeilProduct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTildeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∃ om, IsWeilDatumO ψ S T (η ^ S.rank) (η ^ T.rank) om ∧ (∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε) ∧ VacCharPlus ψ θ S T om := by
  first | exact @GlobalTheory.WeilProduct.exists_weilDatum_etaTilde | exact GlobalTheory.WeilProduct.exists_weilDatum_etaTilde | (intros; apply GlobalTheory.WeilProduct.exists_weilDatum_etaTilde <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

def pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y =>
    ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem actPull_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] {Λ : Type} [Ring Λ]
    (ρ : RingAct G Λ) (a : Λ) :
    ((actPull f ρ).act a).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ρ.act a).left :=
  pullback.lift_fst _ _ _

variable {p : ℕ} {R : Type} [CommRing R] {I : Ideal R} {O : Type} [CommRing O]

theorem isAdicColimit_of_isNilpotent {f : R →+* O} (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) :
    IsAdicColimit I (Over.mk ((specO O S).hom ≫ spMap f)) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hS
  have e : (specO O S).hom ≫ spMap f = Spec.map (CommRingCat.ofHom ((algebraMap O S).comp f)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  rw [e]
  refine isAdicColimit_of_pow I _ (n * m) fun a ha => ?_
  have h₁ : (I ^ n).map f ≤ Ideal.span {(p : O)} := Ideal.map_le_iff_le_comap.2 hn
  have h₂ : f a ∈ Ideal.span {(p : O) ^ m} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono h₁ m ?_
    rw [← Ideal.map_pow, ← pow_mul]
    exact Ideal.mem_map_of_mem f ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h₂
  rw [RingHom.comp_apply, ← hc, map_mul, map_pow, map_natCast, hm, mul_zero]

variable [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} [Algebra O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

theorem spMap_comp_algebraMap (f : R →+* O) :
    spMap ((algebraMap O C).comp f) = spMap (algebraMap O C) ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

def ofCompletion (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (ιG : RingAct G Λ)
    {E : SplitExt (Sp R)} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] (d : E.GtDatum H) (ρ : RingAct H Λ)
    (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)))
    (hnat : ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x)
    (hlin : ∀ T hT (x : T ⟶ H) (a : Λ), J T hT (x ≫ ρ.act a) = J T hT x ≫ ιG.act a)
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) : Point p v O Λ where
  integers := hv
  eps := ε
  A := A'
  oA := oA'
  G := (Over.pullback (spMap f)).obj G
  semi := IsSemiAbelian.pullback _ G hG
  gen := pullback.lift j (A'.A.hom ≫ spMap (algebraMap O C))
    (by rw [hj.1.w, spMap_comp_algebraMap, Category.assoc])
  gen_pull := (isGrpPullback_pullback G (spMap f)).cancel
    (hj.congr (spMap_comp_algebraMap f) (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  oG := actPull (spMap f) ιG
  gen_act a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hact, Category.assoc, actPull_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.lift_snd, Over.w_assoc, Category.assoc]
      exact ((congrArg (_ ≫ ·) (Over.w ((actPull (spMap f) ιG).act a))).trans (pullback.lift_snd _ _ _)).symm
  Ext := GtBaseChange.extBC (spMap f) E
  Gt := (Over.pullback (spMap f)).obj H
  D := (GtBaseChange.isGt_extBC (spMap f) E H d).some
  oGt := actPull (spMap f) ρ
  cmp S _ _ hS := (pushEquiv (isGrpPullback_pullback H (spMap f)) _).trans
    ((J _ (isAdicColimit_of_isNilpotent hf S hS)).trans (pushEquiv (isGrpPullback_pullback G (spMap f)) _).symm)
  cmp_nat S S' _ _ _ _ hS hS' φ x := by
    let k : Over.mk ((specO O S').hom ≫ spMap f) ⟶ Over.mk ((specO O S).hom ≫ spMap f) :=
      Over.homMk (ptMap φ).left (Over.w_assoc (ptMap φ) _)
    have e : ∀ {X : Over (Sp R)} [GrpObj X] (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (ptMap φ ≫ y) =
          k ≫ pushEquiv (isGrpPullback_pullback X (spMap f)) _ y := fun y =>
      Over.OverMorphism.ext (Category.assoc _ _ _)
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hnat]
  cmp_act S _ _ hS a x := by
    have e : ∀ {X : Over (Sp R)} [GrpObj X] [IsCommMonObj X] (α : RingAct X Λ)
        (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (y ≫ (actPull (spMap f) α).act a) =
          pushEquiv (isGrpPullback_pullback X (spMap f)) _ y ≫ α.act a := fun α y =>
      Over.OverMorphism.ext ((Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) (actPull_fst _ α a)).trans (Category.assoc _ _ _).symm))
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hlin]

section Unif

variable [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_comparison : ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H)
    (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T) (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G))),
    (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ T hT w x, J T hT w = x ↔ FormalPoint.IsPointOf U (Φ T w) x) ∧
      ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hL (Φ := Φ) hΦ
  exact ⟨H, inferInstance, inferInstance, Φ, J, hH, hΦ, hJ, fun T T' hT hT' k x =>
    (hJ _ hT' _ _).2 (((hJ _ hT x _).1 rfl).pull k (hΦ.1 _ _ k _))⟩

theorem exists_point_of_unif (hG : IsSemiAbelian G) [Module Λ D.toPre.X] {ιD : D.OAct Λ} {ιA : A.OAct Λ}
    {ιG : RingAct G Λ} (hO : U.OLinear Λ ιD ιA ιG) (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) :
    ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T)
      (ρ : RingAct H Λ) (P : Point p v O Λ),
      (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ (a : Λ) T (x : T ⟶ H), FormalPoint.IsSmulPt ιD a (Φ T x) (Φ T (x ≫ ρ.act a))) ∧
      P.eps = ε ∧ P.A = A' ∧ HEq P.oA oA' ∧ P.G = (Over.pullback (spMap f)).obj G ∧
      P.Ext = GtBaseChange.extBC (spMap f) (splitExt D.toPre) ∧ P.Gt = (Over.pullback (spMap f)).obj H ∧
      ∃ (πG : P.G.left ⟶ G.left) (πH : P.Gt.left ⟶ H.left) (hπG : IsGrpPullback P.G G (spMap f) πG)
        (hπH : IsGrpPullback P.Gt H (spMap f) πH),
        HEq πG (pullback.fst G.hom (spMap f)) ∧ HEq πH (pullback.fst H.hom (spMap f)) ∧
        HEq (P.gen ≫ πG) j ∧
        (∀ a, (P.oG.act a).left ≫ πG = πG ≫ (ιG.act a).left) ∧
        (∀ a, (P.oGt.act a).left ≫ πH = πH ≫ (ρ.act a).left) ∧
        ∀ (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) (x : specO O S ⟶ P.Gt),
          FormalPoint.IsPointOf U (Φ _ (pushPt hπH.1.w x)) (pushPt hπG.1.w (P.cmp S hS x)) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, Φ, J, ⟨d⟩, hΦ, hJ, hnat⟩ := exists_comparison U
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL ιD (Φ := Φ) hΦ
  refine ⟨H, inferInstance, inferInstance, Φ, ρ, ofCompletion hv ε f hf hG ιG d ρ J hnat
      (fun T hT x a => (hJ _ hT _ _).2 (((hJ _ hT x _).1 rfl).smul hL hO a (hρ a _ _))) A' oA' j hj hact,
    ⟨d⟩, hΦ, hρ, rfl, rfl, HEq.rfl, rfl, rfl, rfl, _, _, isGrpPullback_pullback G _, isGrpPullback_pullback H _,
    HEq.rfl, HEq.rfl, heq_of_eq (pullback.lift_fst _ _ _), actPull_fst _ ιG, actPull_fst _ ρ, fun S _ _ hS x => ?_⟩
  exact (hJ _ (isAdicColimit_of_isNilpotent hf S hS) _ _).1
    ((pushEquiv (isGrpPullback_pullback G (spMap f)) _).apply_symm_apply _).symm

end Unif

end GlobalTheory.HTLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift.HermitianFrameExistence

open Matrix
open scoped ComplexOrder

theorem map_star_trip {m k l o : Type} [Fintype k] [Fintype l] (X : Matrix k m ℂ) (Y : Matrix k l ℂ)
    (Z : Matrix l o ℂ) : (Xᵀ * Y * Z.map star).map star = Xᴴ * Y.map star * Z := by
  have h : ∀ {a b : Type} (W : Matrix a b ℂ), W.map star = W.map (starRingEnd ℂ) := fun _ => rfl
  rw [h (Xᵀ * Y * Z.map star), Matrix.map_mul, Matrix.map_mul]
  simp [Matrix.conjTranspose, Matrix.map_map, Function.comp_def]

theorem quad {n ι : Type} [Fintype n] [Fintype ι] (G : Matrix n n ℂ) (B : Matrix n ι ℂ) (w : ι → ℂ) :
    star (B *ᵥ w) ⬝ᵥ G *ᵥ (B *ᵥ w) = star w ⬝ᵥ (Bᴴ * G * B) *ᵥ w := by
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

theorem val_inl {p q : ℕ} (u : Fin p → ℂ) :
    star (Sum.elim u (0 : Fin q → ℂ)) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim u 0 = star u ⬝ᵥ u := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]

theorem val_inr {p q : ℕ} (v : Fin q → ℂ) :
    star (Sum.elim (0 : Fin p → ℂ) v) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim 0 v = -(star v ⬝ᵥ v) := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, neg_mulVec, Finset.sum_neg_distrib]

theorem inertia {n p q r s : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hB : Bᴴ * G * B = fromBlocks 1 0 0 (-1))
    (hA : Aᴴ * G * A = fromBlocks 1 0 0 (-1)) : p + s ≤ n := by
  have key : ∀ (u : Fin p → ℂ) (v : Fin s → ℂ), B *ᵥ Sum.elim u 0 = A *ᵥ Sum.elim 0 v → u = 0 ∧ v = 0 := by
    intro u v h
    have h1 := quad G B (Sum.elim u 0)
    have h2 := quad G A (Sum.elim 0 v)
    rw [hB, val_inl] at h1
    rw [hA, val_inr, ← h, h1] at h2
    have hu := dotProduct_star_self_nonneg u
    have hv := dotProduct_star_self_nonneg v
    have h3 : star u ⬝ᵥ u = 0 := le_antisymm (by rw [h2]; exact neg_nonpos.2 hv) hu
    have h4 : star v ⬝ᵥ v = 0 := by rw [h3] at h2; exact neg_eq_zero.1 h2.symm
    exact ⟨dotProduct_star_self_eq_zero.1 h3, dotProduct_star_self_eq_zero.1 h4⟩
  let f : (Fin p → ℂ) × (Fin s → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    B.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inl ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _)) -
      A.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inr ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _))
  have e1 : ∀ u : Fin p → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm (u, 0) = Sum.elim u 0 := by
    intro u; ext (i | i) <;> simp
  have e2 : ∀ v : Fin s → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm ((0 : Fin r → ℂ), v) = Sum.elim (0 : Fin r → ℂ) v := by
    intro v; ext (i | i) <;> simp
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ huv
    have h0 : B *ᵥ Sum.elim u 0 - A *ᵥ Sum.elim 0 v = 0 := by
      simpa [f, e1, e2, Matrix.mulVecLin_apply] using huv
    obtain ⟨hu, hv⟩ := key u v (sub_eq_zero.1 h0)
    simp [hu, hv]
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod] using this

theorem card_le_of_mul_eq_one {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] (X : Matrix m k ℂ)
    (Y : Matrix k m ℂ) (h : X * Y = 1) : Fintype.card m ≤ Fintype.card k := by
  have hi : Function.Injective Y.mulVecLin := by
    intro u v huv
    have := congrArg (fun w => X *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, mulVec_mulVec, h] using this
  simpa using LinearMap.finrank_le_finrank_of_injective hi

theorem star_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v y : Fin n → ℂ) :
    star (v ⬝ᵥ M *ᵥ star y) = star v ⬝ᵥ M.map star *ᵥ y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum, mul_comm, mul_left_comm]

end GlobalTheory.RealLift.HermitianFrameExistence

namespace GlobalTheory.RealLift

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frameEx_holds : FrameEx := by
  intro n r s M θ hSig hC
  obtain ⟨hrs, A0, hA0⟩ := hSig
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  have hA : A0ᴴ * G * A0 = fromBlocks 1 0 0 (-1) := by
    rw [← map_star_trip, hA0, hJ]

  obtain ⟨L, hLdef⟩ : ∃ L : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ,
      L = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G) := ⟨_, rfl⟩
  have hL : L * A0 = 1 := by
    calc L * A0 = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G * A0) := by
          rw [hLdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, fromBlocks_multiply]; simp
  have e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hR : A0 * L = 1 := (mul_eq_one_comm_of_equiv e).1 hL
  have hLc : Lᴴ * A0ᴴ = 1 := by rw [← conjTranspose_mul, hR, conjTranspose_one]
  have hJh : ((fromBlocks 1 0 0 (-1)) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)ᴴ = fromBlocks 1 0 0 (-1) := by
    simp [fromBlocks_conjTranspose]
  have hA' : A0ᴴ * Gᴴ * A0 = A0ᴴ * G * A0 := by
    calc A0ᴴ * Gᴴ * A0 = (A0ᴴ * G * A0)ᴴ := by simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hA, hJh]
  have Gherm : Gᴴ = G := by
    calc Gᴴ = (Lᴴ * A0ᴴ) * Gᴴ * (A0 * L) := by rw [hLc, hR]; simp
      _ = Lᴴ * (A0ᴴ * Gᴴ * A0) * L := by simp only [Matrix.mul_assoc]
      _ = Lᴴ * (A0ᴴ * G * A0) * L := by rw [hA']
      _ = (Lᴴ * A0ᴴ) * G * (A0 * L) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hLc, hR]; simp

  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  have i1 := inertia G B A0 h3 hA
  have i2 := inertia G A0 B hA h3
  have i3 := card_le_of_mul_eq_one B B' h1
  simp only [Fintype.card_fin, Fintype.card_sum] at i3
  obtain rfl : p = r := by omega
  obtain rfl : q = s := by omega
  refine ⟨B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.RealLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanEigen_orthonormalFrame_exists : GlobalTheory.RealLift.FrameEx := by
  first | exact @GlobalTheory.RealLift.frameEx_holds | exact GlobalTheory.RealLift.frameEx_holds | (intros; apply GlobalTheory.RealLift.frameEx_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
noncomputable section

namespace GlobalTheory.ChrWSmooth

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_chrW {χ : Chr F E} (hχ : Continuous χ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    Continuous (chrW χ t) := by
  have hm : Continuous (Units.map (complMap (splitPrime_under t)).toMonoidHom) :=
    Units.continuous_map (GlobalTheory.LFun.SplitChart.continuous_complMap (splitPrime_under t))
  have h1 : Continuous fun x : (Fv F v)ˣ => ((chrW χ t x : ℂˣ) : ℂ) :=
    (continuous_locChar hχ (splitPrime t)).comp hm
  have h2 : Continuous fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ) := by
    have : (fun x : (Fv F v)ˣ => (((chrW χ t x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((chrW χ t x⁻¹ : ℂˣ) : ℂ) := by
      funext x; rw [map_inv]
    rw [this]
    exact h1.comp continuous_inv
  exact Units.continuous_iff.2 ⟨h1, h2⟩

theorem isUnitaryChar_chrW (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    GlobalTheory.SmGL.IsUnitaryChar (chrW χ t) := fun g => by
  show ‖((Circle.toUnits _ : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem chrW_nu_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t) ∧ GlobalTheory.SmGL.IsUnitaryChar (chrW X.ν t) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT v _ t
  have hν : Continuous X.ν := by
    show Continuous fun x => X.α x / X.β x
    exact hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  exact ⟨GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (continuous_chrW hν t), isUnitaryChar_chrW _ t⟩

end GlobalTheory.ChrWSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitaryStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t) ∧ GlobalTheory.SmGL.IsUnitaryChar (chrW X.ν t) := by
  first | exact @GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary | exact GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary | (intros; apply GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.RealScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ext_realAd (r : ℝ) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F r)) = (r : ℂ) := by
  set y : mixedEmbedding.mixedSpace F := algebraMap ℝ _ r with hy
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y with ha
  have hev : evInf F w (realAd F r) = a w := rfl
  have hay : InfiniteAdeleRing.ringEquiv_mixedSpace F a = y := by rw [ha]; exact RingEquiv.apply_symm_apply _ _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hay
  rw [hev]
  rcases w.isReal_or_isComplex with hw | hw
  · have h1 := congrFun (congrArg Prod.fst hay) ⟨w, hw⟩
    simp only [hy] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [show (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w)) = r from by simpa using h1]
  · have h1 := congrFun (congrArg Prod.snd hay) ⟨w, hw⟩
    simpa [hy] using h1

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (x : AF F) :
    piInf τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) x) = InfinitePlace.Completion.extensionEmbedding w (evInf F w x) := by
  change infEmb τ (compInf F E w (x ⊗ₜ[F] (1 : E))) = _
  rw [compInf]
  change infEmb τ ((evInf F w x) ⊗ₜ[F] ((AlgHom.id F E) 1)) = _
  rw [infEmb_tmul]
  simp

theorem piInf_realAd_smul {w : InfinitePlace F} (τ : EmbOver E w) (r : ℝ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ (realAd F r • z) = (r : ℂ) * piInf τ z := by
  rw [Algebra.smul_def, map_mul, piInf_algebraMap, ext_realAd]

theorem realAd_smul_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  intro F E _ _ _ _ _ σ α β τ _ u r w
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact piInf_realAd_smul (τ w) r (u i j)

end GlobalTheory.RealScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlaceStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  first | exact @GlobalTheory.RealScalar.realAd_smul_map | exact GlobalTheory.RealScalar.realAd_smul_map | (intros; apply GlobalTheory.RealScalar.realAd_smul_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def IsActPull {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] (i' : OAct O G') (i : OAct O G)
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  IsGrpPullback G' G f φ ∧ ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left

def IsCover (k : Type) [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)] (π : C' ⟶ C) : Prop :=
  IsFinite π ∧ Surjective π ∧ π ≫ strHom k C = strHom k C'

def IsRosati (c : O →+* O) {S : Scheme.{0}} (P : Out.PolAV S) (j : OAct O P.A) : Prop :=
  ∀ a, Out.RosatiAdj P.A P.L (j.act a) (j.act (c a))

def PolPart (c : O →+* O) {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (T : TorusExtension G) (P : Out.PolAV (Sp K)) (e : T.B ≅ P.A) (j : OAct O P.A),
    IsMonHom (T.q ≫ e.hom) ∧ (∀ a, i.act a ≫ T.q ≫ e.hom = (T.q ≫ e.hom) ≫ j.act a) ∧ IsRosati c P j

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

def geomGenPt (C : Scheme.{0}) [IsIntegral C] : Sp (AlgebraicClosure C.functionField) ⟶ C :=
  spMap (algebraMap C.functionField (AlgebraicClosure C.functionField)) ≫ genPt C

def PolGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (G' : Over (Sp (AlgebraicClosure C.functionField))) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left),
    IsActPull i' i (geomGenPt C) φ ∧ PolPart c i'

def AbGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (P : Out.PolAV (Sp C.functionField)) (j : OAct O P.A) (φ : P.A.left ⟶ G.left),
    IsActPull j i (genPt C) φ ∧ IsRosati c P j

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Defs

def Splits (O k : Type) [CommRing O] [Field k] : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (τ : κ → (O →+* k)), IsSplitBy τ

section Lemmas

variable {O : Type} [CommRing O]

theorem IsActPull.comp {S S' S'' : Scheme.{0}} {G'' : Over S''} [GrpObj G''] {G' : Over S'} [GrpObj G'] {G : Over S}
    [GrpObj G] {i'' : OAct O G''} {i' : OAct O G'} {i : OAct O G} {g : S'' ⟶ S'} {f : S' ⟶ S} {φ' : G''.left ⟶ G'.left}
    {φ : G'.left ⟶ G.left} (h' : IsActPull i'' i' g φ') (h : IsActPull i' i f φ) : IsActPull i'' i (g ≫ f) (φ' ≫ φ) :=
  ⟨h'.1.comp h.1, fun a => by rw [← Category.assoc, h'.2, Category.assoc, h.2, Category.assoc]⟩

end Lemmas

end GlobalTheory.CurveRootGeometry
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.KFinLoc

theorem split_or_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl (F := F), Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  intro F E _ _ _ _ _ σ B hB v
  have hUn := hB.unram
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun w _ => ?_
    exact Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | hi
  · left
    obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact ⟨(GlobalTheory.AdelicU.existsUnique_splitPrime_eq hB.cm hne h1 h2).exists.choose⟩
  · exact Or.inr hi

end GlobalTheory.KFinLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInertStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.place_split_or_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl (F := F), Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  first | exact @GlobalTheory.KFinLoc.split_or_inert | exact GlobalTheory.KFinLoc.split_or_inert | (intros; apply GlobalTheory.KFinLoc.split_or_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacLn

def trPair (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

theorem trPair_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    trPair F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def coord {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} (d : Darboux B κ) (w : W) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F ((d.e w).1 i), fun i => evI F ((d.e w).2 i))

end GlobalTheory.VacLn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RallisBottom

open GlobalTheory.Core.Rk.IP

variable {D : D7}

def HeckeFormAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

end GlobalTheory.RallisBottom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.RealLift.Dbl

def dblCol {β : Type} {R S : ℕ} (C : Matrix β (Ix R S) ℂ) : Ix (R + S) (S + R) → β ⊕ β → ℂ
  | .inl p => Sum.elim (fun r => Sum.elim (fun i => C i (.inl r)) (0 : β → ℂ))
      (fun s => Sum.elim (0 : β → ℂ) (fun i => C i (.inr s))) (finSumFinEquiv.symm p)
  | .inr q => Sum.elim (fun s => Sum.elim (fun i => C i (.inr s)) (0 : β → ℂ))
      (fun r => Sum.elim (0 : β → ℂ) (fun i => C i (.inl r))) (finSumFinEquiv.symm q)

def dblM {β : Type} {R S : ℕ} (C : Matrix β (Ix R S) ℂ) : Matrix (β ⊕ β) (Ix (R + S) (S + R)) ℂ :=
  Matrix.of fun i j => dblCol C j i

end GlobalTheory.RealLift.Dbl

end
end
