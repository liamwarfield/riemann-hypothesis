module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsPullOfMoveInv
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevPullModel

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LevPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_isLift : ∃ lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La, IsLift lift := by
  have := Dw.proj
  choose lift h using fun γ : Gam Dw l =>
    Module.projective_lifting_property (Submodule.mkQ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
      (γ.toLinearMap ∘ₗ Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨lift, h⟩

theorem lift_mk {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ : Gam Dw l) (a : Dw.La) :
    (Submodule.Quotient.mk (lift γ a) : LaQ Dw l) = γ (Submodule.Quotient.mk a) := LinearMap.congr_fun (h γ) a

end GlobalTheory.LevPullModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedBlockSelfApply
noncomputable section

namespace GlobalTheory.LevelSpanCompare

section Move

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem reflects_half_of_move {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : IsLevMove ρ ν gM gA) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (b : KA l →+* k)
    (hx : x ≫ Xo.s = spMap b) (a : Dw.La) (ha : gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨hs, hM, -⟩ := h
  obtain ⟨-, J, -, -, hJM⟩ := Xo.univ.geom k (x ≫ ρ) b (by rw [Category.assoc, hs]; exact hx)
  have h1 : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime]; simp
  rw [Submodule.sup_smul] at h1
  obtain ⟨b, hb, a', ha', rfl⟩ := Submodule.mem_sup.1 h1
  have hgb : gM b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.mem_map_of_mem (f := gM) hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hga : gM a' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.sub_mem _ ha hgb
    simpa using this
  have e1 : ρ ≫ (Xo.univ.eta a').left = ρ ≫ (Xo.univ.eta 0).left := by
    rw [← hM a', ← hM 0, Xo.univ.eta_ker _ hga, Xo.univ.eta_ker (gM 0) (by simp)]
  have e5 : J.ev l.M a' = J.ev l.M 0 := by
    rw [← hJM _ ha', ← hJM _ (Submodule.zero_mem _)]
    ext
    simpa using congrArg (x ≫ ·) e1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have e6 : J.ev l.M 0 = 1 := (J.ker l.M hM0 0).2 ⟨0, by simp⟩
  obtain ⟨b', hb'⟩ := (J.ker l.M hM0 a').1 (e5.trans e6)
  refine Submodule.add_mem _ hb ?_
  rw [hb', ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (GlobalTheory.LevelGroupTest.natCast_mem_half l) trivial

theorem levR_unique (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (gM : Dw.La →ₗ[𝓞 E] Dw.La)
    {S : Type} [CommRing S] [Algebra c.F S] [Nontrivial S] {y y' y'' : FrPt Xo c S}
    (h' : levR (gM, LinearMap.id) y y') (h'' : levR (gM, LinearMap.id) y y'') : y' = y'' := by
  obtain ⟨ρ, ν, i, h, hm⟩ := h'
  obtain ⟨ρ', ν', i', g, gm⟩ := h''
  obtain ⟨m, hmax⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let φ : S →+* AlgebraicClosure (S ⧸ m) := (algebraMap (S ⧸ m) _).comp (Ideal.Quotient.mk m)
  have hinj := reflects_half_of_move h (AlgebraicClosure (S ⧸ m)) (spMap φ ≫ y.x)
    (φ.comp ((algebraMap c.F S).comp (IntermediateField.inclusion c.le).toRingHom)) (by
      rw [Category.assoc, y.x_over]
      unfold sOf spMap
      rw [← Spec.map_comp]; rfl)
  obtain ⟨rfl, e⟩ := GlobalTheory.T.levelMove_moduli_unique_universalTriple E H Dw l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h g
    (GlobalTheory.exists_sim_of_aut_mod E H Dw l l.A gM hpq l.A_pos hA hinj)
  exact (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν' e.symm hm gm

end Move

section Idem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GoodLatCompare

end Idem

section Framed

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Framed

section Swap

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Swap

section Half

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Lev Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

end Half

end GlobalTheory.LevelSpanCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConst
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevDegree

theorem card_lifts_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; ∀ y y' : FrPt Xo c (CAt σ₂), Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y'} := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ _ y y'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hpq : Dw.p ≠ Dw.q ∧ 1 ≤ Dw.p + Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hk : ∀ a : c.F, algebraMap d.c₂.F (CAt σ₂) (d.eF a) = algebraMap c.F (CAt σ₂) a := fun _ => rfl
  obtain ⟨lift, hlift⟩ := GlobalTheory.LevPullModel.exists_isLift (Dw := Dw) (l := d.l₂)
  have hov : ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom :=
    GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hA d
  have L := GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw d.l₂ d.Xo₂ d.c₂ (Gam Dw d.l₂) lift hpq.2 hA₂
    (fun a => (Submodule.Quotient.eq _).1 ((GlobalTheory.LevPullModel.lift_mk hlift 1 a).trans rfl))
    (fun g h a => (Submodule.Quotient.eq _).1 (by
      rw [GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift]; rfl))
  have key : ∀ y : FrPt Xo c (CAt σ₂),
      Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} =
        Nat.card {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} := by
    intro y
    obtain ⟨y₀, hy₀⟩ := hd.2.2.2.2.2.2.1 (CAt σ₂) hk y
    have T := GlobalTheory.T.levelCover_fibre_torsor_trivial_level_changes D.host.E H Dw l Xo c d hpq.2 hd hA₂ hov lift hlift (CAt σ₂) hk y₀
    have hA₂' : d.l₂.A.Coprime d.l₂.M := by rw [hA₂]; exact Nat.coprime_one_left _
    have hex : ∀ γ : Gam Dw d.l₂, ∃ y₂', levR (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La)) y₀ y₂' :=
      fun γ => L.total γ (CAt σ₂) y₀
    choose g hg using hex
    let f : {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} →
        {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} :=
      fun γ => ⟨g γ.1, ((T (g γ.1) y hy₀).1).2 ⟨γ.1, γ.2, hg γ.1⟩⟩
    refine (Nat.card_eq_of_bijective f ⟨fun γ γ' e => Subtype.ext ?_, fun z => ?_⟩).symm
    · have e' : g γ.1 = g γ'.1 := congrArg Subtype.val e
      exact (T (g γ.1) y hy₀).2 γ.1 γ'.1 (hg γ.1) (e' ▸ hg γ'.1)
    · obtain ⟨γ, hγ, hl⟩ := ((T z.1 y hy₀).1).1 z.2
      exact ⟨⟨γ, hγ⟩, Subtype.ext (GlobalTheory.LevelSpanCompare.levR_unique hpq.2 hA₂' (lift γ) (hg γ) hl)⟩
  exact (key y).trans (key y').symm

end GlobalTheory.LevDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConstStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_framed_lifts_levelCover_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; ∀ y y' : FrPt Xo c (CAt σ₂), Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y'} := by
  first | exact @GlobalTheory.LevDegree.card_lifts_const | exact GlobalTheory.LevDegree.card_lifts_const | (intros; apply GlobalTheory.LevDegree.card_lifts_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFramedLiftsEquivMovedGroupCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFramedLiftsEquivMovedGroupCosets
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

section Group

theorem nonempty_equiv_sigma_quotient {T K G : Type*} [Group G] (Hs : K → Subgroup G) (P : T → K → G → Prop)
    (ex : ∀ y, ∃ k g, P y k g) (w₁ : ∀ y k k' g g', P y k g → P y k' g' → k = k')
    (w₂ : ∀ y k g g', P y k g → P y k g' → g⁻¹ * g' ∈ Hs k)
    (inj : ∀ y y' k g g', P y k g → P y' k g' → g⁻¹ * g' ∈ Hs k → y = y')
    (surj : ∀ k g, ∃ y, P y k g) : Nonempty (T ≃ Σ k, G ⧸ Hs k) := by
  choose kk gg hP using ex
  have val : ∀ y k g, P y k g → (⟨kk y, (gg y : G ⧸ Hs (kk y))⟩ : Σ k, G ⧸ Hs k) = ⟨k, (g : G ⧸ Hs k)⟩ := by
    intro y k g h
    obtain rfl := w₁ y _ _ _ _ (hP y) h
    exact congrArg _ (QuotientGroup.eq.2 (w₂ y _ _ _ (hP y) h))
  refine ⟨Equiv.ofBijective (fun y => ⟨kk y, (gg y : G ⧸ Hs (kk y))⟩) ⟨fun y y' e => ?_, ?_⟩⟩
  · have key : ∀ k (g : G), P y' k g → (⟨kk y, (gg y : G ⧸ Hs (kk y))⟩ : Σ k, G ⧸ Hs k) = ⟨k, (g : G ⧸ Hs k)⟩ → y = y' := by
      intro k g h e'
      obtain ⟨rfl, e₂⟩ := Sigma.mk.inj_iff.1 e'
      exact inj _ _ _ _ _ (hP y) h (QuotientGroup.eq.1 (eq_of_heq e₂))
    exact key _ _ (hP y') e
  · rintro ⟨k, q⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨y, hy⟩ := surj k g
      exact ⟨y, val y k g hy⟩

end Group

section Frames

open ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_moved {X₂ X : Data E r} (hΨ : X₂.Ψ = X.Ψ) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) :
    ∃ x', Moved X₂ X δ x x' :=
  ⟨fun τ => ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, by rw [hΨ]; exact τ.2⟩ : Matrix (Fin r) (Fin r) ℂ),
    fun _ _ _ => rfl⟩

omit [NumberField E] [IsCMField E] in
theorem map_mul_map_inv (τ : E →+* ℂ) (δ : GL (Fin r) E) :
    (δ : Matrix (Fin r) (Fin r) E).map τ * ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero τ) (map_one τ)

omit [NumberField E] [IsCMField E] in
theorem map_inv_mul_map (τ : E →+* ℂ) (δ : GL (Fin r) E) :
    ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * (δ : Matrix (Fin r) (Fin r) E).map τ = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero τ) (map_one τ)

theorem exists_moved_back {X₂ X : Data E r} (hΨ : X₂.Ψ = X.Ψ) (δ : GL (Fin r) E) (x' : Frame X.Ψ r) :
    ∃ x, Moved X₂ X δ x x' :=
  ⟨fun τ => (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x' ⟨τ.1, hΨ ▸ τ.2⟩ : Matrix (Fin r) (Fin r) ℂ),
    fun τ _ h₁ => by
      show mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ *
        (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat x' ⟨τ, h₁⟩)
      rw [← Matrix.mul_assoc, map_mul_map_inv, Matrix.one_mul]⟩

theorem mem_dom_of_moved {X₂ X : Data E r} (δ : GL (Fin r) E) (hp : X₂.p0 = X.p0) (hΨ : X₂.Ψ = X.Ψ) (hG : X₂.Gm = X.Gm)
    (hiso : ∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) =
      herm X₂.Gm v w)
    {x : Frame X₂.Ψ r} {x' : Frame X.Ψ r} (hm : Moved X₂ X δ x x') (hx' : x' ∈ X.dom) : x ∈ X₂.dom := by
  refine GlobalTheory.FrameDom.mem_dom_of_isometry E r X₂ X δ⁻¹ hp (fun τ => by rw [hΨ]) (fun v w => ?_) x' x hx' fun τ h₂ h₁ => ?_
  · have e : ∀ u : Fin r → E, (δ : Matrix (Fin r) (Fin r) E).mulVec
        (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec u) = u := fun u => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have h := hiso (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec v)
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec w)
    rw [e, e] at h
    rw [← h, hG]
  · rw [hm τ h₁ h₂, ← Matrix.mul_assoc, map_inv_mul_map, Matrix.one_mul]

theorem moved_iff {Ψ₂ Ψ : Finset (E →+* ℂ)} (h : Ψ₂ = Ψ) (δ g : GL (Fin r) E) {x₂ x₂' : Frame Ψ₂ r} {x₁ x₁' : Frame Ψ r}
    (m : ∀ (τ : E →+* ℂ) (h₂ : τ ∈ Ψ₂) (h₁ : τ ∈ Ψ),
      mat x₁ ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x₂ ⟨τ, h₂⟩)
    (m' : ∀ (τ : E →+* ℂ) (h₂ : τ ∈ Ψ₂) (h₁ : τ ∈ Ψ),
      mat x₁' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x₂' ⟨τ, h₂⟩) :
    (∃ b ∈ Bor Ψ₂ r, x₂' = rmul (lact g x₂) b) ↔ ∃ b ∈ Bor Ψ r, x₁' = rmul (lact (MulAut.conj δ g) x₁) b := by
  subst h
  obtain rfl : x₁ = lact δ x₂ := funext fun τ => m τ.1 τ.2 τ.2
  obtain rfl : x₁' = lact δ x₂' := funext fun τ => m' τ.1 τ.2 τ.2
  have e : lact (MulAut.conj δ g) (lact δ x₂) = lact δ (lact g x₂) := by
    rw [← lact_mul, ← lact_mul, MulAut.conj_apply, inv_mul_cancel_right]
  rw [e]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  rw [← lact_rmul δ (lact g x₂) b]
  constructor
  · exact fun h => congrArg _ h
  · intro h
    have := congrArg (lact δ⁻¹) h
    rwa [lact_inv, lact_inv] at this

theorem eq_rmul_lact (X : Data E r) {γ γ' : GL (Fin r) E} {x y b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (e : rmul (lact γ x) b = rmul (lact γ' y) b') : x = rmul (lact (γ⁻¹ * γ') y) (rmul b' (invF X b)) := by
  have h₁ : lact γ⁻¹ (rmul (lact γ x) b) = rmul x b := by rw [lact_rmul, lact_inv]
  have h₂ : lact γ⁻¹ (rmul (lact γ' y) b') = rmul (lact (γ⁻¹ * γ') y) b' := by rw [lact_rmul, ← lact_mul]
  have h₃ : rmul x b = rmul (lact (γ⁻¹ * γ') y) b' := by rw [← h₁, e, h₂]
  calc x = rmul (rmul x b) (invF X b) := by rw [rmul_assoc, rmul_invF X hb, rmul_oneF]
    _ = _ := by rw [h₃, rmul_assoc]

theorem eq_of_rmul_lact_eq (X : Data E r) {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ) {x b b' : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (e : rmul (lact γ x) b = rmul (lact γ' x) b') : γ = γ' := by
  have h := eq_rmul_lact X hb' e.symm
  have hc : rmul b (invF X b') ∈ Bor X.Ψ r := mul_mem X hb (invF_mem X hb')
  set c := rmul b (invF X b') with hcd
  have e₂ : lact (γ'⁻¹ * γ) x = rmul x (invF X c) := by
    conv_rhs => rw [h]
    rw [rmul_assoc, rmul_invF X hc, rmul_oneF]
  have h₁ := X.Γ_free _ (X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ) x hx _ (invF_mem X hc) e₂
  exact (inv_mul_eq_one.1 h₁).symm

end Frames

section Lift

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem frOver_inj (d : DeltaDat Xo c n) (hG : GlobalFnsSt) {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    {y : FrPt Xo c S} {y₂ y₂' : FrPt d.Xo₂ d.c₂ S} (h : FrOver d y₂ y) (h' : FrOver d y₂' y) (ex : y₂.x = y₂'.x) :
    y₂ = y₂' := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', R'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique hG (UnivPol.pol d.Xo₂) Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _
    hw.2 hw'.2
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y₂
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y₂'
  dsimp only at ex e e' hu hu' p p₁ p₂ R p' p₁' p₂' R'
  subst ex
  obtain rfl : u = u' := funext fun τ => funext fun i =>
    d.m.cart.1.hom_ext ((hu τ i).trans (hu' τ i).symm) ((tan τ i).1.trans (tan' τ i).1.symm)
  obtain rfl : p = p' := pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)
  obtain ⟨p'', n', q₁, q₂, hn, -⟩ := exists_pm_iso d.m e
  obtain rfl : p'' = p := pm_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
  have one : ∀ {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs r z ⊤ (1 : Γ(Y, ⊤)) = 1 := fun r z => by
    rw [gs_eq r z ⊤ (by trivial), map_one, map_one]
  have K := (rel_scal_iff Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB p₁ hn p₂ (1 : Γ(Sp S, ⊤)) R R').2 (fun Z r z j _ => by
    rw [one, _root_.one_mul])
  have K₂ := (scal_iff (fst (Over.mk x) d.Xo₂.univ.t.G).left (1 : Γ(Sp S, ⊤)) s s').2 K
  obtain rfl : s = s' := by
    cases s
    cases s'
    congr
    funext i
    have k := K₂ i
    simp only [map_one] at k
    exact (k.trans (_root_.one_mul _)).symm
  rfl

end Lift

section Core

open CategoryTheory GlobalTheory.FrameLift ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem lifts_equiv (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) {r : ℕ}
    (B : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r) (C : Unf d.Xo₂ d.c₂ σ₂ r) (hB : IsUnf B) (hC : IsUnf C)
    (π : C.Comp → B.Comp) (δ : C.Comp → GL (Fin r) E) (hGm : ∀ k₂, (C.X k₂).Gm = (B.X (π k₂)).Gm)
    (hiso : ∀ k₂ v w, herm (C.X k₂).Gm (((δ k₂) : Matrix (Fin r) (Fin r) E).mulVec v)
      (((δ k₂) : Matrix (Fin r) (Fin r) E).mulVec w) = herm (C.X k₂).Gm v w)
    (hle : ∀ k₂, (C.X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ (B.X (π k₂)).Γ)
    (hOv : ∀ k₂, Over d σ₂ B C k₂ (π k₂) (δ k₂)) (k : B.Comp) (x' : (B.X k).dom) :
    letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
    Nonempty ({y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ (B.un k x')} ≃
      Σ k₂ : {k₂ // π k₂ = k}, ↥(B.X k).Γ ⧸ (((C.X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf (B.X k).Γ)) := by
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have G₂ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw d.l₂ d.Xo₂ d.c₂ (CAt σ₂)
  have hΨ : ∀ k₂ k, (C.X k₂).Ψ = (B.X k).Ψ := fun k₂ k => Finset.ext fun τ =>
    ((hC.2.1 k₂).2 τ).trans ((hB.2.1 k).2 τ).symm
  have hp : ∀ k₂ k, (C.X k₂).p0 = (B.X k).p0 := fun k₂ k => (hC.2.1 k₂).1.trans (hB.2.1 k).1.symm
  refine nonempty_equiv_sigma_quotient _ (fun y k₂ γ => ∃ (x₂ : (C.X k₂.1).dom) (t : Ix Dw → (CAt σ₂)ˣ)
      (x₁ : Frame (B.X k).Ψ r), ∃ b ∈ Bor (B.X k).Ψ r, FrBor t (C.un k₂.1 x₂) y.1 ∧
        Moved (C.X k₂.1) (B.X k) (δ k₂.1) x₂.1 x₁ ∧ x'.1 = rmul (lact γ.1 x₁) b) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨y₂, hy⟩
    obtain ⟨k₂, x₂, t, ht⟩ := hC.2.2.1 y₂
    obtain ⟨x₁, hm⟩ := exists_moved (hΨ k₂ (π k₂)) (δ k₂) x₂.1
    obtain ⟨hx₁, s, -, y₀, hb₀, ho⟩ := hOv k₂ x₂.1 x₂.2 x₁ hm
    have hb := GlobalTheory.CoverSec.frBor_down d hG ho hy ht
    have hc := G.2.1 _ _ _ _ _ hb₀ hb
    obtain ⟨γ, hγ, b, hb', e⟩ := (hB.2.2.2.1 (π k₂) k ⟨x₁, hx₁⟩ x').1 ⟨_, hc⟩
    obtain ⟨hk, e₂⟩ := Sigma.mk.inj_iff.1 e
    subst hk
    exact ⟨⟨k₂, rfl⟩, ⟨γ, hγ⟩, x₂, t, x₁, b, hb', ht, hm, eq_of_heq e₂⟩
  · rintro ⟨y₂, hy⟩ ⟨k₂, hk⟩ ⟨k₂', hk'⟩ γ γ' ⟨x₂, t, x₁, b, hb, ht, hm, e⟩ ⟨x₂', t', x₁', b', hb', ht', hm', e'⟩
    have hc := G₂.2.1 _ _ _ _ _ ht (G₂.2.2.1 _ _ _ ht')
    obtain ⟨g, hg, b₂, hb₂, e₂⟩ := (hC.2.2.2.1 k₂ k₂' x₂ x₂').1 ⟨_, hc⟩
    exact Subtype.ext (Sigma.mk.inj_iff.1 e₂).1.symm
  · rintro ⟨y₂, hy⟩ ⟨k₂, hk⟩ γ γ' ⟨x₂, t, x₁, b, hb, ht, hm, e⟩ ⟨x₂', t', x₁', b', hb', ht', hm', e'⟩
    subst hk
    have hc := G₂.2.1 _ _ _ _ _ ht (G₂.2.2.1 _ _ _ ht')
    obtain ⟨g, hg, b₂, hb₂, e₂⟩ := (hC.2.2.2.1 k₂ k₂ x₂ x₂').1 ⟨_, hc⟩
    have e₃ : x₂'.1 = rmul (lact g x₂.1) b₂ := eq_of_heq (Sigma.mk.inj_iff.1 e₂).2
    obtain ⟨b₃, hb₃, e₄⟩ := (moved_iff (hΨ k₂ (π k₂)) (δ k₂) g hm hm').1 ⟨b₂, hb₂, e₃⟩
    have hh : MulAut.conj (δ k₂) g ∈ (B.X (π k₂)).Γ := hle k₂ (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
    obtain ⟨hx₁, -⟩ := hOv k₂ x₂.1 x₂.2 x₁ hm
    have e₅ : rmul (lact γ.1 x₁) b = rmul (lact (γ'.1 * MulAut.conj (δ k₂) g) x₁) (rmul b₃ b') := by
      rw [← e, e', e₄, lact_rmul, lact_mul, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc]
    have e₆ := eq_of_rmul_lact_eq (B.X (π k₂)) γ.2 (Subgroup.mul_mem _ γ'.2 hh) hx₁ hb
      (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem _ hb₃ hb') e₅
    rw [Subgroup.mem_subgroupOf]
    have e₇ : ((γ⁻¹ * γ' : (B.X (π k₂)).Γ) : GL (Fin r) E) = (MulAut.conj (δ k₂) g)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e₆]
      group
    rw [e₇]
    exact Subgroup.inv_mem _ (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
  · rintro ⟨y₂, hy⟩ ⟨y₂', hy'⟩ ⟨k₂, hk⟩ γ γ' ⟨x₂, t, x₁, b, hb, ht, hm, e⟩ ⟨x₂', t', x₁', b', hb', ht', hm', e'⟩ hγ
    subst hk
    rw [Subgroup.mem_subgroupOf] at hγ
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1 hγ
    have hc : (γ.1)⁻¹ * γ'.1 = MulAut.conj (δ k₂) g := by
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul]
      exact hgγ.symm
    have e₁ := eq_rmul_lact (B.X (π k₂)) hb (e.symm.trans e')
    rw [hc] at e₁
    obtain ⟨b₂, hb₂, e₂⟩ := (moved_iff (hΨ k₂ (π k₂)) (δ k₂) g hm' hm).2
      ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem _ hb' (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem _ hb), e₁⟩
    obtain ⟨s, hs⟩ := (hC.2.2.2.1 k₂ k₂ x₂' x₂).2 ⟨g, hg, b₂, hb₂, by rw [e₂]⟩
    exact Subtype.ext (frOver_inj d hG hy hy' (ht.1.trans (hs.1.trans ht'.1.symm)))
  · rintro ⟨k₂, rfl⟩ ⟨γ, hγ⟩
    have hx₁ : lact γ⁻¹ x'.1 ∈ (B.X (π k₂)).dom :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ (Subgroup.inv_mem _ hγ) _).2 x'.2
    obtain ⟨x₂, hm⟩ := exists_moved_back (hΨ k₂ (π k₂)) (δ k₂) (lact γ⁻¹ x'.1)
    have hx₂ : x₂ ∈ (C.X k₂).dom := mem_dom_of_moved (δ k₂) (hp k₂ _) (hΨ k₂ _) (hGm k₂) (hiso k₂) hm hx₁
    obtain ⟨hx₁', s, -, y₀, hb₀, ho⟩ := hOv k₂ x₂ hx₂ _ hm
    have ex : x'.1 = rmul (lact γ (lact γ⁻¹ x'.1)) (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _) := by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_oneF, ← lact_mul, mul_inv_cancel, lact_one]
    obtain ⟨t₁, ht₁⟩ := (hB.2.2.2.1 _ _ ⟨_, hx₁'⟩ x').2
      ⟨γ, hγ, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF_mem _, by rw [← ex]⟩
    have hw := G.2.1 _ _ _ _ _ (G.2.2.1 _ _ _ hb₀) ht₁
    have e : ((C.un k₂ ⟨x₂, hx₂⟩).x ≫ d.r) = (B.un (π k₂) x').x := ho.1.trans hw.1.symm
    obtain ⟨y₂, hy₂x, hy₂⟩ := exists_frOver (S := CAt σ₂) d (fun _ => rfl) (B.un (π k₂) x') _ e (C.un k₂ ⟨x₂, hx₂⟩).x_over
    exact ⟨⟨y₂, hy₂⟩, ⟨x₂, hx₂⟩, _, _, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF _, ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.oneF_mem _,
      frBor_lift d hG ho hy₂ hy₂x hw, hm, ex⟩

end Core

theorem frLifts_equiv_cosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; Nonempty ({y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ≃ Σ k₂ : {k₂ // π k₂ = k}, ↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ π δ hyp k x'
  exact lifts_equiv d σ₂ (U _) (U₂ σ₂) (hL.unf _ (good_comp d σ₂ hσ₂)) (hL₂.unf σ₂ hσ₂) π δ
    (fun k₂ => (hyp k₂).1) (fun k₂ => (hyp k₂).2.1) (fun k₂ => (hyp k₂).2.2.1) (fun k₂ => (hyp k₂).2.2.2.2) k x'

end GlobalTheory.LevModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFramedLiftsEquivMovedGroupCosetsStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFramedLifts_equiv_movedGroupCosets : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; Nonempty ({y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ≃ Σ k₂ : {k₂ // π k₂ = k}, ↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
  first | exact @GlobalTheory.LevModel.frLifts_equiv_cosets | exact GlobalTheory.LevModel.frLifts_equiv_cosets | (intros; apply GlobalTheory.LevModel.frLifts_equiv_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentIndexSumEqConst
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

theorem cover_degree_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∃ N : ℕ, 0 < N ∧ ∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  classical
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  letI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hC := GlobalTheory.T.complexFramedLifts_equiv_movedGroupCosets D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  have hK := GlobalTheory.T.card_framed_lifts_levelCover_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂
  have hfin : ∀ k (k₂ : {k₂ // pr k₂ = k}), Finite (↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
    intro k k₂
    have h := (hπ k₂.1).2.2.2.1
    rw [k₂.2] at h
    exact Subgroup.index_ne_zero_iff_finite.1 h
  have hS : ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), (∑ᶠ k₂ : {k₂ // pr k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ∧ Finite {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} := by
    intro k x'
    obtain ⟨e⟩ := hC k x'
    haveI := hfin k
    refine ⟨?_, Finite.of_equiv _ e.symm⟩
    rw [Nat.card_congr e, Nat.card_sigma, finsum_eq_sum_of_fintype]
    rfl
  have hne : ∀ y : FrPt Xo c (CAt σ₂), Nonempty {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} := by
    intro y
    obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hd
    obtain ⟨y₂, hy₂⟩ := hlift (CAt σ₂) (fun _ => rfl) y
    exact ⟨⟨y₂, hy₂⟩⟩
  by_cases hc : Nonempty (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp
  · obtain ⟨k₀⟩ := hc
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k₀)
    refine ⟨Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)}, ?_, fun k => ?_⟩
    · haveI := (hS k₀ ⟨x₀, hx₀⟩).2
      haveI := hne ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)
      exact Nat.card_pos
    · obtain ⟨x, hx⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k)
      rw [(hS k ⟨x, hx⟩).1]
      exact hK _ _
  · refine ⟨1, one_pos, fun k => (hc ⟨k⟩).elim⟩

end GlobalTheory.LevModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentIndexSumEqConstStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_component_index_sum_eq_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∃ N : ℕ, 0 < N ∧ ∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N := by
  first | exact @GlobalTheory.LevModel.cover_degree_const | exact GlobalTheory.LevModel.cover_degree_const | (intros; apply GlobalTheory.LevModel.cover_degree_const <;> assumption)
end
