module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspForms
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductsShortRec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaStableOfAlgHom
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeries
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaLevelMove

section Move

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.TranslMove GlobalTheory.VVRank GlobalTheory.ShortValMove
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_isVtOver {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} {τ : T.left ⟶ T₀.left} {L₀ : RigLB G} {L₁ : RigLB A}
    {w : LB.Iso L₁.L (L₀.L.pull φ)} (hw : w.IsGen)
    {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (h₁ : Ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ)
    (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    {e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left} (he : eSec A ≫ φ = e ≫ eSec G)
    (hρ : PMaps w (K := PUnit) (fun _ => eSec A) (fun _ => eSec G) (fun _ => 1) L₁.rig L₀.rig e) (N : ℕ)
    (hk : ∀ θ : ThetaGrp A L₁.L ((N : ℤ) ^ 2) T, θ.pt ^ (N ^ 2) = 1)
    {s₀ : LB.Sec (LPow G L₀.L 1 T₀)} {s : LB.Sec (LPow A L₁.L 1 T)} (hs : SecRel w Ψ s₀ s)
    {ok₀ : (T₀ ⟶ G) → Prop} {ok : (T ⟶ A) → Prop} {t₀ : T₀ ⟶ G} {t : T ⟶ A}
    (ht : ∀ y : T₀ ⟶ G, y ^ N = t₀ → ok₀ y → ∃ x : T ⟶ A, τ ≫ y.left = x.left ≫ φ ∧ x ^ N = t ∧ ok x)
    {F₀ : LB.Sec (LPow G L₀.L ((N : ℤ) ^ 2) T₀)} (H : IsVtOver G L₀ N ok₀ s₀ t₀ F₀) :
    ∃ F, IsVtOver A L₁ N ok s t F ∧ SecRel w Ψ F₀ F := by
  obtain ⟨y₁, β₀, β, r₁, V₁, hy, oy, g₀, n₀, cβ, tw, sl₁, ac₁⟩ := H
  obtain ⟨x₁, hx₁, hx, ox⟩ := ht y₁ hy oy
  obtain ⟨α₀, gα₀, nα₀, v₀⟩ := exists_normMul hp L₀.isLB L₁.isLB hw he hρ N g₀ n₀
  obtain ⟨α, gα, cα⟩ := NormMulUniv.exists_pull L₁.isLB α₀ gα₀ T
  have v : GenRel w Ψ β α := fun Z r z J₀ J hJ₀ hJ => by
    rw [val_corr hJ₀ cβ, val_pull hJ₀, val_corr hJ cα, val_pull hJ, Category.assoc, h₂, ← Category.assoc,
      v₀ Z _ z J₀ J hJ₀ hJ, Category.comp_id, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨s₁, tw'⟩ := VVRank.exists_isTwistPull A (ψ := mulT A T N) (hm := lift_snd _ _) (b := 1) L₁.isLB gα s
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow hp h₂ N) h₂) v tw tw' hs
  obtain ⟨U₁, l₁, a₁⟩ := exists_symLift hp L₀.isLB L₁.isLB hw h₁ h₂ hk hx₁ sl₁
  obtain ⟨F, b₁, R₂⟩ := a₁ _ _ _ ac₁ R₁
  exact ⟨F, ⟨x₁, α₀, α, s₁, U₁, hx, ox, gα₀, nα₀, cα, tw', l₁, b₁⟩, R₂⟩

theorem isVtOver_move (hLaw : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {x x' : Sp S ⟶ Xo.X} {pm : Gx x ⟶ Gx x'}
    {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)}
    (h₁ : pm ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) (hw : CubIso ν w)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} (hs : SecRel (T := Over.mk x) (T₀ := Over.mk x') w pm s' s) (N : ℕ)
    {ok' : (ptO Xo x' ⟶ Xo.univ.t.G) → Prop} {ok : (ptO Xo x ⟶ Xo.univ.t.G) → Prop}
    {t' : ptO Xo x' ⟶ Xo.univ.t.G} {t : ptO Xo x ⟶ Xo.univ.t.G}
    (ht : ∀ q : ptO Xo x' ⟶ Xo.univ.t.G, q ^ N = t' → ok' q →
      ∃ p : ptO Xo x ⟶ Xo.univ.t.G, q.left = p.left ≫ ν.φ ∧ p ^ N = t ∧ ok p)
    {F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x'))}
    (hF : IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok' s' t' F') :
    ∃ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x)),
      IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F ∧ SecRel (T := ptO Xo x) (T₀ := ptO Xo x') w pm F' F := by
  have := UnivPol.isLocallyNoetherian Xo
  have hρ := (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig Xo.univ.t.PP.rig ν.cm.e _
    (rigPull_le ν.cm.F ν.cm.e ν.cm.e_comm Xo.univ.t.PP.L) (fun _ => rfl)).1 hw.2.1
  exact exists_isVtOver ν.cart (T := ptO Xo x) (T₀ := ptO Xo x') (τ := 𝟙 (Sp S)) hw.1
    (h₁.trans (Category.comp_id _).symm) h₂ ν.cm.e_comm hρ N
    (fun θ => pt_pow_eq_one hLaw.kerPow (UnivPol.pol Xo) (N ^ 2) (Nat.cast_pow N 2).symm θ) hs
    (fun q hq oq => (ht q hq oq).imp fun p hp => ⟨(Category.id_comp _).trans hp.1, hp.2⟩) hF

theorem nab_move (hLaw : Laws) (hCI : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c}
    (hnab : IsNab Xo c nab) {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} {pm : Gx y.x ⟶ Gx y'.x}
    {w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (hx : y'.x = y.x ≫ ρ)
    (h₁ : pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left)
    (h₂ : pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ) (hw : CubIso ν w)
    (hu : ∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (N : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x)))
    (hF : ∀ b, SecRel (T := ptO Xo y.x) (T₀ := ptO Xo y'.x) w pm (F' b) (F b)) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  have hL := Xo.univ.t.PP.isLB
  have e : (N : ℤ) ^ 2 = (N ^ 2 : ℕ) := (Nat.cast_pow N 2).symm
  refine GlobalTheory.T.harmonic_values_invariant_universal_endomorphism hLaw hCI E H Dw l Xo c nab hnab S ρ ν y y' pm w hx h₁ h₂ hw hu n a P hP N F F' fun b => ?_
  have hc := @secRel_iff _ _ _ _ _ _ ν.cm.F (ptO Xo y.x) (ptO Xo y'.x) _ _ w pm hL hL h₂ ((N : ℤ) ^ 2) (N ^ 2) e
  exact (hc _ _).1 (hF b)

theorem thValAt_move (hLaw : Laws) (hCI : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c}
    (hnab : IsNab Xo c nab) {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} {y y' : FrPt Xo c S}
    (hlev : IsLevMove ρ ν gM gA) (hmv : FrMove ρ ν y y') {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {x : Fin n → Dw.La} {v : S} (hv : ThValAt Xo c nab y' x P v) :
    ThValAt Xo c nab y (fun b => gM (x b)) P v := by
  obtain ⟨S', _, _, φ, y₁', F', hff, hfr, hV, hval⟩ := hv
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.FramedBaseChange.exists_frMap hLaw E H Dw l Xo c S S' φ y
  obtain ⟨hx, hu, pm, ω, hf, hs, hω, hR⟩ := exists_move_baseChange hmv hy₁ hfr
  obtain ⟨e, he⟩ := exists_ptEquiv ν hx
  have he' : ∀ p, p.left = (e.symm p).left ≫ ν.φ := fun p => by rw [← he, e.apply_symm_apply]
  have hact : ∀ p b, e (p ≫ Xo.univ.t.act.act b) = e p ≫ Xo.univ.t.act.act b := fun p b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, ν.act])
  have hact' : ∀ p b, e.symm p ≫ Xo.univ.t.act.act b = e.symm (p ≫ Xo.univ.t.act.act b) := fun p b =>
    e.injective (by rw [hact, e.apply_symm_apply, e.apply_symm_apply])
  have hlv : ∀ q : Dw.La, e (levPt Xo y₁.x (gM q)) = levPt Xo y₁'.x q := fun q => by
    refine Over.OverMorphism.ext ?_
    rw [he, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, hlev.2.1, Over.toUnit_left,
      Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx.symm)
  choose F hF hFF using fun b : Fin n =>
    isVtOver_move hLaw hf hs hω hR l.M (ok := KilledBy Xo (l.Mb ^ 2)) (t := levPt Xo y₁.x (gM (x b)))
      (fun p hp op => ⟨e.symm p, he' p, by rw [← map_pow, hp, ← hlv, e.symm_apply_apply],
        fun r hr => by rw [hact', op r hr, map_one]⟩) (hV b)
  refine ⟨S', inferInstance, inferInstance, φ, y₁, F, hff, hy₁, hF, ?_⟩
  rw [hval, thExpr, thExpr, nab_move hLaw hCI hnab hx hf hs hω hu hP l.M F F' hFF]

end Move

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem actLev_mem_th : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.th j w, f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.th j w := by
  intro hCI D T h j hj w γ f hf _
  obtain ⟨x, P, hP, hf⟩ := hf
  obtain ⟨st, hnab⟩ := h.nabPin j hj
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
    have hk := D.R.m_add_three_le_k
    have h1 := hj.1
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have hA := (GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hr h.pins.2.1.2).total
  refine ⟨fun b => liftLa γ (x b), P, hP, fun p y => ?_⟩
  obtain ⟨ρ, ν, -, hlev, hmv⟩ := mvPt_spec hA γ y
  exact thValAt_move GlobalTheory.firstFiveLaws.1 hCI hnab hlev hmv hP.1 (hf p _)

end GlobalTheory.ThetaLevelMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemThetaSeriesStatement
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_mem_thetaSeries : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.th j w, f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.th j w := by
  first | exact @GlobalTheory.ThetaLevelMove.actLev_mem_th | exact GlobalTheory.ThetaLevelMove.actLev_mem_th | (intros; apply GlobalTheory.ThetaLevelMove.actLev_mem_th <;> assumption)
end
end

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem theta_stable_of_algHom {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (Ψ : X.Forms →ₐ[B.KO] X.Forms) (Sc : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (hL : ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Ψ (X.inc wL F) = X.inc wL F')
    (hS : ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Ψ (X.inc w F) = X.inc w F') :
    ∀ x ∈ X.Theta Sc ka wL wF T, Ψ x ∈ X.Theta Sc ka wL wF T := by
  let Φ : X.Forms →ₐ[𝓞 B.KO] X.Forms := Ψ.restrictScalars _
  suffices key : (X.Theta Sc ka wL wF T).map Φ.toLinearMap ≤ X.Theta Sc ka wL wF T from
    fun x hx => key ⟨x, hx, rfl⟩
  change ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Φ (X.inc wL F) = X.inc wL F' at hL
  change ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Φ (X.inc w F) = X.inc w F' at hS
  have hsm : ∀ (s : 𝓞 B.KO) w (F : B.Cusp j w), X.inc w (s • F) = s • X.inc w F := fun s w F =>
    ((X.inc w).restrictScalars (𝓞 B.KO)).map_smul s F
  have hsc : ∀ (s : 𝓞 B.KO) w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') →
      ∀ F ∈ X.scaled s w N, ∃ F' ∈ X.scaled s w N, Φ (X.inc w F) = X.inc w F' := by
    rintro s w N hN _ ⟨F, hF, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    refine ⟨_, ⟨F', hF', rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, hsm, map_smul, e]
  have hemb : ∀ w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') → (X.emb w N).map Φ.toLinearMap ≤ X.emb w N := by
    rintro w N hN _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    exact ⟨F', hF', e.symm⟩
  have h1 : (X.emb wL (X.WWc Sc.sW wL)).map Φ.toLinearMap ≤ X.emb wL (X.WWc Sc.sW wL) :=
    hemb _ _ (hsc _ _ _ hL)
  have h2 : ∀ s w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) →
      (X.emb w (X.Thc s w)).map Φ.toLinearMap ≤ X.emb w (X.Thc s w) := fun s w hw =>
    hemb _ _ (hsc _ _ _ (hsc _ _ _ (hS w hw)))
  unfold WeightAlgebra.PJ.Theta
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_mul, Submodule.map_mul, Submodule.map_pow, Submodule.map_pow]
  refine sup_le_sup (sup_le_sup (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inl rfl)))
    (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inr (Or.inl rfl))))) (h2 _ _ (Or.inr (Or.inr rfl)))

theorem map_mem_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) (ψ : R j →ₗ[K] R j)
    (hs : ∀ f ∈ s, ∃ (u : 𝓞 K) (f' : R j), f' ∈ s ∧ ψ f = (u : K) • f') (F F' : cutR C j w) (e : F'.1 = ψ F.1) (hF : F ∈ spanIn C j w s) :
    F' ∈ spanIn C j w s := by
  change F'.1 ∈ Submodule.span (𝓞 K) s
  rw [e]
  have hle : (Submodule.span (𝓞 K) s).map (ψ.restrictScalars (𝓞 K)) ≤ Submodule.span (𝓞 K) s := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨u, f', hf', e'⟩ := hs f hf
    have e'' : ψ f = u • f' := e'.trans (algebraMap_smul K u f')
    change ψ f ∈ Submodule.span (𝓞 K) s
    rw [e'']
    exact Submodule.smul_mem _ u (Submodule.subset_span hf')
  exact hle ⟨F.1, hF, rfl⟩

theorem coe_one_smul_eq {K : Type} [Field K] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)] (j : ℕ)
    (x : R j) : x = ((1 : 𝓞 K) : K) • x := by
  simp

noncomputable def actLevAlg {D : D7} (T : Top D) (j : ℕ)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) : T.R j →ₐ[T.Q.c.F] T.R j :=
  AlgHom.ofLinearMap (actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ) rfl (fun _ _ => rfl)

theorem levAct_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j), LawsFull T → (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (Sc : WeightAlgebra.Scal (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ∀ (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j ka → (recB h.toLawsCore).Cusp j ka), IsLevAct T.toTop h j ka ℓ act → ∀ g F, (recPJ h j hj).inc ka F ∈ (recPJ h j hj).Theta Sc ka wL wF Tn → (recPJ h j hj).inc ka (act g F) ∈ (recPJ h j hj).Theta Sc ka wL wF Tn := by
  intro hC D T h j hj hfull hxi Sc ka wL wF Tn _ hn _ hr P ℓ act hact g F hF
  let ψ := actLevAlg T.toTop j (ℓ g)
  let Φ0 : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] AddMonoidAlgebra (T.R j) (Deg D j) :=
    AddMonoidAlgebra.mapAlgHom (Deg D j) ψ
  let Φ : @AlgHom _ _ _ _ _ _ (recPJ h j hj).aF (recPJ h j hj).aF := Φ0
  have hΦ : ∀ w (F F' : (recB h.toLawsCore).Cusp j w), F'.1 = ψ F.1 →
      Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w F F' e
    change Φ0 (AddMonoidAlgebra.single (deg w) F.1) = AddMonoidAlgebra.single (deg w) F'.1
    rw [e]
    exact AddMonoidAlgebra.mapAlgHom_single _ _ _
  have hspan : ∀ w (s : Set (T.R j)), (∀ f ∈ s, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ s ∧ ψ f = (u : T.Q.c.F) • f') →
      ∀ F ∈ spanIn T.C j w s,
      ∃ F' ∈ spanIn T.C j w s, Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w s hs F hF
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_levelChangeAction_on_cuspForms D T.toTop h j hj w P ℓ
    exact ⟨a g F, map_mem_spanIn T.C j w s ψ.toLinearMap hs F _ (ha g F) hF, hΦ w F _ (ha g F)⟩
  have hone : ∀ x : T.R j, x = ((1 : 𝓞 T.Q.c.F) : T.Q.c.F) • x := fun x => coe_one_smul_eq (R := T.R) j x
  have key := theta_stable_of_algHom (recPJ h j hj) Φ Sc ka wL wF Tn
    (hspan wL (T.th j wL) fun f hf => by
      obtain ⟨_, hnab⟩ := h.nabPin j hj
      exact ⟨1, ψ f, GlobalTheory.T.levelAction_mem_thetaSeries hC D T.toTop h j hj wL (ℓ g) f hf
        (GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC _ _ _ _ _ _ _ hnab _ _ f hf), hone _⟩)
    (fun w hw => hspan w (T.toTop.sh j w) fun f hf => GlobalTheory.T.levelAction_shortThetaSeries_rootOfUnity_mul hC D T hfull j hj hxi w (by
      rcases hw with rfl | rfl | rfl
      · exact hr
      · exact hr.trans (Nat.le_add_right _ _)
      · rw [hn]; exact hr.trans (Nat.le_add_right _ _)) (ℓ g) f hf)
  rw [← hΦ ka F (act g F) (hact g F)]
  exact key _ hF

end GlobalTheory.FormTies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaSpansIsLatIn
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K] {C : Type} [AddCommGroup C]
  [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C)

theorem spanK_fg_of_subset [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] (N : Submodule (𝓞 F) C) (hN : N.FG)
    (s : Set C) (hs : s ⊆ N) : (spanK z s).FG := by
  classical
  obtain ⟨t, ht⟩ := hN
  have hle : spanK z s ≤ spanK z (t : Set C) := by
    unfold spanK
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hf' : f ∈ Submodule.span (𝓞 F) (t : Set C) := ht ▸ hs hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : z.symm (1 ⊗ₜ[F] (a • x)) =
          (RingOfIntegers.mapRingHom (algebraMap F K) a) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F a x, TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul,
          ← algebraMap_smul K (RingOfIntegers.mapRingHom (algebraMap F K) a)]
        rfl
      beta_reduce
      rw [e]
      exact Submodule.smul_mem _ _ hx
  have hfg : (spanK z (t : Set C)).FG := Submodule.fg_span (t.finite_toSet.image _)
  exact hfg.of_le hle

theorem span_spanK_eq_top (s : Set C) (hs : Submodule.span F s = ⊤) :
    Submodule.span K (spanK z s : Set (Fin n → K)) = ⊤ := by
  have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z s : Set (Fin n → K)) := by
    intro f
    have hf : f ∈ Submodule.span F s := hs ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (h1 f)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem scalOfP_sK_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {j : ℕ} (p : ℕ) (hp : 0 < p) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (scalOfP B hinj EX p ka wL wF T).sK ≠ 0 := by
  obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
  have h1 := fun w => (GlobalTheory.log_norm_normaliser D B hinj EX j w σ).1
  have h2 := fun a b c => ((GlobalTheory.RunIn.pPow_size D j ka).2.2.2.2.2 a b c).1
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (h1 _))) (h1 _)) ?_
  · exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  · exact Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h2 _ _ _))

theorem theta_spans_isLatIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → 0 < p → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → Submodule.IsLattice B.KO (B.Mlat j ka) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt X ka → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v i) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v i) := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act ht hp hF hn hD hM hSp h2
  have hle := Formalism.MainNotions.Gaps.T0.theta_le_msup X _ h2 hF rfl hn hD
  refine ⟨⟨?_, ?_⟩, ht.ThK_fg, ?_⟩
  · rw [ht.Th_eq]
    refine spanK_fg_of_subset z (B.Mlat j ka) hM.fg _ fun f hf => ?_
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 (hle hf)
    exact X.inc_inj ka e ▸ hg
  · rw [ht.Th_eq]
    apply span_spanK_eq_top
    apply top_unique
    rw [← hSp]
    apply Submodule.span_le.2
    intro f hf
    let a : 𝓞 B.KO := (scalOfP B hinj EX p ka wL wF T).sK
    let b : 𝓞 B.KO := ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * ka.n)
    have ha : (a : B.KO) ≠ 0 := by
      exact_mod_cast scalOfP_sK_ne_zero B hinj EX p hp ka wL wF T
    have hb : (b : B.KO) ≠ 0 := by
      dsimp [b]
      exact_mod_cast pow_ne_zero (D.R.f * D.R.r * ka.n) (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hm : X.inc ka (a • (b • f)) ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T := by
      apply (le_sup_right : X.emb ka (X.Thc a ka) ≤ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T)
      apply Submodule.mem_map.2
      refine ⟨a • (b • f), ?_, rfl⟩
      exact Submodule.mem_map.2 ⟨b • f, Submodule.mem_map.2 ⟨f, hf, rfl⟩, rfl⟩
    have hs := Submodule.subset_span (R := B.KO) (s := {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}) hm
    have he : a • (b • f) = ((a : B.KO) * (b : B.KO)) • f := by
      rw [← algebraMap_smul B.KO a (b • f), ← algebraMap_smul B.KO b f, smul_smul]
    rw [he] at hs
    have := (Submodule.span B.KO {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}).smul_mem (((a : B.KO) * (b : B.KO))⁻¹) hs
    change f ∈ Submodule.span B.KO {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero ha hb), one_smul] using this
  · apply top_unique
    have hs : Submodule.span K (spanK z (X.shortTh ka : Set _) : Set (Fin (O.nZ i) → K)) = ⊤ := span_spanK_eq_top z _ hSp
    rw [← hs]
    apply Submodule.span_mono
    intro x hx
    apply ht.ThK_ge
    exact spanK_mono z (fun f hf => by
      change X.inc ka f ∈ thetaPlain X ka wL wF T
      apply (le_sup_right : X.emb ka (X.shortTh ka) ≤ thetaPlain X ka wL wF T)
      exact Submodule.mem_map.2 ⟨f, hf, rfl⟩) hx
end GlobalTheory.FormTies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledSpanClauses
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaScaledSpanLeSigmaSmulUnscaledSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaScaledSpanLeSigmaSmulUnscaledSpan
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScaledSpan

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def sc (s : R) (N : Submodule R A) : Submodule R A := N.map (s • LinearMap.id)

theorem mem_sc {s : R} {N : Submodule R A} {x : A} : x ∈ sc s N ↔ ∃ y ∈ N, x = s • y := by
  simp [sc, eq_comm]

theorem sc_mul_le {s t : R} {M M' N N' : Submodule R A} (h : M ≤ sc s M') (h' : N ≤ sc t N') :
    M * N ≤ sc (s * t) (M' * N') := by
  refine Submodule.mul_le.2 fun m hm n hn => ?_
  obtain ⟨a, ha, rfl⟩ := mem_sc.1 (h hm)
  obtain ⟨b, hb, rfl⟩ := mem_sc.1 (h' hn)
  exact mem_sc.2 ⟨a * b, Submodule.mul_mem_mul ha hb, smul_mul_smul_comm s a t b⟩

theorem sc_pow_le {s : R} {M M' : Submodule R A} (h : M ≤ sc s M') (n : ℕ) :
    M ^ n ≤ sc (s ^ n) (M' ^ n) := by
  induction n with
  | zero => intro x hx; exact mem_sc.2 ⟨x, by simpa using hx, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ, pow_succ]; exact sc_mul_le ih h

theorem sc_le_of_dvd {s t : R} {M N : Submodule R A} (hd : t ∣ s) (h : M ≤ N) : sc s M ≤ sc t N := by
  obtain ⟨c, rfl⟩ := hd
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_sc.1 hx
  exact mem_sc.2 ⟨c • y, N.smul_mem c (h hy), mul_smul t c y⟩

end General

variable {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem emb_WWc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.WWc s w) ≤ sc s (X.emb w (X.thAll w)) := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, by simp⟩

theorem emb_Thc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.Thc s w) ≤
      sc (s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n)) (X.emb w (X.shortTh w)) := by
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  refine mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

theorem nnW_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {ka wL wF : WeightFamilies.Wt D j} {T n : ℕ} (h : WeightAlgebra.IsF' ka wL wF T n) :
    nnW B hinj EX ka = nnW B hinj EX wL ^ T * nnW B hinj EX wF := by
  obtain ⟨-, hP, hM⟩ := h
  have hP' : ∀ τ i, ka.aP τ i = wL.aP τ i * T + wF.aP τ i := fun τ i => by
    have := hP τ i
    zify
    linarith
  have hM' : ∀ τ i, ka.aM τ i = wL.aM τ i * T + wF.aM τ i := fun τ i => by
    have := hM τ i
    zify
    linarith
  have h1 : Dplus ka = Dplus wL * T + Dplus wF := by
    simp only [Dplus, hP', Finset.sum_add_distrib, Finset.sum_mul]
  have h2 : Dminus ka = Dminus wL * T + Dminus wF := by
    simp only [Dminus, hM', Finset.sum_add_distrib, Finset.sum_mul]
  simp only [nnW, h1, h2, Fin.prod_univ_two]
  ring

theorem nnW_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) : nnW B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact_mod_cast (D.host.g_prime i).ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))

theorem theta_le_sigma_smul : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  intro D B P6 j X hinj EX p ka wL wF T hF hn hT
  refine ⟨?_, fun F hF' => mem_sc.1 (?_ : F ∈ sc _ _)⟩
  · refine mul_ne_zero (nnW_ne_zero B hinj EX ka) (Nat.cast_ne_zero.2 ?_)
    have hq : D.host.q ≠ 0 := (D.host.hyp.1 : D.host.q.Prime).ne_zero
    have hd : D.host.d ≠ 0 := (D.host.hyp.2.1 : D.host.d.Prime).ne_zero
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    have hS : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    unfold pPow
    positivity
  · revert F
    change X.Theta _ ka wL wF T ≤ _
    have hnn := nnW_eq B hinj EX hF
    refine sup_le (sup_le ?_ ?_) ?_
    · refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) T) (emb_Thc_le X _ wF)).trans
        (sc_le_of_dvd ⟨(zOwnP D p wF : 𝓞 B.KO), ?_⟩ (le_sup_left.trans le_sup_left))
      simp only [scalOfP, sigRec, hnn, pPow]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
      refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) _) (emb_Thc_le X _ _)).trans
        (sc_le_of_dvd ⟨(zOwnP D p (X.wF0 wL wF) : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (WeightFamilies.dimY D j * wL.n)), ?_⟩
          (le_sup_right.trans le_sup_left))
      have e : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
      simp only [scalOfP, sigRec, hnn, pPow, e, Nat.add_sub_cancel_left]
      unfold WeightAlgebra.PJ.wF0
      push_cast
      ring
    · refine (emb_Thc_le X _ ka).trans
        (sc_le_of_dvd ⟨(zOwnP D p ka : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (T * wL.n)), ?_⟩ le_sup_right)
      simp only [scalOfP, sigRec, hnn, pPow, hn]
      push_cast
      ring

end GlobalTheory.ScaledSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaScaledSpanLeSigmaSmulUnscaledSpanStatement
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_scaled_span_le_sigma_smul_unscaled_span : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  first | exact @GlobalTheory.ScaledSpan.theta_le_sigma_smul | exact GlobalTheory.ScaledSpan.theta_le_sigma_smul | (intros; apply GlobalTheory.ScaledSpan.theta_le_sigma_smul <;> assumption)
end
end

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory

theorem scaledSpan_clauses : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → (∀ g F, X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T → X.inc ka (act g F) ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T) → O.Th v i ≤ O.Ms i ∧ (∀ g : P, (O.Th v i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Th v i) ∧ O.σ v i ≠ 0 ∧ O.Th v i ≤ Formalism.EigenvalueLevelCeiling.sc (O.σ v i) (O.ThK v i) := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act h hF hn hD h2 hact
  obtain ⟨hσ, hsig⟩ := GlobalTheory.T.theta_scaled_span_le_sigma_smul_unscaled_span D B P6 j X hinj EX p ka wL wF T hF hn hD
  have hle := Formalism.MainNotions.Gaps.T0.theta_le_msup X _ h2 hF rfl hn hD
  have hσK : (((sigRec B hinj EX ka wL wF T : 𝓞 B.KO) : B.KO)) ≠ 0 := by
    intro h0
    exact hσ (RingOfIntegers.coe_eq_zero_iff.1 h0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.Th_eq, h.Ms_eq]
    refine Submodule.span_mono (Set.image_mono fun F hFm => ?_)
    obtain ⟨G, hG, e⟩ := Submodule.mem_map.1 (hle hFm)
    have : G = F := X.inc_inj ka e
    exact this ▸ hG
  · intro g
    rw [h.Th_eq, spanK, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hFm, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨act g F, hact g F hFm, ?_⟩
    exact (h.rho_eq g F).symm
  · rw [h.σ_eq]
    exact (map_ne_zero_iff _ (algebraMap B.KO K).injective).2 hσK
  · rw [h.Th_eq, spanK, Submodule.span_le]
    rintro _ ⟨F, hFm, rfl⟩
    obtain ⟨G, hG, e⟩ := hsig _ hFm
    set s : B.KO := ((sigRec B hinj EX ka wL wF T : 𝓞 B.KO) : B.KO) with hs
    have e' : X.inc ka F = s • G := by
      rw [e, hs]
      exact (algebraMap_smul B.KO _ G).symm
    have hG' : X.inc ka (s⁻¹ • F) = G := by
      rw [map_smul, e', smul_smul, inv_mul_cancel₀ hσK, one_smul]
    have hmem : z.symm (1 ⊗ₜ[B.KO] (s⁻¹ • F)) ∈ O.ThK v i :=
      h.ThK_ge (Submodule.subset_span ⟨s⁻¹ • F, by simpa [hG'] using hG, rfl⟩)
    refine Submodule.mem_map.2 ⟨_, hmem, ?_⟩
    have key : O.σ v i • z.symm (1 ⊗ₜ[B.KO] (s⁻¹ • F)) = z.symm (1 ⊗ₜ[B.KO] F) := by
      rw [← map_smul, h.σ_eq]
      congr 1
      change algebraMap B.KO K s • _ = _
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, smul_smul, mul_inv_cancel₀ hσK, one_smul]
    simpa using key

end GlobalTheory
end

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

private theorem choose_two_add' (p q : ℕ) : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

private theorem dimY_eq_flag' {D : D7} {j : ℕ} (hj : InR D j) : WeightFamilies.dimY D j = D.R.f * D.R.r.choose 2 := by
  have h : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    have := hj.1; have := hj.2
    unfold Ranks.r Ranks.sigW; simp only; omega
  unfold WeightFamilies.dimY
  rw [h, choose_two_add', Nat.choose_two_right, Nat.choose_two_right]

private lemma ofGaps_eq_sub_mul' {p : ℕ} (a b g : Fin p → ℕ) (T : ℕ)
    (hg : ∀ k : Fin p, (g k : ℤ) = if (k : ℕ) + 1 < p then _root_.Formalism.MainNotions.WeightAlgebra.gapZ a k - T * _root_.Formalism.MainNotions.WeightAlgebra.gapZ b k
      else (a k : ℤ) - T * b k) (i : Fin p) :
    (_root_.Formalism.MainNotions.DIV.Cons.ofGaps g i : ℤ) = a i - T * b i := by
  suffices h : ∀ n, ∀ i : Fin p, p - (i : ℕ) = n → (_root_.Formalism.MainNotions.DIV.Cons.ofGaps g i : ℤ) = a i - T * b i from
    h _ i rfl
  intro n
  induction n with
  | zero => intro i hi; have := i.isLt; omega
  | succ n ih =>
    intro i hi
    by_cases h : (i : ℕ) + 1 < p
    · rw [_root_.Formalism.MainNotions.DIV.Cons.ofGaps_succ g i h]
      push_cast
      rw [ih ⟨(i : ℕ) + 1, h⟩ (by simp only; omega), hg i, if_pos h]
      unfold _root_.Formalism.MainNotions.WeightAlgebra.gapZ
      rw [dite_eq_left h, dite_eq_left h]
      ring
    · rw [_root_.Formalism.MainNotions.DIV.Cons.ofGaps_last g i h, hg i, if_neg h]

private lemma mul_toNat_fdiv_add_two_le_of_add_two_le' {T K : ℕ} (hK : T + 2 ≤ K) {d : ℤ} (hd : 0 ≤ d) :
    (T : ℤ) * ((d + 2).fdiv K).toNat ≤ d := by
  have hKpos : (0 : ℤ) < K := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hKpos.le]
  have hq : 0 ≤ (d + 2) / (K : ℤ) := Int.ediv_nonneg (by omega) hKpos.le
  rw [Int.toNat_of_nonneg hq]
  have hle := Int.ediv_mul_le (d + 2) hKpos.ne'
  have hK' : (T : ℤ) + 2 ≤ K := by exact_mod_cast hK
  rcases (show (d + 2) / (K : ℤ) = 0 ∨ 1 ≤ (d + 2) / (K : ℤ) by omega) with h0 | h1
  · rw [h0]; simp [hd]
  · nlinarith

private lemma gapZ_nonneg_of_antitone' {p : ℕ} (a : Fin p → ℕ) (ha : Antitone a) (k : Fin p) :
    0 ≤ _root_.Formalism.MainNotions.WeightAlgebra.gapZ a k := by
  unfold _root_.Formalism.MainNotions.WeightAlgebra.gapZ
  split_ifs with h
  · have hk : k ≤ ⟨(k : ℕ) + 1, h⟩ := by rw [Fin.le_iff_val_le_val]; simp
    have := ha hk
    omega
  · positivity

private lemma mul_toNat_fdiv_le_of_le_of_nonneg' {T K : ℕ} (hK : T + 2 ≤ K) {y a : ℤ} (hy : y ≤ a)
    (ha : 0 ≤ a) : (T : ℤ) * (y.fdiv K).toNat ≤ a := by
  have hKpos : (0 : ℤ) < K := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hKpos.le]
  by_cases hq : 0 ≤ y / (K : ℤ)
  · rw [Int.toNat_of_nonneg hq]
    have hle := Int.ediv_mul_le y hKpos.ne'
    have hK' : (T : ℤ) + 2 ≤ K := by exact_mod_cast hK
    nlinarith
  · rw [Int.toNat_of_nonpos (by omega)]
    simpa using ha

private theorem isF'_fWt' {D : D7} {j : ℕ} (ka : WeightFamilies.Wt D j) (T nW nP : ℕ) (hW : Even nW) (hP : Even nP) :
    WeightAlgebra.IsF' ka (lWt D ka T nW hW) (fWt D ka (lWt D ka T nW hW) T nP hP) T nP := by
  have hK : T + 2 ≤ WeightAlgebra.Tp D j T := by unfold WeightAlgebra.Tp; omega
  unfold WeightAlgebra.IsF'
  refine ⟨rfl, fun τ i => ?_, fun τ i => ?_⟩
  · have hl : (lWt D ka T nW hW).aP τ = ofGaps (lGapP D ka T nW τ) := rfl
    show (ofGaps (fGapP D ka (lWt D ka T nW hW) T τ) i : ℤ) = _
    refine ofGaps_eq_sub_mul' _ _ _ T (fun k => ?_) i
    unfold fGapP
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      rw [hl, gapZ_ofGaps]
      unfold lGapP
      rw [if_pos h]
      have := mul_toNat_fdiv_add_two_le_of_add_two_le' hK (gapZ_nonneg_of_antitone' _ (ka.aPlus_antitone τ) k)
      linarith
    · refine Int.toNat_of_nonneg ?_
      rw [hl, ofGaps_last _ k h]
      unfold lGapP
      rw [if_neg h]
      refine sub_nonneg.mpr (mul_toNat_fdiv_le_of_le_of_nonneg' hK ?_ (by positivity))
      refine (sub_le_self _ ?_).trans (sub_le_self _ ?_) <;> positivity
  · have hl : (lWt D ka T nW hW).aM τ = ofGaps (lGapM D ka T τ) := rfl
    show (ofGaps (fGapM D ka (lWt D ka T nW hW) T τ) i : ℤ) = _
    refine ofGaps_eq_sub_mul' _ _ _ T (fun k => ?_) i
    unfold fGapM
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      rw [hl, gapZ_ofGaps]
      unfold lGapM
      rw [if_pos h]
      have := mul_toNat_fdiv_add_two_le_of_add_two_le' hK (gapZ_nonneg_of_antitone' _ (ka.aM_anti τ) k)
      linarith
    · refine Int.toNat_of_nonneg ?_
      rw [hl, ofGaps_last _ k h]
      unfold lGapM
      rw [if_neg h]
      have := mul_toNat_fdiv_le_of_le_of_nonneg' hK le_rfl (show (0 : ℤ) ≤ ka.aM τ k by positivity)
      linarith

private theorem coord_one_tmul_smul' {F : Type} [Field F] {K : Type} [Field K] [Algebra F K]
    {C : Type} [AddCommGroup C] [Module F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (r : F) (f : C) :
    z.symm (1 ⊗ₜ[F] (r • f)) = algebraMap F K r • z.symm (1 ⊗ₜ[F] f) := by
  rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    Algebra.smul_def, smul_eq_mul]

private theorem spanK_span' {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K]
    {C : Type} [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (s : Set C) :
    spanK z (Submodule.span (𝓞 F) s : Set C) = spanK z s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hi : IsIntegral ℤ (algebraMap F K (r : F)) :=
        (RingOfIntegers.isIntegral_coe r).map (algebraMap F K).toIntAlgHom
      have e : z.symm (1 ⊗ₜ[F] (r • x)) = (⟨algebraMap F K (r : F), hi⟩ : 𝓞 K) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F r x, coord_one_tmul_smul']
        rfl
      simp only [e]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

private theorem spanK_isLatIn' {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K]
    {C : Type} [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (hfg : M.FG)
    (htop : Submodule.span F (M : Set C) = ⊤) : Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (spanK z (M : Set C)) := by
  constructor
  · obtain ⟨s, rfl⟩ := hfg
    rw [spanK_span']
    exact Submodule.fg_span (s.finite_toSet.image _)
  · have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z (M : Set C) : Set (Fin n → K)) := by
      intro f
      have hf : f ∈ Submodule.span F (M : Set C) := htop ▸ Submodule.mem_top
      induction hf using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [TensorProduct.tmul_add, map_add (f := _)]
        exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [coord_one_tmul_smul']
        exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, rfl⟩ := z.symm.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k f =>
      have e : (k ⊗ₜ[F] f : K ⊗[F] C) = k • (1 ⊗ₜ[F] f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ (h1 f)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hx trivial) (hy trivial)

private theorem supLattice_isLatIn_stable' : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → Submodule.IsFullLattice B.KO (B.Mlat j ka) → (∀ g, ∀ F ∈ B.Mlat j ka, act g F ∈ B.Mlat j ka) → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act h hL hact
  rw [h.Ms_eq]
  refine ⟨spanK_isLatIn' z _ hL.toIsLattice.fg hL.span_eq_top, fun g => ?_⟩
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  show O.ρ i g (z.symm (1 ⊗ₜ f)) ∈ spanK z _
  rw [h.rho_eq]
  exact Submodule.subset_span ⟨act g f, hact g f hf, rfl⟩

theorem leaves_sup_span_lemmaS_of_formTieK : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc), (∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J), ∃ (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j) (p : ℕ) (_ : Algebra (recB h.toLawsCore).KO K), ∃ z act, ∃ ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), FormTieK (recPJ h j hj) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO O v i z act ∧ IsLevAct T.toTop h j (kaR Tp hK j) ℓ act ∧ LawsFull T ∧ (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) ∧ OneCover T.toTop j ∧ 0 < p ∧ Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j (kaR Tp hK j) ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) (kaR Tp hK j) ∧ WeightAlgebra.H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j)) → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
  intro hCI D L Pm Tp hK hinj EX K _ _ _ Bs Df S P _ _ oc O H
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J),
      (IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i) ∧
      (IsLatIn ⊤ (O.Th v i) ∧ IsLatIn ⊤ (O.ThK v i)) ∧
      (O.Th v i ≤ O.Ms i ∧ (∀ g : P, (O.Th v i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Th v i) ∧
        O.σ v i ≠ 0 ∧ O.Th v i ≤ Formalism.EigenvalueLevelCeiling.sc (O.σ v i) (O.ThK v i)) := by
    intro v i
    obtain ⟨T, h, j, hj, p, inst, z, act, ℓ, hFK, hA, hFull, hxi, hO, hp, hLat, hSp, hH⟩ := H v i
    have ⟨h1, h2, h3, h4⟩ : WeightAlgebra.IsF' (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (fR Tp hK j).n ∧
        (kaR Tp hK j).n = (fR Tp hK j).n + Tp.TO * (lR Tp hK j).n ∧ WeightFamilies.dimY D j ≤ Tp.TO ∧ D.R.r ≤ (fR Tp hK j).n := by
      have hP : (fR Tp hK j).n = Tp.nP := rfl
      have hW : (lR Tp hK j).n = Tp.nWn := rfl
      refine ⟨isF'_fWt' _ _ _ _ _ _, ?_, ?_, ?_⟩
      · rw [hP, hW, ← Tp.split]; exact kaWt_n D hK _ j
      · rw [dimY_eq_flag' hj, ← Tp.Dp_eq]
        have := Tp.TO_40
        omega
      · rw [hP, Tp.nP_eq]
        have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
        nlinarith
    have hF := hFK.toFormTie (shortTh_fg _ hinj EX hp _ _ _ _ hLat.toIsLattice hH)
      (productsShort_rec hCI D T.toTop h j hj hFull.sh hO (hFull.lvA j hj 0) _ _ _ _ h1 h2 h3 h4 (kaWt_n _ _ _ _))
    exact ⟨supLattice_isLatIn_stable' D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hLat
        (levAct_mem_Mlat D T.toTop h j hj _ P ℓ act hA),
      theta_spans_isLatIn D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF hp h1 h2 h3 hLat.toIsLattice hSp hH,
      GlobalTheory.scaledSpan_clauses D _ _ j _ hinj EX p _ _ _ _ K Bs Df S P oc O v i z act hF h1 h2 h3 hH
        (levAct_theta hCI D T h j hj hFull hxi _ _ _ _ _ h1 h2 h3 h4 P ℓ act hA)⟩
  obtain ⟨v₀, -⟩ := exists_place3 K
  exact ⟨fun i => (key v₀ i).1,
    fun w _ => ⟨fun i => (key w i).2.1, fun i => (key (conjPl w) i).2.1⟩,
    fun w _ => ⟨fun i => (key w i).2.2, fun i => (key (conjPl w) i).2.2⟩⟩

end GlobalTheory.FormTies
