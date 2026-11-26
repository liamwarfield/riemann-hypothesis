module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphism
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwistedGramMatricesMatch
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieLatticeAgree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEqOfCodimOneEq
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeStalkDvrTwistedModels
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomain
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistLatticeCompat

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwistedBundlesMatchModels
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpBundK

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem labels_side (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (Ω : Type) [Field Ω] (cst : c.F →+* Ω) (g : HostAut H) (s s' : CMType H ⊕ CMType H)
    (h : cst.comp (labelEmb c s') = (cst.comp (labelEmb c s)).comp g.s.toRingHom) : s.isLeft = s'.isLeft := _root_.GlobalTheory.CompanionTheory.Ar.CmpBund.labels_side E H l c Ω cst g s s' h

theorem span_coe_congr {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] (R R' : Subring Ω)
    (h : R = R') (T : Set V) : (Submodule.span R T : Set V) = Submodule.span R' T := by
  subst h; rfl

theorem isVB_of_iso (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : X' ≅ X) (he : ξ' ≫ e.hom = ξ) (V : Type) [AddCommGroup V] [Module Ω V]
    (L : Lat ξ V) (L' : Lat ξ' V) (r : ℕ) (W : Submodule Ω V)
    (hc : ∀ (q' : Cpt ξ') (h : genPt ξ ⤳ e.hom q'.1), regAt ξ' q' = regAt ξ ⟨e.hom q'.1, h⟩ ∧
      (L' q' : Set V) = L ⟨e.hom q'.1, h⟩) (hL : L.IsVB r W) : L'.IsVB r W := _root_.GlobalTheory.CompanionTheory.Ar.CmpBund.isVB_of_iso X X' Ω ξ ξ' e he V L L' r W hc hL

theorem isVB_comap_equiv (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (L : Lat ξ V) (φ : V' ≃ₗ[Ω] V)
    (r : ℕ) (W : Submodule Ω V) (hL : L.IsVB r W) : (L.comap φ.toLinearMap).IsVB r (W.comap φ.toLinearMap) := _root_.GlobalTheory.CompanionTheory.Ar.CmpBund.isVB_comap_equiv X Ω ξ V V' L φ r W hL

theorem patch_coe_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (V : Type) [AddCommGroup V] [Module Ω V]
    (M : LieModel G ξ V) (M' : LieModel G' ξ' V) (L : LB G.left) (L' : LB G'.left) (S : Finset ℕ) (n : ℕ → ℕ)
    (ρ : 𝓞 E →+* Module.End Ω V) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H)
    (q : Cpt ξ) (q' : Cpt ξ') (hR : regAt ξ' q' = regAt ξ q) (hlat : (M'.lat q' : Set V) = M.lat q)
    (hom : ∀ N, (M'.htOm L' N q' : Set (Module.Dual Ω V)) = M.htOm L N q) :
    (Lat.patch S (M'.eigLat ρ (σ s)) (fun p => htLabel M' L' (n p) ρ σ s) q' : Set V) =
      Lat.patch S (M.eigLat ρ (σ s)) (fun p => htLabel M L (n p) ρ σ s) q := _root_.GlobalTheory.CompanionTheory.Ar.CmpBund.patch_coe_eq E H X X' Ω ξ ξ' G G' V M M' L L' S n ρ σ s q q' hR hlat hom

theorem comap_span_equiv {Ω : Type} [Field Ω] {F F' : Type} [AddCommGroup F] [Module Ω F] [AddCommGroup F']
    [Module Ω F'] (R : Subring Ω) (φ : F' ≃ₗ[Ω] F) (T : Set F) :
    (Submodule.span R T).comap (φ.toLinearMap.restrictScalars R) = Submodule.span R (φ ⁻¹' T) := _root_.GlobalTheory.CompanionTheory.Ar.CmpBund.comap_span_equiv (Ω := Ω) (F := F) (F' := F') R φ T

theorem patch_comap_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (G : Over X) [GrpObj G]
    (F F' : Type) [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (M : LieModel G ξ F) (φ : F' ≃ₗ[Ω] F) (L : LB G.left) (S : Finset ℕ) (n : ℕ → ℕ)
    (ρ : 𝓞 E →+* Module.End Ω F') (ρ' : 𝓞 E →+* Module.End Ω F) (hρ : ∀ a v, φ (ρ a v) = ρ' a (φ v))
    (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H) :
    (Lat.patch S (M.eigLat ρ' (σ s)) (fun p => htLabel M L (n p) ρ' σ s)).comap φ.toLinearMap =
      Lat.patch S ((Flat.lieModelOfEquiv M φ).eigLat ρ (σ s))
        (fun p => htLabel (Flat.lieModelOfEquiv M φ) L (n p) ρ σ s) := _root_.GlobalTheory.CompanionTheory.Ar.CmpBund.patch_comap_equiv E H X Ω ξ G F F' M φ L S n ρ ρ' hρ σ s

theorem sabMap_congr_base {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (h : f = f') (m : SABMap t' t f) :
    ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

theorem htOm_eq_of_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S₀ : Scheme.{0}) (s₀ : S₀ ⟶ Sp B) (o₀ : Obj D l b s₀)
    (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (x : Sp Ω ⟶ S₀)
    (t t' : SAB H X) (tΩ : SAB H (Sp Ω)) (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ)
    (u : SABMap tΩ o₀.t x) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V)
    (M' : LieModel t'.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n →
    (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, v.left ≫ m.φ = (M.pt e).left ∧ v.left ≫ m'.φ = (M'.pt e).left) →
    (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) →
    M'.htOm t'.PP.L n q = M.htOm t.PP.L n q := by
  intro E _ _ _ H D l B _ b S₀ s₀ o₀ g X Ω _ _ ξ x t t' tΩ m m' u V _ _ M M' n q hgen hn hFT htie hq
  obtain ⟨o, ⟨mo⟩⟩ := GlobalTheory.ObjPull.objPull_of_pol
    (GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally) E H D l B B b b (RingHom.id B)
    S₀ (Sp Ω) s₀ (x ≫ s₀) x rfl rfl (by simp [spMap]) o₀
  obtain ⟨n₀, -⟩ := sabMap_congr_base (Category.id_comp x).symm mo.toSABMap
  obtain ⟨c, -⟩ := sabCancel pullCubCancel E H S₀ (Sp Ω) (Sp Ω) o₀.t tΩ o.t x (𝟙 _) u n₀
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H X (Sp Ω) (Sp Ω) t tΩ o.t ξ (𝟙 _) m c
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H X (Sp Ω) (Sp Ω) t' (twistSAB tΩ g) (twistSAB o.t g) ξ (𝟙 _) m'
    (twistMap c g)
  obtain ⟨k₁, hk₁⟩ := sabMap_congr_base (Category.id_comp ξ) n₁
  obtain ⟨k₂, hk₂⟩ := sabMap_congr_base (Category.id_comp ξ) n₂
  refine PositivityTheory.UnitarySelfGeneration.lattice_stalk_dvr_twisted_models E H D l B b g X Ω ξ (x ≫ s₀) o t t' k₁ k₂ V M M' n q hgen hn hFT (fun e => ?_) hq
  obtain ⟨w, hw, hw'⟩ := htie e
  have hp := c.cart.1
  let v0 : (epsAt (𝟙 (Sp Ω))).left ⟶ o.t.G.left :=
    hp.lift w.left (epsAt (𝟙 (Sp Ω))).hom (by rw [Over.w w, Category.comp_id])
  have hv0 : v0 ≫ c.φ = w.left := hp.lift_fst _ _ _
  refine ⟨Over.homMk v0 (hp.lift_snd _ _ _), ?_, ?_⟩
  · show v0 ≫ k₁.φ = _
    rw [hk₁, hn₁, ← Category.assoc, hv0, hw]
  · show v0 ≫ k₂.φ = _
    rw [hk₂, hn₂]
    exact (Category.assoc v0 c.φ m'.φ).symm.trans ((congrArg (· ≫ m'.φ) hv0).trans hw')

theorem bund : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      (∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v)) →
      ∀ s s', A'.emb s' = (A.emb s).comp g.s.toRingHom → ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li),
        v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V s' q := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
    t tΩ k m mA' u u' M₁ φ E1 E2 E3 hk htie hFT hT hact s s' hss'

  have hside : s.isLeft = s'.isLeft :=
    labels_side E H l c Ω A.cst g s s' (by have h := hss'; unfold HodgeCpt.emb at h; rwa [← hc] at h)

  haveI : IsLocallyNoetherian A'.X := by
    have := (GlobalTheory.T.regAt_noetherian_model_noetherian A'.X Ω A'.ξ ℤ ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) A'.tie).2 A'.all
    haveI := this.1
    infer_instance
  let M₂ : LieModel A'.t.G A'.ξ A.Li := Flat.lieModelOfEquiv A'.M φ
  have hlat : M₁.lat = M₂.lat :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_of_normal A'.X Ω A'.ξ A'.tie.gen t.G A'.t.G tΩ.G m.φ mA'.φ t.semi A'.t.semi m.cart mA'.cart A.Li M₁ M₂
      htie inferInstance (fun x => ⟨A'.normal.isDomain_stalk x, A'.normal.isIntegrallyClosed_stalk x⟩)
  haveI : CharZero Ω := (RingHom.charZero_iff A.cst.injective).1 inferInstance
  have heig : (eigSp A'.ρ (A'.emb s')).comap φ.toLinearMap = eigSp A.ρ (A.emb s) := by
    rw [← eigSp_comp_ringEquiv Ω A.Li (𝓞 E) A.ρ g.s (A.emb s), ← hss']
    ext v
    simp only [eigSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]
    refine forall_congr' fun a => ?_
    rw [show (A.ρ.comp g.s.toRingHom) a v = A.ρ (g.s a) v from rfl, ← φ.injective.eq_iff, hact, map_smul]
  have hom : ∀ q : Cpt A'.ξ, (∃ _ : IsDomain (A'.X.presheaf.stalk q.1),
      IsDiscreteValuationRing (A'.X.presheaf.stalk q.1)) →
      ∀ p ∈ S, M₂.htOm A'.t.PP.L (p ^ A.R p) q = M₁.htOm t.PP.L (p ^ A.R p) q := fun q hq p hp =>
    htOm_eq_of_dvr E H D l _ (baseKA l) _ _ Y.oF g A'.X Ω A'.ξ x t A'.t tΩ m mA' u A.Li M₁ M₂ (p ^ A.R p) q
      A'.tie.gen (pow_pos (A.S_prime p hp).pos _) (hFT _ (A.tors p hp)) htie hq
  let La : Lat A'.ξ A.Li :=
    Lat.patch S (M₁.eigLat A.ρ (A.emb s)) (fun p => htLabel M₁ t.PP.L (p ^ A.R p) A.ρ A.emb s)
  let Lb : Lat A'.ξ A.Li := (A'.V s').comap φ.toLinearMap
  have hLb : Lb = Lat.patch S (M₂.eigLat (A.ρ.comp g.s.toRingHom) (A'.emb s'))
      (fun p => htLabel M₂ A'.t.PP.L (p ^ A'.R p) (A.ρ.comp g.s.toRingHom) A'.emb s') :=
    patch_comap_equiv E H A'.X Ω A'.ξ A'.t.G A'.Li A.Li A'.M φ A'.t.PP.L S (fun p => p ^ A'.R p)
      (A.ρ.comp g.s.toRingHom) A'.ρ hact A'.emb s'
  have hcar : ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), (La q : Set A.Li) = A.V s ⟨e.hom q.1, h⟩ :=
    fun q h => patch_coe_eq E H A.X A'.X Ω A.ξ A'.ξ A.t.G t.G A.Li A.M M₁ A.t.PP.L t.PP.L S
      (fun p => p ^ A.R p) A.ρ A.emb s ⟨e.hom q.1, h⟩ q (hT q h).1 (hT q h).2.1 (hT q h).2.2
  have hvbA : La.IsVB (labelRk D s) (eigSp A.ρ (A.emb s)) :=
    isVB_of_iso A.X A'.X Ω A.ξ A'.ξ e hξ A.Li (A.V s) La _ _ (fun q h => ⟨(hT q h).1, hcar q h⟩) (A.vb s)
  have hrk : labelRk D s' = labelRk D s := by
    rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at hside <;> rfl
  have hvbB : Lb.IsVB (labelRk D s) (eigSp A.ρ (A.emb s)) := by
    have h1 := isVB_comap_equiv A'.X Ω A'.ξ A'.Li A.Li (A'.V s') φ _ _ (A'.vb s')
    rw [hrk] at h1
    rw [← heig]
    exact h1
  have hagree : ∀ q ∈ (Set.univ : Set (Cpt A'.ξ)), La q = Lb q := by
    refine GlobalTheory.T.lattice_eq_of_codim_one_eq A'.X Ω A'.ξ A'.tie.gen Set.univ (fun _ _ _ _ => trivial)
      (fun p _ => A'.normal.isIntegrallyClosed_stalk p.1) A.Li La Lb (labelRk D s) (eigSp A.ρ (A.emb s)) hvbA hvbB ?_
    intro q _ hq1
    have hdvr := GlobalTheory.T.normal_codim_one_stalk_dvr A'.X (fun x => ⟨A'.normal.isDomain_stalk x, A'.normal.isIntegrallyClosed_stalk x⟩) q.1 hq1
    rw [hLb]
    simp only [La, Lat.patch]
    split_ifs with hF
    · refine iInf_congr fun p => iInf_congr fun hp => iInf_congr fun _ => ?_
      rw [hR p hp]
      have key := GlobalTheory.T.hodge_tate_dual_eq_of_omega_eq E g.s A'.X Ω A'.ξ t.G A'.t.G t.PP.L A'.t.PP.L A.Li M₁ M₂ (p ^ A.R p)
        (p ^ A.R p) A.ρ (A.emb s) q (hom q hdvr p hp)
      rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at hside
      · simp only [htLabel]; rw [hss']; exact key.2.symm
      · simp only [htLabel]; rw [hss']; exact key.1.symm
    · simp only [LieModel.eigLat, Lat.inter]
      rw [hss', eigSp_comp_ringEquiv, hlat]
  intro q h v
  have e1 : v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ v ∈ La q := by
    rw [← SetLike.mem_coe, ← hcar q h, SetLike.mem_coe]
  rw [e1, hagree q trivial]
  exact Iff.rfl

end GlobalTheory.CompanionTheory.Ar.CmpBundK

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem twisted_bundles_match_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      (∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v)) →
      ∀ s s', A'.emb s' = (A.emb s).comp g.s.toRingHom → ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li),
        v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V s' q :=
  @GlobalTheory.CompanionTheory.Ar.CmpBundK.bund

end PositivityTheory.UnitarySelfGeneration
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpTiedK

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem cmpHodgeTied : HodgeComparisonCompatibility := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
  obtain ⟨t, tΩ, k, m, mA, mA', u, u', M₁, φ, hmA, E1, E2, E3, hk, htie, hT, hL⟩ :=
    GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
  have E1' : m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ := by rw [← Category.assoc, ← hmA, E1]
  have hact : ∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v) :=
    GlobalTheory.T.lie_model_twisted_comparison E H g Ω A.X A'.X A.ξ A'.ξ A.t A'.t tΩ mA mA' A.Li A'.Li A.M A'.M A.ρ A'.ρ φ A.act A'.act
      (fun v => by
        obtain ⟨w, hw, hw'⟩ := htie v
        exact ⟨w, by rw [hmA, ← Category.assoc, hw, hk], hw'⟩)
  refine ⟨φ, fun v => ?_, hact,
    PositivityTheory.UnitarySelfGeneration.twisted_bundles_match_models E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR t tΩ k m mA' u u' M₁ φ E1' E2 E3 hk htie hT hL hact,
    fun z => ⟨GlobalTheory.T.hodge_component_twist_frame_compat E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR z, fun hz r b Γ =>
      (GlobalTheory.T.lie_model_base_change_iso_compat E H A.X A'.X e Ω A.ξ A'.ξ A.t t k A.Li A.M M₁ hξ hk z r b Γ).symm.trans
        (PositivityTheory.UnitarySelfGeneration.twisted_gram_matrices_match E H D l Xo c O O' β β' Y Y' g Φ n S Ω K J y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR t tΩ k m mA' u u' M₁ φ E1' E2 E3 hk htie hT hL z hz r b Γ)⟩⟩
  obtain ⟨w, hw, hw'⟩ := htie v
  have h1 : u'.φ ≫ Y'.oF.t.G.hom = (twistSAB tΩ g).G.hom ≫ x' := u'.cart.1.w
  have h2 : u.φ ≫ Y.oF.t.G.hom = tΩ.G.hom ≫ x := u.cart.1.w
  have key : u'.φ ≫ Y'.oF.t.G.hom ≫ pullback.snd _ _ = u.φ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ := by
    rw [reassoc_of% h1, reassoc_of% h2, hs]
    rfl
  refine ⟨w.left ≫ u.φ, w.left ≫ u'.φ, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [← E1', ← hk v, ← hw]
    simp only [Category.assoc]
  · calc (w.left ≫ u'.φ) ≫ Y'.m.φ = w.left ≫ (u'.φ ≫ Y'.m.φ) := Category.assoc _ _ _
      _ = w.left ≫ (mA'.φ ≫ A'.m.φ) := congrArg (fun f => w.left ≫ f) E2.symm
      _ = (w.left ≫ mA'.φ) ≫ A'.m.φ := (Category.assoc _ _ _).symm
      _ = _ := by rw [hw']
  · calc (w.left ≫ u'.φ) ≫ Y'.m0.toSABMap.φ = w.left ≫ (u'.φ ≫ Y'.m0.toSABMap.φ) := Category.assoc _ _ _
      _ = w.left ≫ (u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ) := congrArg (fun f => w.left ≫ f) E3
      _ = _ := (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans ((congrArg (fun f => w.left ≫ f) key).trans (Category.assoc _ _ _).symm)

end GlobalTheory.CompanionTheory.Ar.CmpTiedK

namespace PositivityTheory.UnitarySelfGeneration

theorem cmpHodgeTiedAlt : GlobalTheory.CompanionTheory.Ar.HodgeComparisonCompatibility :=
  @GlobalTheory.CompanionTheory.Ar.CmpTiedK.cmpHodgeTied

end PositivityTheory.UnitarySelfGeneration
