module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibTors

open GlobalTheory.Models GlobalTheory.UU

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_relDim_fibre (X : Scheme.{0}) (G : Over X) [GrpObj G] (hG : IsSemiAbelian G) (y : Sp ℂ ⟶ X) :
    ∃ n, SmoothOfRelativeDimension n ((Over.pullback y).obj G).hom := by
  have hG' : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback y).obj G).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback y).obj G).hom
  exact exists_dim_of_preconnected _ (((1 : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G).left) (default : PrimeSpectrum ℂ))

theorem lieBasis_card (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (y : Sp ℂ ⟶ X) (g n : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (v : Fin n → (epsR ℂ ⟶ (Over.pullback y).obj G)) (hv : IsLieBasis v) : n = g := by
  classical
  let G' := (Over.pullback y).obj G
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let ρ : epsPt y ⟶ Over.mk ((epsR ℂ).hom ≫ y) := Over.homMk (𝟙 _) rfl
  let T : (epsR ℂ ⟶ G') →* (epsPt y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G y) (epsR ℂ))
  have hT : ∀ a, (T a).left = a.left ≫ pullback.fst G.hom y := fun a => Category.id_comp _
  let U : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
  let ρ0 : Over.mk y ⟶ Over.mk (U.hom ≫ y) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ0).comp (toBaseHom (toBase_mul_pullback G y) U)
  have hη : η[G'].left ≫ pullback.fst G.hom y = (1 : Over.mk y ⟶ G).left := by
    have h' : (φ 1).left = (1 : U ⟶ G').left ≫ pullback.fst G.hom y := Category.id_comp _
    rw [map_one] at h'
    rw [h']
    congr 2
  have hTb : Function.Bijective T := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hT, ← hT, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (epsR ℂ).hom (Over.w p)) (pullback.lift_snd _ _ _),
        Over.OverMorphism.ext ((hT _).trans (pullback.lift_fst _ _ _))⟩
  have htan : ∀ a : epsR ℂ ⟶ G', IsTangent a ↔
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T a).left = (e 0).left := by
    intro a
    rw [h0, hT, ← hη]
    refine ⟨fun h => by rw [← Category.assoc, h], fun h => pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h
    · have e1 : a.left ≫ pullback.snd G.hom y = (epsR ℂ).hom := Over.w a
      have e2 : η[G'].left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w η[G']
      rw [Category.assoc, e1, e2]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.TanMod.spMap_comp']
      have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
        RingHom.ext fun _ => rfl
      rw [this]
      exact Spec.map_id _
  let Te := MulEquiv.ofBijective T hTb
  have hTe : ∀ a, Te a = T a := fun _ => rfl
  choose D hD _ using h1
  have hDmul : ∀ w w', D (w + w') = D w * D w' := fun w w' =>
    Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD (w + w'))
      (GlobalTheory.UnifCompare.isDerivAt0_mul (congrArg (·.left) h0) (hD w) (hD w')))
  have hDtan : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (D w).left = (e 0).left := fun w => (hD w).1
  let Dl : (Fin g → ℂ) → (epsR ℂ ⟶ G') := fun w => Te.symm (D w)
  have hTDl : ∀ w, T (Dl w) = D w := fun w => Te.apply_symm_apply (D w)
  have hDl_tan : ∀ w, IsTangent (Dl w) := fun w => (htan _).2 (by rw [hTDl]; exact hDtan w)
  have hDl_add : ∀ w w', Dl (w + w') = Dl w * Dl w' := fun w w' => by
    apply Te.injective
    rw [map_mul, hTe, hTe, hTe, hTDl, hTDl, hTDl, hDmul]
  have hDl_zero : Dl 0 = 1 := by
    have := hDl_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hDl_smul : ∀ (c : ℂ) w, (Dl (c • w)).left = spMap (epsScaleR c) ≫ (Dl w).left := by
    intro c w
    have hov : (spMap (epsScaleR c) ≫ (Dl w).left) ≫ G'.hom = (epsR ℂ).hom := by
      rw [Category.assoc, Over.w (Dl w)]
      show spMap _ ≫ spMap _ = spMap _
      rw [GlobalTheory.TanMod.spMap_comp']
      have hc : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) :=
        RingHom.ext fun a => by ext <;> simp [epsScaleR]
      rw [hc]
    let a : epsR ℂ ⟶ G' := Over.homMk (spMap (epsScaleR c) ≫ (Dl w).left) hov
    have ha : T a = D (c • w) := by
      refine Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique ?_ (hD (c • w)))
      rw [hT]
      have := GlobalTheory.UnifCompare.isDerivAt0_smul (hD w) c
      rw [← hTDl w, hT] at this
      show IsDerivAt0 _ _ ((spMap (epsScaleR c) ≫ (Dl w).left) ≫ pullback.fst G.hom y)
      rw [Category.assoc]
      exact this
    have : a = Dl (c • w) := by
      apply Te.injective
      rw [hTe, hTe, ha, hTDl]
    rw [← this]
    rfl
  have hDl_inj : ∀ w w', Dl w = Dl w' → w = w' := by
    intro w w' h
    have h' : D w = D w' := by rw [← hTDl, ← hTDl, h]
    exact (h2 (D w) (hDtan w)).unique (hD w) (h' ▸ hD w')
  have hDl_onto : ∀ a, IsTangent a → ∃ w, Dl w = a := by
    intro a ha
    obtain ⟨w, hw, -⟩ := h2 (T a) ((htan a).1 ha)
    refine ⟨w, Te.injective ?_⟩
    rw [Te.apply_symm_apply, hTe]
    exact Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD w) hw)
  have hsum : ∀ (k : ℕ) (f : Fin k → Fin g → ℂ), Dl (∑ i, f i) = (List.ofFn fun i => Dl (f i)).prod := by
    intro k
    induction k with
    | zero => intro f; simp [hDl_zero]
    | succ k ih =>
      intro f
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, hDl_add, ih]
  choose ws hws using fun i => hDl_onto (v i) (hv.1 i)
  have hcomb : ∀ c : Fin n → ℂ, IsLieComb c v (Dl (∑ i, c i • ws i)) := by
    intro c
    refine ⟨fun i => Dl (c i • ws i), fun i => ?_, hsum n _⟩
    rw [hDl_smul, hws]
  have hdet : ∀ (c : Fin n → ℂ) (a a' : epsR ℂ ⟶ G'), IsLieComb c v a → IsLieComb c v a' → a = a' := by
    rintro c a a' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
    rw [this]
  have hli : LinearIndependent ℂ ws := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have e1 := hcomb c
    rw [hc] at e1
    have e2 := hcomb 0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e2
    have := (hv.2 (Dl 0) (hDl_tan 0)).unique e1 e2
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ws) := by
    intro w _
    obtain ⟨c, hc, -⟩ := hv.2 (Dl w) (hDl_tan w)
    have := hDl_inj _ _ (hdet c _ _ hc (hcomb c))
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  simpa using hb.symm

end GlobalTheory.FibTors


open GlobalTheory.FibTors GlobalTheory.Models GlobalTheory.UU in
theorem GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro E _ _ _ H X t y g N e hN hexp _ _
  obtain ⟨hadd, hd1, hd2⟩ := hexp
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h1 : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro w
    obtain ⟨v, ⟨hv1, hv2⟩, hu⟩ := hd1 w
    refine ⟨Over.homMk v hv1.1, hv2, fun v' hv' => Over.OverMorphism.ext (hu v'.left ⟨⟨Over.w v', ?_⟩, hv'⟩)⟩
    refine hv'.1.trans ?_
    show (e 0).left = _
    rw [h0]
  have h2 : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro v hv
    exact hd2 v.left ⟨Over.w v, by rw [hv, h0]⟩
  obtain ⟨n, hn⟩ := exists_relDim_fibre X t.G t.semi y
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hn
  have hng := lieBasis_card X t.G y g n e hadd h1 h2 v hv
  subst hng
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let G : Over X := t.G
  let x := y
  let k := ℂ
  have h3 := GlobalTheory.laws3
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G t.semi
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension n G'.hom := hn
  obtain ⟨E⟩ := t.semi.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) t.PP t.cub
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e' := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e' a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e'.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E n N hG' dG' hN'
  refine ⟨e' '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, s0, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e'.surjective y
    have ht : s0 ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) t.PP _ t.cub c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e'.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e'.injective _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  first | exact @GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp | exact GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp | (intros; apply GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFrames
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.FlagEmb

theorem spMap_comp_spMap_same {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem spMap_pt {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {N : ℕ}
    (c : R →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)
    (ψ : A →+* B) :
    spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
  refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
  unfold pt
  congr 1
  exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)

theorem cell_pt_eq_of_tri (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type)
    [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X)
    (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P))
    (hc : IsCover β s V α c D) (hp : IsPlk β s V α c p0 p h) (k : Type) [Field k] (b b' : B) (w w' : Pm m)
    (ψ : CR m (V b) →+* k) (ψ' : CR m (V b') →+* k) (d : Let m → k)
    (hb : spMap ψ ≫ cbase m (V b) = spMap ψ' ≫ cbase m (V b')) (hd : ∀ z, d z ≠ 0)
    (ht : Tri (fun z => ψ ∘ uvec (c b) w z) (fun z => ψ' ∘ uvec (c b') w' z) d) :
    spMap ψ ≫ h b w = spMap ψ' ≫ h b' w' := by
  have hO : ψ.comp ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) =
      ψ'.comp ((MvPolynomial.C : _ →+* CR m (V b')).comp ((α b').comp β)) := by
    have e := congrArg (· ≫ s) hb
    simp only [cbase, Category.assoc, hc.ovr, spMap_comp_spMap_same] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine hp.ext _ _ _ ?_ fun en => ?_
  · rw [Category.assoc, Category.assoc, hp.base, hp.base, hb]
  · obtain ⟨hu, e⟩ := hp.plk b w en
    obtain ⟨hu', e'⟩ := hp.plk b' w' en
    rw [Category.assoc, Category.assoc, e, e', spMap_pt, spMap_pt]
    have hu2 := span_range_comp_eq_top _ hu' ψ'
    have key : ∀ (f g : O →+* k) (v v' : Fin (plN M en.1 + 1) → k) hv hv', f = g → (∃ u : kˣ, v' = u • v) →
        pt f v hv = pt g v' hv' := by
      rintro f g v v' hv hv' rfl hh
      exact (pt_eq_pt_iff f hv hv').2 hh
    refine key _ _ _ _ _ _ hO ⟨Units.mk0 (∏ l, d (en.2.1 l)) (Finset.prod_ne_zero_iff.2 fun l _ => hd _), ?_⟩
    rw [map_plk, map_plk, GlobalTheory.T.pluckerVector_blockTriangular_frame_change T m k M _ _ d en.1 en.2.1 ht en.2.2]
    rfl

end GlobalTheory.FlagEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellPointEqOfTriangularFramesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCell_point_eq_of_triangular_frames : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (k : Type) [Field k] b b' w w' (ψ : CR m (V b) →+* k) (ψ' : CR m (V b') →+* k) (d : Let m → k), spMap ψ ≫ cbase m (V b) = spMap ψ' ≫ cbase m (V b') → (∀ z, d z ≠ 0) → Tri (fun z => ψ ∘ uvec (c b) w z) (fun z => ψ' ∘ uvec (c b') w' z) d → spMap ψ ≫ h b w = spMap ψ' ≫ h b' w' := by
  first | exact @GlobalTheory.FlagEmb.cell_pt_eq_of_tri | exact GlobalTheory.FlagEmb.cell_pt_eq_of_tri | (intros; apply GlobalTheory.FlagEmb.cell_pt_eq_of_tri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinates
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UnifCoordPull

theorem exists_unif_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  intro R _ _ _ V _ _ _ hR hV ψ hψl G _ _ hG D A U W hWo hψ hker G' _ _ β hpb hab hrig hsym hamp hkt
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aV := admissibleBase_of_completeNormalLocalCharZero hV
  have hI : (maximalIdeal R).map ψ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff ψ a).2 ha
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G (spMap ψ))
  subst hbc

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgK := (isGrpPullback_pullback G' (jK V)).comp hpb
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdK : SmoothOfRelativeDimension A.g ((Over.pullback (jK V)).obj G').hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgK.1 hd
  have he := GlobalTheory.PolBaseChange.eSec_comm hpb
  let A' : PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback (jK V)).obj G'
      isAb := hab
      g := A.g
      smoothDim := hdK
      L := U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ψ))
      isLB := pull_isLB U.LG.isLB _
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  have eAm : IsMonHom (Iso.refl A'.A).hom := show IsMonHom (𝟙 A'.A) from inferInstance
  have wA : ∃ wA : LB.Iso (A'.L.pull (Iso.refl A'.A).hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ψ))), wA.IsGen := by
    have k : LBIso (A'.L.pull (𝟙 _)) (U.LG.L.pull (𝟙 _ ≫ pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫
        pullback.fst G.hom (specOf ψ))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ (𝟙 _), GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
    rw [Category.id_comp] at k
    exact k
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap ψ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hgen : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) ∈ (⟨W, hWo⟩ : (Sp R).Opens) := by
    have : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) =
        (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext rfl
    rw [this]; exact hker
  obtain ⟨D', hD, U', hLG, -, -⟩ := h4.unifBaseChange R V _ _ aR aV ψ hI D A G hG U ⟨W, hWo⟩
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre ⟨W, hWo⟩ ⟨_, hker⟩ hψ) hgen G' bc mbc A' rfl (Iso.refl _) eAm wA
    L' wL he gL rL
  refine ⟨D', A', U', hD.xe, ?_, fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩
  rw [hLG]
  exact LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩

end GlobalTheory.UnifCoordPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  first | exact @GlobalTheory.UnifCoordPull.exists_unif_psiCoord | exact GlobalTheory.UnifCoordPull.exists_unif_psiCoord | (intros; apply GlobalTheory.UnifCoordPull.exists_unif_psiCoord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormsLiftRulesCorrespondExtendedData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormsLiftRulesCorrespondExtendedData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.CuspExt


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem cusp_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {H H' : Host E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {U : ∀ j (σ : c.F →+* ℂ), Formalism.L2.Pj.Unf (Xo j) c σ r} {U' : ∀ j (σ : c'.F →+* ℂ), Formalism.L2.Pj.Unf (Xo' j) c' σ r}
    (hU : HEq U' U) {a a' : (E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) (j : ℕ) :
    Formalism.L2.Pj.Rul (Xo' j) c' = Formalism.L2.Pj.Rul (Xo j) c ∧
    (∀ (x : Formalism.L2.Pj.Rul (Xo j) c) (x' : Formalism.L2.Pj.Rul (Xo' j) c'), HEq x' x →
      (x' ∈ Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n' ↔ x ∈ Formalism.L2.Pj.cusp (Xo j) c (U j) a n)) ∧
    (∀ (x : Formalism.L2.Pj.Rul (Xo j) c) (x' : Formalism.L2.Pj.Rul (Xo' j) c') (h : x ∈ Formalism.L2.Pj.cusp (Xo j) c (U j) a n)
      (h' : x' ∈ Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n'), HEq x' x →
      HEq (⟨x', h'⟩ : Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n') (⟨x, h⟩ : Formalism.L2.Pj.cusp (Xo j) c (U j) a n)) := by
  subst hH ha hn
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hU
  refine ⟨rfl, fun x x' hx => ?_, fun x x' h h' hx => ?_⟩
  · obtain rfl := eq_of_heq hx; exact Iff.rfl
  · obtain rfl := eq_of_heq hx; exact HEq.rfl


set_option maxHeartbeats 2000000 in
theorem cusp_ext : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        z'.core.R ((j' : ℕ) + 1) = z.core.R ((j : ℕ) + 1) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r → (r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n ↔ r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (h : r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) (h' : r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n), HEq r' r →
          HEq (⟨r', h'⟩ : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) (⟨r, h⟩ : z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) := by
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj => ?_
  have hB := hE.1
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e

  obtain ⟨h1, h2, h3⟩ := hx.κ j' j' rfl
  have e1 : (z'.geo.κ j').aP = (z.geo.κ j').aP := eq_of_heq h1
  have e2 : (z'.geo.κ j').aM = (z.geo.κ j').aM := eq_of_heq h2
  have hw : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j') := by
    funext x
    unfold Formalism.L2.Pj.wtA
    rw [e1, e2]
    rfl
  obtain ⟨hR, hm, hs⟩ := cusp_heq (r := (w.st Z).toD7.R.r) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.U hw h3 ((j' : ℕ) + 1)
  exact ⟨hR, hm, hs⟩

end GlobalTheory.Mem.R3.CuspExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormsLiftRulesCorrespondExtendedDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_liftRules_correspond_extendedData : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        z'.core.R ((j' : ℕ) + 1) = z.core.R ((j : ℕ) + 1) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r → (r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n ↔ r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (h : r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) (h' : r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n), HEq r' r →
          HEq (⟨r', h'⟩ : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) (⟨r, h⟩ : z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) := by
  exact @GlobalTheory.Mem.R3.CuspExt.cusp_ext
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharactersOnLiftFormsExtendedData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharactersOnLiftFormsExtendedData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.ChiExt

theorem res_unique {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {P : Pl E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c u = χ.locK P k)
    (h' : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c' u = χ.locK P k) : c = c' := by
  ext1 u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have ha0 : (a : E) ≠ 0 := by
    intro h0
    have : a = 0 := by exact_mod_cast h0
    exact u.ne_zero (by rw [← ha, this, map_zero])
  exact (h a (Units.mk0 _ ha0) u rfl ha.symm).trans (h' a (Units.mk0 _ ha0) u rfl ha.symm).symm

theorem prod_eq {B B' : Base} (hB : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} (hf : HEq f' f)
    {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) (j : Fin B.R.m) (j' : Fin B'.R.m) (hj : (j : ℕ) = j')
    {Pg : Finset (Pl B.host.E)} {Pg' : Finset (Pl B'.host.E)} (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* G0 Pg B.R.r) (eG' : Gc B' px' ≃* G0 Pg' B'.R.r) (heG : HEq eG' eG)
    (c : ∀ PP : Pl B.host.E, (kP PP)ˣ →* ℂˣ) (c' : ∀ PP : Pl B'.host.E, (kP PP)ˣ →* ℂˣ)
    (h : ∀ PP ∈ Pg, ∀ (a : 𝓞 B.host.E) (k : B.host.Eˣ) (u : (kP PP)ˣ), (k : B.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c PP)⁻¹ u = (f.mu0 j).locK PP k)
    (h' : ∀ PP ∈ Pg', ∀ (a : 𝓞 B'.host.E) (k : B'.host.Eˣ) (u : (kP PP)ˣ), (k : B'.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c' PP)⁻¹ u = (f'.mu0 j').locK PP k)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    ∏ PP : Pg', ((c' PP.1 (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((c PP.1 (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  obtain rfl : f' = f := eq_of_heq hf
  obtain rfl : Pg' = Pg := eq_of_heq hPg
  obtain rfl : eG' = eG := eq_of_heq heG
  obtain rfl : g' = g := eq_of_heq hg
  obtain rfl : j = j' := Fin.ext hj
  refine Finset.prod_congr rfl fun PP _ => ?_
  have e : c' PP.1 = c PP.1 := inv_injective (res_unique (h' PP.1 PP.2) (h PP.1 PP.2))
  rw [e]
  rfl


set_option maxHeartbeats 2000000 in
theorem chi_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (((z'.R.toRealDat.FW j').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.R.toRealDat.FW j).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj φ hφ g g' hg => ?_
  apply RingHom.injective (w'.st Z').toD7.what₂.embLL
  refine (z'.pins.char.base.grp.chiW j' g').trans (Eq.trans ?_ ((hφ _).trans (z.pins.char.base.grp.chiW j g)).symm)
  have hC : z.R.toLevCh.C.mu0 j = f.mu0 j := by
    rw [z.lev.C, w.C_eq]; rfl
  have hC' : z'.R.toLevCh.C.mu0 j' = f'.mu0 j' := by
    rw [z'.lev.C, w'.C_eq]; rfl
  exact prod_eq hE.1 hf hpx j j' hj hx.Pg z.R.eG z'.R.eG hx.eG (z.R.chi ((j : ℕ) + 1)) (z'.R.chi ((j' : ℕ) + 1))
    (fun PP hP => hC ▸ z.lev.is.chi j PP hP) (fun PP hP => hC' ▸ z'.lev.is.chi j' PP hP) g g' hg

end GlobalTheory.Mem.R3.ChiExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharactersOnLiftFormsExtendedDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroupCharactersOnLiftForms_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (((z'.R.toRealDat.FW j').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.R.toRealDat.FW j).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  exact GlobalTheory.Mem.R3.ChiExt.chi_ext
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftExtendedDataEqMapSmallerField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftExtendedDataEqMapSmallerField
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem unipotentBaseLevelChar_map_coefficientField {E : Type} [Field E] [NumberField E] {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (ψ' : ∀ PP : Pl E, AddChar (kP PP) K') (h : ∀ PP c, ψ' PP c = φ (ψ PP c))
    (g : G0 Pg r) (hg : g ∈ (P0 Pg r ψ).H) (hg' : g ∈ (P0 Pg r ψ').H) :
      ((((P0 Pg r ψ').chi⁻¹ ⟨g, hg'⟩ : K'ˣ)) : K') = φ (((P0 Pg r ψ).chi⁻¹ ⟨g, hg⟩ : Kˣ) : K) := by
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
  congr 1
  unfold P0 LevelP.ofLocal at *
  dsimp only
  rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h _ _

theorem exists_int_of_mem_vGs {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : 𝓞 X.E ⧸ P.asIdeal) : ∃ b : ℤ, x = b := by
  classical
  have h : ∃ i, P ∈ Pr.vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := h
  have hc : Nat.card (𝓞 X.E ⧸ P.asIdeal) = Pr.g i := by
    rw [← hPr.vG_norm i P hi, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 X.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ (hPr.g_prime i).ne_zero)
  exact Formalism.L2.Col.owedC_exists_int (hPr.g_prime i) hc x

theorem baseLevels_correspond_weilAdditiveChars {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (I : ColIn B px) (I' : ColIn B' px')
    (hB : B'.toPre = B.toPre) (hpx : HEq px' px) (hPr : (B.primes px).Ok) (hw : I.Ch.WeilTied B.embLL B.host.xi0)
    (hw' : I'.Ch.WeilTied B'.embLL B'.host.xi0)
    (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) (e : Gc B px ≃* Gc B' px') (he : ∀ g, HEq (e g) g) :
    ∃ hP : lev0 I' = (lev0 I).map e.toMonoidHom, ∀ h : lev0 I,
      (((chr0 I')⁻¹ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : B'.LLˣ) : B'.LL) =
        φ (((chr0 I)⁻¹ h : B.LLˣ) : B.LL) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  have he' : e = MulEquiv.refl _ := MulEquiv.ext fun g => eq_of_heq (he g)
  subst he'
  refine ⟨(Subgroup.map_id _).symm, fun h => ?_⟩
  refine unipotentBaseLevelChar_map_coefficientField φ _ _ (psiC I) (psiC I') (fun PP c => ?_) h.1 h.2 h.2
  unfold psiC
  split_ifs with hP hQ hQ
  · obtain ⟨b, hb⟩ := exists_int_of_mem_vGs hPr hP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
    apply RingHom.injective (Base.embLL _)
    exact (hw' ⟨PP, hP⟩ c b hb).trans ((hφ _).trans (hw ⟨PP, hP⟩ c b hb)).symm
  · exact absurd hP hQ
  · exact absurd hQ hP
  · rw [AddChar.one_apply, AddChar.one_apply, map_one]


set_option maxHeartbeats 2000000 in
theorem lev_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∃ hP : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).P = ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P.map e.toMonoidHom, ∀ h : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P, ((((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).ψ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).ψ h : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ e he => ?_
  exact baseLevels_correspond_weilAdditiveChars w.I w'.I hE.1 hpx w.l.pr w.ok.weil w'.ok.weil φ hφ e he

end GlobalTheory.Mem.R3.DefLatBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftExtendedDataEqMapSmallerFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelLift_extendedData_eq_map_smallerField : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∃ hP : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).P = ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P.map e.toMonoidHom, ∀ h : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P, ((((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).ψ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).ψ h : (w.st Z).toD7.what₂.LL)) := by
  exact @GlobalTheory.Mem.R3.DefLatBC.lev_ext
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataIntertwinesFiniteGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataIntertwinesFiniteGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC


open _root_.Formalism.L2.Col in
theorem repCSD_lift_of_reading {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
    (S : GSD K) (S' : GSD K') (hS : S.Ok) (hS' : S'.Ok) {A A' : Type} [Group A] [Group A']
    (ρ : Representation K A S.EqFun) (ρ' : Representation K' A' S'.EqFun) {T T' : Type} (rd : S.V → T) (rd' : S'.V → T')
    (hrd' : Function.Injective rd') (L : (S.toCSD hS).Forms → (S'.toCSD hS').Forms)
    (hC : ∀ (f : (S.toCSD hS).Forms) (d : S.D) (d' : S'.D), HEq d' d →
      HEq (rd' ((((S'.res hS').symm (L f) : S'.EqFun) : S'.D → S'.V) d')) (rd ((((S.res hS).symm f : S.EqFun) : S.D → S.V) d)))
    (hex : ∀ d' : S'.D, ∃ d : S.D, HEq d' d) (a : A) (a' : A') (t : S.D → S.D) (t' : S'.D → S'.D)
    (hρ : ∀ (φ : S.EqFun) d, (ρ a φ : S.D → S.V) d = (φ : S.D → S.V) (t d))
    (hρ' : ∀ (φ : S'.EqFun) d, (ρ' a' φ : S'.D → S'.V) d = (φ : S'.D → S'.V) (t' d))
    (ht : ∀ (d : S.D) (d' : S'.D), HEq d' d → HEq (t' d') (t d)) (f : (S.toCSD hS).Forms) :
    S'.repCSD hS' ρ' a' (L f) = L (S.repCSD hS ρ a f) := by
  apply (S'.res hS').symm.injective
  apply Subtype.ext
  funext d'
  apply hrd'
  obtain ⟨d, hd⟩ := hex d'
  have e1 : (S'.res hS').symm (S'.repCSD hS' ρ' a' (L f)) = ρ' a' ((S'.res hS').symm (L f)) := by
    simp [GSD.repCSD]
  have e2 : (S.res hS).symm (S.repCSD hS ρ a f) = ρ a ((S.res hS).symm f) := by
    simp [GSD.repCSD]
  rw [e1, hρ']
  have h1 := hC f (t d) (t' d') (ht d d' hd)
  have h2 := hC (S.repCSD hS ρ a f) d d' hd
  rw [e2, hρ] at h2
  exact eq_of_heq (h1.trans h2.symm)

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC


open _root_.Formalism.L2.Col in
theorem decoratedLattice_translates_heq_of_eq_primes {X : Fields} {n r : ℕ} (h : r ≤ n) {SG Q Q' : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : Q' = Q) :
    (∀ d' : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q'), ∃ d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q), HEq d' d) ∧
    ∀ (g : G0 X.E SG r) (d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q)) (d' : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := uSG SG Q')), HEq d' d →
      HEq (((1 : UF X.E n), (extGLG Q' (diagonalEmbeddingProduct SG h g))⁻¹) • d') (((1 : UF X.E n), (extGLG Q (diagonalEmbeddingProduct SG h g))⁻¹) • d) := by
  subst hQ
  exact ⟨fun d' => ⟨d', HEq.rfl⟩, fun g d d' hd => by cases hd; rfl⟩


open _root_.Formalism.L2.Col in
theorem decoratedLattice_translates_heq_of_eq_preData (B B' : Base) (px : PreX B.toPre) (px' : PreX B'.toPre) (h : B'.toPre = B.toPre) (hp : HEq px' px)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E))
    (sel' : HeightOneSpectrum (𝓞 B'.fields.F) → HeightOneSpectrum (𝓞 B'.fields.E)) {S S' : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K S) (mu' : Tup B'.fields.F B'.fields.E B'.fields.K S')
    (hQ : QE sel (mu : Chr B.fields.F B.fields.E B.fields.K) = ∅)
    (hQ' : QE sel' (mu' : Chr B'.fields.F B'.fields.E B'.fields.K) = ∅) :
    (∀ d' : DecoSet (E := B'.fields.E) (n := B'.R.nV) (ST := ∅) (SG := rowSG (B'.primes px') sel' mu'),
      ∃ d : DecoSet (E := B.fields.E) (n := B.R.nV) (ST := ∅) (SG := rowSG (B.primes px) sel mu), HEq d' d) ∧
    ∀ (g : Gc B px) (g' : Gc B' px'), HEq g' g → ∀ (d : DecoSet (E := B.fields.E) (n := B.R.nV) (ST := ∅) (SG := rowSG (B.primes px) sel mu))
      (d' : DecoSet (E := B'.fields.E) (n := B'.R.nV) (ST := ∅) (SG := rowSG (B'.primes px') sel' mu')), HEq d' d →
      HEq (((1 : UF B'.fields.E B'.R.nV), (unipotentGroupBlockEmbedding (B'.primes px') sel' mu' (r_le_nV B'.R) g')⁻¹) • d')
        (((1 : UF B.fields.E B.R.nV), (unipotentGroupBlockEmbedding (B.primes px) sel mu (r_le_nV B.R) g)⁻¹) • d) := by
  cases B
  cases B'
  dsimp only at h
  subst h
  cases hp
  refine ⟨fun d' => (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).1 d', fun g g' hg d d' hd => ?_⟩
  have e := eq_of_heq hg
  subst e
  exact (decoratedLattice_translates_heq_of_eq_primes (r_le_nV _) (hQ'.trans hQ.symm)).2 _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC

set_option maxHeartbeats 8000000 in
theorem GlobalTheory.Mem.R3.DefLatBC.act_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ (g : Gc B w.px) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).r (e g) (L f) = L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).r g f)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ _ e he L _ hC g f0 => ?_
  have hP := GlobalTheory.Mem.R3.DefLatBC.decoratedLattice_translates_heq_of_eq_preData B B' w.px w'.px hE.1 hp w.I.sel w'.I.sel
    (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
    (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
    (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _) (Formalism.L2.Col.twistPrimes_trivialTuple_empty _ _)
  have hinj : Function.Injective fun v : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V => MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) v.1 :=
    (MvPolynomial.map_injective _ (B'.embLL : B'.fields.K →+* ℂ).injective).comp Subtype.val_injective
  exact GlobalTheory.Mem.R3.DefLatBC.repCSD_lift_of_reading (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.unipotentRightActionFormsV (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1))
    (fun v => MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) v.1) _ hinj (fun x => L x) hC hP.1 g (e g) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun d d' hd => hP.2 g (e g) (he g) d d' hd) f0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataIntertwinesFiniteGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsLift_extendedData_intertwines_finiteGroup : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ (g : Gc B w.px) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).r (e g) (L f) = L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).r g f)) := by
  exact GlobalTheory.Mem.R3.DefLatBC.act_ext
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepGroupElementOfChartLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepGroupElementOfChartLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT


set_option maxHeartbeats 4000000 in
theorem exists_stepElt_of_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ (((K (chOf c)).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ' : B.LLˣ) : B.LL) ∧ ∀ (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ.1 g := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb hchi κ
  obtain ⟨x, hxchi, ⟨q, hq⟩, hxκ⟩ := GlobalTheory.T.exists_levelElement_same_character_near_bad I hOk hPins l Z u a i hi bad Ch chOf K k hR c hchi κ
  have hl := hR.lev c x.1 q hq
  have hx : x.1 ∈ (fun β => (K β).lev.U) (chOf c) := x.2
  obtain ⟨κ', h3⟩ := hl.mp hx
  have hg := h3.1
  have hact := h3.2.1
  have hcos := h3.2.2
  refine ⟨κ', ⟨hg, hcos⟩, ?_, ?_⟩
  · rw [← hxchi]
    exact hR.chr c x κ' hg (hact ▸ hq)
  · intro P g hL
    obtain ⟨hm1, hm2, hn⟩ := GlobalTheory.T.levelElement_at_bad_primes_integral_and_near I hOk l Z u a i hi bad Ch chOf K k hR c x.1 κ' hg (hact ▸ hq) P
    obtain ⟨p, hp, hpN⟩ := hR.k_std (chOf c)
    exact GlobalTheory.T.adelicMatrixCongruence_move_rational_frame _ _ κ.1 x.1 (k (chOf c)) (fb P) _ (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).1)
      (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).2) hm1 hm2 (hxκ P) (hn g hL) (hfb P).1 (hfb P).2

end GlobalTheory.Mem.Col2.AdT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepGroupElementOfChartLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepGroupElement_of_chartLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ (((K (chOf c)).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ' : B.LLˣ) : B.LL) ∧ ∀ (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ.1 g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_stepElt_of_level | exact GlobalTheory.Mem.Col2.AdT.exists_stepElt_of_level | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_stepElt_of_level <;> assumption)
end
end
