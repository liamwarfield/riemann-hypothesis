module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddingSectionsSpanGeometricFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsGenericSpreadOut
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescended

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfGenerization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.CharZeroPts

theorem exists_generization {o : Type} [CommRing o] [IsDomain o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Flat s]
    (p : S) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      x ≫ s = spMap β ∧ ∀ u, x u ⤳ p := by
  let ξ : Sp o := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o)
  have hξ : ξ ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨q, hq, hq'⟩ := Flat.generalizingMap s hξ
  obtain ⟨K, _, _, x, hx⟩ := FinEt.exists_algClosed_point S q
  have hx' : ∀ u, x u = q := fun u => by
    have : x u ∈ Set.range x := ⟨u, rfl⟩
    rwa [hx] at this
  let β : o →+* K := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have hinj : Function.Injective β := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have e : spMap β (default : PrimeSpectrum K) = ξ := by
      rw [← hβ]
      exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg s (hx' _)).trans hq')
    have e' : a ∈ (spMap β (default : PrimeSpectrum K)).asIdeal := by
      show β a ∈ (default : PrimeSpectrum K).asIdeal
      rw [ha]; exact zero_mem _
    rw [e] at e'
    exact e'
  exact ⟨K, inferInstance, inferInstance, charZero_of_injective_ringHom hinj, x, β, hβ, fun u => (hx' u).symm ▸ hq⟩

variable {S : Scheme.{0}}

abbrev toB {T : Scheme.{0}} (x : T ⟶ S) : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)

theorem smoothOfRelativeDimension_of_generization {X : Scheme.{0}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f]
    (g : ℕ) (h : ∀ y : X, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ X), (∀ u, z u ⤳ y) ∧
      ∀ m, SmoothOfRelativeDimension m (pullback.snd f (z ≫ f)) → m = g) : SmoothOfRelativeDimension g f := by
  choose n W hW hd using H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  obtain ⟨k, _, z, hz, hg⟩ := h y
  have : ConnectedSpace ↥(pullback f (z ≫ f)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (z ≫ f) _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback f (z ≫ f) := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd f (z ≫ f)) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst f (z ≫ f) = z := pullback.lift_fst _ _ _
    have e' := congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e
    exact (congrArg (fun u => u ∈ W y) e').mpr ((hz _).mem_open (W y).isOpen (hW y)))
  rw [← hg m hm, ← e₁]
  exact hd y

theorem weilIs_of_generization (hL : Out.Laws) (P : Out.PolAV S) (n : ℕ) (x y : Out.baseOver S ⟶ P.A) (c : Γ(S, ⊤)ˣ)
    (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) (hx : x ^ n = 1) (hy : y ^ n = 1) (hc : c ^ n = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      Out.WeilIs P.A P.L n (toB z ≫ x) (toB z ≫ y) (Units.map z.appTop.hom.toMonoidHom c)) :
    Out.WeilIs P.A P.L n x y c := by
  obtain ⟨U, hU, H⟩ := exists_clopen_weilIs_iff hL S P n (Out.baseOver S) x y c hn hu hx hy hc
  have := (H _ (𝟙 _)).2 (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨K, _, z, hz, hw⟩ := h p
    exact (hz (default : PrimeSpectrum K)).mem_closed hU ((H _ (toB z)).1 hw ⟨_, rfl⟩))
  rw [Category.id_comp, Category.id_comp] at this
  convert this
  ext
  simp

theorem torsion_basis_of_generization (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A))
    (hA : IsAbelianScheme A) (hk : 0 < k) (hu : IsUnit (k : Γ(S, ⊤))) (hpt : ∀ i, pt i ^ k = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
        ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A) (hy : y ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB x ≫ pt i) (fun i => (c i).val) = y := by
  let Sg : Set S := {p | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S),
    p ∈ Set.range z ∧ ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
      ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y}
  refine torsion_basis_of_dense S A k r pt Sg hA hk hu hpt ?_ (fun p hp => hp) K x y hy
  intro p
  obtain ⟨K, _, _, z, hz, H⟩ := h p
  exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure
    (subset_closure ⟨K, inferInstance, inferInstance, z, ⟨_, rfl⟩, H⟩)

end GlobalTheory.CharZeroPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MonoOfGeomPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FibreEmbed

theorem mono_of_geom_points {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h₁ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y')
    (h₂ : ∀ (k : Type) [Field k] [IsAlgClosed k] (w : Sp (DualNumber k) ⟶ X),
      w ≫ f = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w ≫ f →
        w = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w) : Mono f := by
  have hu : FormallyUnramified f := TangentCrit.formallyUnramified_of_tangent f h₂
  have hs : Surjective (pullback.diagonal f) := by
    refine ((tfae_universallyInjective f).out 2 4).1 fun (k : Type) [Field k] y y' e => ?_
    let x : Sp (AlgebraicClosure k) ⟶ Sp k := spMap (algebraMap k (AlgebraicClosure k))
    have : Surjective x :=
      ⟨fun z => ⟨(default : PrimeSpectrum (AlgebraicClosure k)), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Epi x := Flat.epi_of_flat_of_surjective x
    refine (cancel_epi x).1 (h₁ _ _ _ ?_)
    rw [Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]; rfl

theorem sp_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem projRep_of_fibres : ∀ (R σ : Type) [CommRing R] [Finite σ] (X : Scheme.{0}) (s : X ⟶ Sp R) (M : LB X) (th : σ → M.Sec), M.IsLB → IsProper s → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K), ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (s' : X' ⟶ Sp K) (M' : LB X') (th' : σ → M'.Sec) (I : Ideal (MvPolynomial σ K)), IsPullback π s' s (spMap x) ∧ ProjRep I s' M' th' ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X') (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ π) w) → ProjRep (idealOf s M th (𝟙 X)) s M th := by
  intro R σ _ _ X s M th hM hs H
  obtain ⟨P, sP, MP, thP, -, hP, -⟩ := GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat R σ ⊥ 0 (by
    intro F hF e
    rw [Ideal.mem_bot] at hF
    simp [hF])
  have hPp : IsProper sP := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R σ ⊥ (Over.mk sP) MP thP hP).2.1
  obtain ⟨f, hf, -, hfc, -⟩ := GlobalTheory.T.exists_scheme_map_of_projective_coordinates R σ ⊥ P X sP s MP M thP th hP hM (by
    intro R' _ β y v hy hv
    refine ⟨?_, fun F hF => by rw [Ideal.mem_bot] at hF; simp [hF]⟩
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field m
    let K := AlgebraicClosure (R' ⧸ m)
    let φ : R' →+* K := (algebraMap (R' ⧸ m) K).comp (Ideal.Quotient.mk m)
    obtain ⟨X', π, s', M', th', I, hpb, hrep, hc⟩ := H K (φ.comp β)
    have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ hM hv).1 K φ
    have e : (spMap φ ≫ y) ≫ s = 𝟙 _ ≫ spMap (φ.comp β) := by
      rw [Category.assoc, hy, sp_comp, Category.id_comp]
    have h2 := (hrep.2.1 K (RingHom.id K) (hpb.lift _ _ e) _ (by rw [hpb.lift_snd, sp_id])
      ((hc K _ _).2 (by rw [hpb.lift_fst]; exact h1))).1
    have h3 : Ideal.span (Set.range fun i => φ (v i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      have : Ideal.Quotient.mk m (v i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span ⟨i, rfl⟩))
      simp [φ, this]
    exact bot_ne_top (h3.symm.trans h2))
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (T : Type) [CommRing T] [IsLocalRing T] (c : K →+* T)
      (x : Sp K ⟶ Sp R) (y y' : Sp T ⟶ X), y ≫ s = spMap c ≫ x → y ≫ f = y' ≫ f → y = y' := by
    intro K _ _ T _ _ c x y y' hy e
    obtain ⟨x, rfl⟩ : ∃ g : R →+* K, spMap g = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
    have hy' : y' ≫ s = spMap c ≫ spMap x := by
      rw [← hy, ← hf, ← Category.assoc, ← e, Category.assoc]
    obtain ⟨X', π, s', M', th', I, hpb, hrep, hc⟩ := H K x
    obtain ⟨v, hv⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally X M σ th hM).1 T y
    have hv' : SecCoord M th y' v := (hfc T y' v).2 (e ▸ (hfc T y v).1 hv)
    have a1 : SecCoord M' th' (hpb.lift _ _ hy) v := (hc T _ _).2 (by rw [hpb.lift_fst]; exact hv)
    have a2 : SecCoord M' th' (hpb.lift _ _ hy') v := (hc T _ _).2 (by rw [hpb.lift_fst]; exact hv')
    obtain ⟨u1, u2⟩ := hrep.2.1 T c _ v (hpb.lift_snd _ _ hy) a1
    have := (hrep.2.2 T c v u1 u2).unique ⟨hpb.lift_snd _ _ hy, a1⟩ ⟨hpb.lift_snd _ _ hy', a2⟩
    rw [← hpb.lift_fst _ _ hy, this, hpb.lift_fst]
  have : IsProper (f ≫ sP) := hf ▸ hs
  have : IsProper f := IsProper.of_comp f sP
  have hm : Mono f := by
    refine mono_of_geom_points f (fun k _ _ y y' e => key k k (RingHom.id k) (y ≫ s) y y' ?_ e)
      fun k _ _ w hw => key k (DualNumber k) (algebraMap _ _) (TangentCrit.dualPt k ≫ w ≫ s) _ _ ?_ ?_
    · rw [sp_id, Category.id_comp]
    · have := congrArg (· ≫ sP) hw
      simpa only [Category.assoc, hf] using this
    · simpa only [Category.assoc] using hw
  have hci : IsClosedImmersion f := (IsClosedImmersion.iff_isProper_and_mono f).2 ⟨‹_›, hm⟩
  have := GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme R σ ⊥ P X sP MP thP f M th hP hci hM hfc
  rwa [hf] at this

end GlobalTheory.FibreEmbed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.EmbedLocal

theorem exists_emb_projRep :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ :=
  of_parts GlobalTheory.exists_emb_locally GlobalTheory.T.thetaEmbeddingSections_baseChange_affine GlobalTheory.T.embedding_sections_span_geometric_fibre GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning GlobalTheory.FibreEmbed.projRep_of_fibres

end GlobalTheory.ZM.EmbedLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_multiplicationPullback_theta_embedding : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ := by
  first | exact @GlobalTheory.ZM.EmbedLocal.exists_emb_projRep | exact GlobalTheory.ZM.EmbedLocal.exists_emb_projRep | (intros; apply GlobalTheory.ZM.EmbedLocal.exists_emb_projRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SpreadLevel

theorem pushHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) :=
  ⟨fun x y hxy =>
      Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y])),
    fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem map_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S} {T' : Over S'}
    (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (y : Fin n → (T' ⟶ G')) (a : Fin n → ℕ) :
    ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  simp only [Out.linComb, map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem unitS_comp {o : Type} [CommRing o] {S S' : Scheme.{0}} (f : S' ⟶ S) (s : S ⟶ Sp o) (u : oˣ) :
    unitS (f ≫ s) u = Units.map f.appTop.hom.toMonoidHom (unitS s u) := by
  apply Units.ext
  show (f ≫ s).appTop.hom _ = f.appTop.hom (s.appTop.hom _)
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem unitS_spMap_pow {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (k : ℕ) (h : β u ^ k = 1) :
    unitS (spMap β) u ^ k = 1 := by
  apply Units.ext
  have e : (spMap β).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (β u) :=
    (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  rw [Units.val_pow_eq_pow_val]
  show (spMap β).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u) ^ k = 1
  rw [e, ← map_pow, h, map_one]

theorem exists_extension (hL : Out.Laws) {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
    {K : Type} [Field K] {S : Scheme.{0}} [PreconnectedSpace S] (s : S ⟶ Sp o) (j : Sp K ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {sK : Sp K ⟶ Sp o} (hs : j ≫ s = sK) (hk : 0 < k)
    (hζ : unitS s b.ζ ^ k = 1) (t : TObj g k J b sK)
    (P : Out.PolAV S) (φ : t.A.left ⟶ P.A.left) (hg : P.g = g) (hφ : IsGrpPullback t.A P.A j φ)
    (hφL : LBIso t.L (P.L.pull φ)) (p : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (hp : ∀ i, (t.pt i).left ≫ φ = j ≫ (p i).left) (a : J → (P.A ⟶ P.A))
    (ha : ∀ i, (t.act i).left ≫ φ = φ ≫ (a i).left) : ∃ t' : TObj g k J b s, TMap t t' j := by
  subst hs
  have := P.isAb.proper
  have := P.isAb.smooth
  have := P.isAb.comm
  have hku : IsUnit (k : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rwa [map_natCast] at this
  let h : Over.mk ((Out.baseOver (Sp K)).hom ≫ j) ⟶ Out.baseOver S := Over.homMk j (by simp)
  have hpush : ∀ i, pushHom hφ _ (t.pt i) = h ≫ p i := fun i => Over.OverMorphism.ext (hp i)
  have tors : ∀ i, p i ^ k = 1 := fun i => by
    have e : h ≫ (p i ^ k) = h ≫ (1 : Out.baseOver S ⟶ P.A) := by
      have e₁ := map_pow (preHom (G := P.A) h) (p i) k
      have e₂ := map_one (preHom (G := P.A) h)
      refine e₁.trans (Eq.trans ?_ e₂.symm)
      show (h ≫ p i) ^ k = 1
      rw [← hpush, ← map_pow, t.torsion, map_one]
    exact Over.OverMorphism.ext (ExtUnique.hom_ext_of_dominant P.A.hom (by rw [Over.w, Over.w]) j
      (congrArg CommaMorphism.left e))
  refine ⟨{ A := P.A, ab := P.isAb, dim := hg ▸ P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
            ample := P.ample, ktriv := P.ktriv, pt := p, torsion := tors, bij := ?_, pairing := fun i i' => ?_
            act := a, hom := fun i => ?_ }, φ, hφ, hφL, hp, ha⟩
  · refine GlobalTheory.torsion_basis_of_dense S P.A k (2 * g) p (Set.range j) P.isAb hk hku tors j.denseRange ?_
    rintro _ ⟨z, rfl⟩
    let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K _)
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    refine ⟨AlgebraicClosure K, inferInstance, inferInstance, x₀ ≫ j,
      ⟨IsLocalRing.closedPoint _, (Scheme.Hom.comp_apply _ _ _).trans (congrArg j (Subsingleton.elim _ _))⟩,
      fun y hy => ?_⟩
    have hb := pushHom_bijective hφ (Over.mk x₀)
    obtain ⟨y', rfl⟩ := hb.2 y
    have hy' : y' ^ k = 1 := hb.1 (by rw [map_pow, map_one]; exact hy)
    refine (existsUnique_congr fun c => ?_).1 (t.bij _ x₀ y' hy')
    rw [← hb.1.eq_iff, map_linComb]
    refine Eq.congr_left (congrArg (fun q => Out.linComb q _) (funext fun i => Over.OverMorphism.ext ?_))
    show (x₀ ≫ (t.pt i).left) ≫ φ = (x₀ ≫ j) ≫ (p i).left
    rw [Category.assoc, hp, Category.assoc]
  · obtain ⟨U, hU, H⟩ := GlobalTheory.exists_clopen_weilIs_iff hL S P k (Out.baseOver S) (p i) (p i')
      (unitS s b.ζ ^ Out.stdSymp g i i') hk hku (tors i) (tors i')
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow])
    have w := (GlobalTheory.weilIs_grpPullback_of_comm S (Sp K) P.A t.A j φ P.L t.L P.isLB t.isLB hφ hφL (Out.baseOver (Sp K))
      k (t.pt i) (t.pt i') (h ≫ p i) (h ≫ p i') _ (hp i).symm (hp i').symm).1 (t.pairing i i')
    rw [unitS_comp, ← map_zpow] at w
    have hr : Set.range h.left ⊆ U := (H _ h).1 w
    have hall : (U : Set (Out.baseOver S).left) = Set.univ :=
      IsClopen.eq_univ (α := S) ⟨hU, U.isOpen⟩ ⟨_, hr ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have := (H _ (𝟙 _)).2 (fun y _ => hall ▸ Set.mem_univ y)
    simpa using this
  · have := t.hom i
    exact ExtUnique.isMonHom_of_isGrpPullback hφ hφ (t.act i) (a i) (ha i)

theorem main : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (t : TObj g k J b (spMap (algebraMap R K) ≫ spMap β)) (P' : Out.PolAV (Sp R)) (φ : t.A.left ⟶ P'.A.left), P'.g = g → IsGrpPullback t.A P'.A (spMap (algebraMap R K)) φ → LBIso t.L (P'.L.pull φ) → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g k J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) := by
  intro hL _ o _ g k J b _ R K _ _ _ _ _ _ β t P' φ hg hφ hφL
  have := P'.isAb.proper
  have := P'.isAb.smooth
  let e : pullback P'.A.hom (spMap (algebraMap R K)) ⟶ t.A.left :=
    hφ.1.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ φ = pullback.fst _ _ := hφ.1.lift_fst _ _ _
  have e₂ : e ≫ t.A.hom = pullback.snd _ _ := hφ.1.lift_snd _ _ _
  let e' : t.A.left ⟶ pullback P'.A.hom (spMap (algebraMap R K)) := pullback.lift φ t.A.hom hφ.1.w
  have ee : e' ≫ e = 𝟙 _ := by
    apply hφ.1.hom_ext
    · rw [Category.assoc, e₁, Category.id_comp]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, e₂, Category.id_comp]; exact pullback.lift_snd _ _ _
  have wpt : ∀ i, (t.pt i).left ≫ t.A.hom = 𝟙 (Sp K) := fun i => Over.w (t.pt i)
  let v : Fin (2 * g) ⊕ J → (t.A.left ⟶ t.A.left) :=
    Sum.elim (fun i => t.A.hom ≫ (t.pt i).left) (fun j => (t.act j).left)
  have hv : ∀ i, v i ≫ t.A.hom = t.A.hom := by
    rintro (i | j)
    · exact (Category.assoc _ _ _).trans ((congrArg (t.A.hom ≫ ·) (wpt i)).trans (Category.comp_id _))
    · exact Over.w (t.act j)
  obtain ⟨f, hf, u', hu'⟩ := GlobalTheory.morphisms_generic_spread_out R K P'.A.left P'.A.left P'.A.hom P'.A.hom (Fin (2 * g) ⊕ J)
    (fun i => e ≫ v i ≫ φ) inferInstance inferInstance inferInstance (fun i => by
      rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (v i), hv, ← Category.assoc, e₂,
        pullback.condition])
  have hfK : IsUnit (algebraMap R K f) :=
    IsUnit.mk0 _ fun h0 => hf (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  let ψ : Localization.Away f →+* K := IsLocalization.Away.lift f hfK
  have hψ : ψ.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f hfK
  have hψs : spMap ψ ≫ spMap (algebraMap R (Localization.Away f)) = spMap (algebraMap R K) := by
    rw [← hψ]; exact (Spec.map_comp _ _).symm
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hψi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, m⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) x
    have h₁ := congrArg ψ h
    rw [map_mul, hx, zero_mul, ← RingHom.comp_apply, hψ] at h₁
    have h₂ : r = 0 := IsFractionRing.injective R K (h₁.symm.trans (map_zero _).symm)
    rw [h₂, map_zero] at h
    exact (IsLocalization.map_units (Localization.Away f) m).mul_left_eq_zero.1 h
  have : IsSchemeTheoreticallyDominant (spMap ψ) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hψi
  have : PreconnectedSpace (Sp (Localization.Away f)) :=
    inferInstanceAs (PreconnectedSpace (PrimeSpectrum (Localization.Away f)))
  have hprim := b.prim K ((algebraMap R K).comp β)
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by
    have := b.unit.map β
    rw [h0, Nat.cast_zero, map_zero] at this
    exact not_isUnit_zero this
  have hζ : unitS (spMap (algebraMap R (Localization.Away f)) ≫ spMap β) b.ζ ^ k = 1 := by
    rw [unitS_comp, ← map_pow, unitS_spMap_pow β b.ζ k (IsFractionRing.injective R K (by
      rw [map_pow, map_one]; exact hprim.pow_eq_one)), map_one]
  obtain ⟨P, χ, hχ₀, hgP, hm, c, hc⟩ := hL.polBaseChange _ _ (spMap (algebraMap R (Localization.Away f))) P'
  have hχ : IsGrpPullback P.A P'.A (spMap (algebraMap R (Localization.Away f))) χ :=
    ⟨hχ₀, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hχ₀.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hχ₀.w y),
        ← hm]
      rfl⟩
  let w : t.A.left ⟶ P.A.left := hχ₀.lift φ (t.A.hom ≫ spMap ψ) (by rw [Category.assoc, hψs, hφ.1.w])
  have w₁ : w ≫ χ = φ := hχ₀.lift_fst _ _ _
  have w₂ : w ≫ P.A.hom = t.A.hom ≫ spMap ψ := hχ₀.lift_snd _ _ _
  have hw : IsGrpPullback t.A P.A (spMap ψ) w := hχ.cancel (hφ.congr hψs.symm w₁.symm) w₂
  have hwL : LBIso t.L (P.L.pull w) :=
    hφL.trans t.isLB (LB.isLB_pull P'.isLB _) (LB.isLB_pull P.isLB _)
      (LBIso.chartPull (chartPullSame P'.L (fun _ : PUnit => φ) (fun _ : PUnit => χ) (fun _ => 1) w fun _ => w₁.symm)
        (Geo.Tor.chartPullPull P.L w w rfl) ⟨c, hc⟩)
  let d : P.A.left ⟶ pullback P'.A.hom (spMap (algebraMap R (Localization.Away f))) := pullback.lift χ P.A.hom hχ₀.w
  have d₁ : d ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  let v' : Fin (2 * g) ⊕ J → (P.A ⟶ P.A) := fun i => Over.homMk (hχ₀.lift (d ≫ u' i) P.A.hom (by
    rw [Category.assoc, (hu' i).1, ← Category.assoc, d₁, hχ₀.w])) (hχ₀.lift_snd _ _ _)
  have hv' : ∀ i, v i ≫ w = w ≫ (v' i).left := fun i => by
    have a₁ : (v' i).left ≫ χ = d ≫ u' i := hχ₀.lift_fst _ _ _
    have a₂ := (hu' i).2 (e ≫ w ≫ d) (by rw [Category.assoc, Category.assoc, d₁, w₁, e₁])
    apply hχ₀.hom_ext
    · rw [Category.assoc, Category.assoc, w₁, a₁]
      have a₃ := congrArg (e' ≫ ·) a₂
      simp only [← Category.assoc, ee, Category.id_comp] at a₃
      rw [← a₃, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w (v' i), w₂, ← Category.assoc, hv]
  have z₁ : eSec P.A ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have z₂ : eSec t.A ≫ t.A.hom = 𝟙 _ := Over.w η[t.A]
  refine ⟨f, hf, ?_⟩
  obtain ⟨t', ht'⟩ := exists_extension hL (spMap (algebraMap R (Localization.Away f)) ≫ spMap β) (spMap ψ)
    (by rw [← Category.assoc, hψs]) hk hζ t P w (hgP.trans hg) hw hwL
    (fun i => Over.homMk (eSec P.A ≫ (v' (.inl i)).left) (by
      show (eSec P.A ≫ (v' (.inl i)).left) ≫ P.A.hom = 𝟙 _
      rw [Category.assoc, Over.w (v' _), z₁]))
    (fun i => by
      show (t.pt i).left ≫ w = spMap ψ ≫ eSec P.A ≫ (v' (.inl i)).left
      refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
      refine (congrArg (· ≫ (v' (.inl i)).left) (PolBaseChange.eSec_comm hw).symm).trans ?_
      refine (Category.assoc _ _ _).trans ((congrArg (eSec t.A ≫ ·) (hv' (.inl i)).symm).trans ?_)
      show eSec t.A ≫ (t.A.hom ≫ (t.pt i).left) ≫ w = _
      rw [Category.assoc, ← Category.assoc, z₂]
      exact Category.id_comp _)
    (fun j => v' (.inr j)) (fun j => hv' (.inr j))
  exact ⟨t', ψ, hψ, ht'⟩

end GlobalTheory.SpreadLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_endomorphisms_spread_over_basicOpen : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (t : TObj g k J b (spMap (algebraMap R K) ≫ spMap β)) (P' : Out.PolAV (Sp R)) (φ : t.A.left ⟶ P'.A.left), P'.g = g → IsGrpPullback t.A P'.A (spMap (algebraMap R K)) φ → LBIso t.L (P'.L.pull φ) → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g k J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) := by
  first | exact @GlobalTheory.SpreadLevel.main | exact GlobalTheory.SpreadLevel.main | (intros; apply GlobalTheory.SpreadLevel.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolume
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV Filter Topology

namespace GlobalTheory.VolEx

theorem tendsto_pow_div_pow {i k : ℕ} (h : i ≤ k) :
    Tendsto (fun e : ℕ => (e : ℝ) ^ i / (e : ℝ) ^ k) atTop (𝓝 (if i = k then 1 else 0)) := by
  split_ifs with hik
  · subst hik
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with e he
    rw [div_self (by positivity)]
  · exact (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne h hik)).comp tendsto_natCast_atTop_atTop

theorem tendsto_eval_div_pow (Q : Polynomial ℚ) {k : ℕ} (h : Q.natDegree ≤ k) :
    Tendsto (fun e : ℕ => ((Q.eval (e : ℚ) : ℚ) : ℝ) / (e : ℝ) ^ k) atTop (𝓝 (Q.coeff k : ℝ)) := by
  have h1 : Tendsto (fun e : ℕ => ∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * ((e : ℝ) ^ i / (e : ℝ) ^ k)) atTop
      (𝓝 (∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * (if i = k then 1 else 0))) :=
    tendsto_finsetSum _ fun i hi =>
      (tendsto_pow_div_pow (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).const_mul _
  simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true] at h1
  refine h1.congr fun e => ?_
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h)]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem vAmp_of_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {m : ℕ} {s : Fin (m + 1) → M.Sec}
    (h : AbLaw.VeryAmpleBy p M s) : VAmp p M s := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  obtain ⟨r, hr, hs⟩ := (h.2 i).2
  refine ⟨r, hr, fun f => ?_⟩
  obtain ⟨F, hF⟩ := hs f
  exact ⟨F, hF.symm⟩

theorem vol_of_eventually {p : X ⟶ Sp K} {M : LB X} (hex : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r) (φ : ℕ → ℝ)
    (hφ : ∀ᶠ e : ℕ in atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) {k : ℕ} {δ : ℝ}
    (hδ : Tendsto (fun e : ℕ => φ e / (e : ℝ) ^ k) atTop (𝓝 δ)) : Vol p M k δ := by
  have : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ ((∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) → (r : ℝ) = φ e) := by
    intro e
    by_cases h : ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e
    · obtain ⟨r, h1, h2⟩ := h
      exact ⟨r, h1, fun _ => h2⟩
    · obtain ⟨r, h1⟩ := hex e
      exact ⟨r, h1, fun h' => absurd h' h⟩
  choose h h1 h2 using this
  refine ⟨h, h1, hδ.congr' ?_⟩
  filter_upwards [hφ] with e he
  rw [h2 e he]

theorem vol_nonneg {p : X ⟶ Sp K} {M : LB X} {k : ℕ} {δ : ℝ} (h : Vol p M k δ) : 0 ≤ δ := by
  obtain ⟨h, -, hh⟩ := h
  exact ge_of_tendsto' hh fun e => by positivity

theorem exists_vol : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → ∃ δ : ℝ, 0 < δ ∧ Vol P.A.hom M P.g δ := by
  intro hL _ K _ _ P M hM hA
  have hex : ∀ (N : LB P.A.left), N.IsLB → ∀ e, ∃ r, SectionsHaveFiniteDimension P.A.hom (lbPow N e) r := fun N hN e =>
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P (lbPow N e) 0 (LB.isLB_linComb hN _ _)).1
  have : IsProper P.A.hom := P.isAb.proper
  obtain ⟨d, hd, m, s, hs⟩ :=
    ((relAmple_iff_isAmpleLB_of_isAffine P.A hM).1 hA).exists_veryAmpleBy (R := K) P.A.hom
  have hH : (lbPow M d).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.hilbertFunction_vanishingIdeal_veryAmpleSystem K (Fin (m + 1)) _ P.A.hom (lbPow M d) s hH (vAmp_of_veryAmpleBy hs)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have volM : ∀ k, Q.natDegree ≤ k → Vol P.A.hom M k ((Q.coeff k : ℝ) / (d : ℝ) ^ k) := by
    intro k hk
    refine (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P M k hM).2.2.2.2.1 d _ hd hA ?_
    rw [mul_div_cancel₀ _ (by positivity)]
    refine vol_of_eventually (hex _ hH) _ ?_ (tendsto_eval_div_pow Q hk)
    filter_upwards [hQ] with e ⟨r, h1, h2, _⟩
    exact ⟨r, h1, by rw [← h2]; norm_cast⟩
  have volL : ∀ k, P.g ≤ k → Vol P.A.hom P.L k (if P.g = k then 1 else 0) := by
    intro k hk
    refine vol_of_eventually (hex _ P.isLB) (fun e => (e : ℝ) ^ P.g) ?_ (tendsto_pow_div_pow hk)
    filter_upwards [eventually_ge_atTop 1] with e he
    exact ⟨e ^ P.g, PowSec.exists_basis_sections hL.globalSectionsRank K P e he, by push_cast; rfl⟩
  have dom : ∀ (A B : LB P.A.left), A.IsLB → B.IsLB → Out.RelAmple P.A A → ∃ c : ℕ, ∀ k δ δ',
      Vol P.A.hom B k δ → Vol P.A.hom A k δ' → δ ≤ (c : ℝ) ^ k * δ' := by
    intro A B hA hB ha
    obtain ⟨c, ⟨⟨t, ht⟩, -⟩, hc⟩ := ((GlobalTheory.T.eventually_section_and_relAmple_pow_div K P A B hA hB ha).and (eventually_ge_atTop 1)).exists
    refine ⟨c, fun k δ δ' h1 h2 => ?_⟩
    exact ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P B k hB).2.2.2.2.2 (lbPow A c) t (LB.isLB_linComb hA _ _) ht).2 _ _ h1
      ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P A k hA).2.2.2.1 c δ' hc h2)
  have hdeg : Q.natDegree ≤ P.g := by
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc⟩ := dom P.L M P.isLB hM P.ample
    have h1 := hc _ _ _ (volM _ le_rfl) (volL _ hlt.le)
    rw [if_neg hlt.ne, mul_zero] at h1
    have h2 := le_antisymm h1 (vol_nonneg (volM _ le_rfl))
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · have h3 : Q.leadingCoeff = 0 := by exact_mod_cast h2
      rw [Polynomial.leadingCoeff_eq_zero] at h3
      rw [h3] at hlt
      simp at hlt
    · exact absurd h2 (by positivity)
  refine ⟨_, ?_, volM _ hdeg⟩
  obtain ⟨c, hc⟩ := dom M P.L hM P.isLB hA
  have h1 := hc _ _ _ (volL _ le_rfl) (volM _ hdeg)
  rw [if_pos rfl] at h1
  refine lt_of_le_of_ne (vol_nonneg (volM _ hdeg)) fun h => ?_
  rw [← h, mul_zero] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory.VolEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolumeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizedAbelian_ample_exists_positive_volume : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → ∃ δ : ℝ, 0 < δ ∧ Vol P.A.hom M P.g δ := by
  first | exact @GlobalTheory.VolEx.exists_vol | exact GlobalTheory.VolEx.exists_vol | (intros; apply GlobalTheory.VolEx.exists_vol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientPrincipalTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropicOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescends
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LinDescent


open ThetaSplit in
theorem lbPow_descends : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) := by
  intro hlaw k _ _ P n C B _ ψ hn hnk htor hW hψ hfin het hsurj hker
  have := P.isAb.comm
  letI : CommGroup C := { (inferInstance : Group C) with mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }
  have hfinT : Finite {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} := by
    have h := (hlaw.mulN (Sp k) P n hn).2.2.2.2 k (𝟙 _) hnk
    exact Nat.finite_of_card_ne_zero (h.trans_ne (pow_ne_zero _ hn.ne'))
  have : Finite C := Finite.of_injective
    (fun c : C => (⟨c.1, htor c.1 c.2⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1}))
    fun a b h => Subtype.ext (congrArg (fun q => q.1) h)
  obtain ⟨u, hu, hc⟩ := ThetaSplit.exists_cocycle hlaw.globalFns P.isAb P.isLB (ThetaSplit.units_divisible k) n C.subtype
    (fun c c' => hW c.1 c.2 c'.1 c'.2)
  refine exists_descent_of_isReduced (Sp k) P.A B ψ C C.subtype (lbPow P.L n) (DVR.linComb_isLB P.L P.isLB _ _) hψ hfin het hsurj
    (fun k' _ _ t => ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c h => ?_⟩) u hu hc
  · obtain ⟨c, h₁, h₂⟩ := ThetaSplit.exists_rational_ker ψ t x hx
    exact ⟨⟨c, (hker c).1 h₁⟩, h₂⟩
  · rintro ⟨c, rfl⟩
    rw [Category.assoc, (hker (C.subtype c)).2 c.2, MonObj.comp_one]
  · have : Epi t := ThetaSplit.epi_of_fields t
    refine Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 ?_))
    have e : toUnit (Over.mk t) ≫ c.1 = toUnit (Over.mk t) ≫ (1 : 𝟙_ (Over (Sp k)) ⟶ P.A) :=
      h.trans (MonObj.comp_one _).symm
    exact congrArg (fun q => q.left) e

end GlobalTheory.LinDescent
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem lbPow_descends_of_isotropic_of_laws : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) :=
  LinDescent.lbPow_descends

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientPrincipalTriple
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem exists_heckeQuotient_triple_of_laws : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left) := by
  intro laws E _ _ _ H k _ _ _ t g p C hp hprop hsm hamp hK hst hpow
    hweil hcard
  have glob : Out.GlobalFnsSt := laws.globalFns
  have cube := GlobalTheory.Moduli.cube_of_isLB
  have cubeDesc := GlobalTheory.cube_descends_along_etale_isogeny glob
  have quot := GlobalTheory.exists_quotient_by_finite_group_of_points laws
  have split := GlobalTheory.lbPow_descends_of_isotropic_of_laws laws
  have princ := GlobalTheory.kTriv_of_descent laws
  have amp := GlobalTheory.relAmple_finite_pow_iso
  have prim := GlobalTheory.PrimNorm.exists_primitive_normalisation glob
  have seesaw := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian glob
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp k) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp _).ne')
  obtain ⟨B, gB, ψ, hB, hψ, hf, he, hs, hker, huniv⟩ :
      ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : t.G ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧
        Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧
        ∀ (Y : Over (Sp k)) (f : t.G ⟶ Y), (∀ x ∈ C, ((toUnit t.G ≫ x) * 𝟙 t.G) ≫ f = f) →
          ∃! f' : B ⟶ Y, ψ ≫ f' = f := quot k P C hfin
  have := hB.comm
  obtain ⟨M, hM, hiso⟩ : ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) :=
    split k P (p ^ 2) C B ψ hn (Nat.cast_ne_zero.2 hn.ne') hpow hweil hψ hf he hs hker
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen :=
    cubeDesc k t.G B ψ M hA hB hM hψ hf he hs (cube _ P (M.pull ψ.left) (pull_isLB hM _))
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hid : IsFinite (𝟙 t.G : t.G ⟶ t.G).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple t.G (lbPow t.PP.L (p ^ 2)) :=
    (amp _ t.G t.G (𝟙 _) t.PP.L (p ^ 2) hn hA hA hL hid).2.1.2 hamp

  have hMamp : Out.RelAmple B M :=
    (amp _ t.G B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs
      ((amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁)

  have fac : ∀ (Y : Over (Sp k)) [GrpObj Y] (f : t.G ⟶ Y) [IsMonHom f], (∀ x ∈ C, x ≫ f = 1) →
      ∃ f' : B ⟶ Y, ψ ≫ f' = f := fun Y _ f _ h =>
    (huniv Y f fun x hx => by
      rw [MonObj.mul_comp, Category.assoc, h x hx, MonObj.comp_one, _root_.one_mul, Category.id_comp]).exists
  have canc : ∀ (Y : Over (Sp k)) (f f' : B ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    (huniv Y (ψ ≫ f) fun x hx => by
      rw [← Category.assoc, MonObj.mul_comp, Category.assoc, (hker x).2 hx, MonObj.comp_one, _root_.one_mul,
        Category.id_comp]).unique rfl h.symm
  have hact : ∀ a, ∃ f' : B ⟶ B, ψ ≫ f' = t.act.act a ≫ ψ := fun a => by
    have := t.act.hom a
    exact fac B _ fun x hx => by rw [← Category.assoc]; exact (hker _).2 (hst x hx a)
  choose α hα using hact
  let act : OAct (𝓞 E) B :=
    { act := α
      hom := fun a => laws.rigidity _ B B hB hB _ (by
        have := t.act.hom a
        rw [← IsMonHom.one_hom ψ, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom])
      one := canc _ _ _ (by rw [hα, t.act.one, Category.id_comp, Category.comp_id])
      mul := fun a b => canc _ _ _ (by
        rw [hα, t.act.mul, ← Category.assoc ψ, hα, Category.assoc, Category.assoc, hα])
      add := fun a b => canc _ _ _ (by rw [hα, t.act.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) }
  have hαhom : ∀ a, IsMonHom (α a) := act.hom

  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]

  have hpowhom : IsMonHom (𝟙 t.G ^ p ^ 2) := laws.rigidity _ _ _ hA hA _ (by
    have e₁ : (η[t.G] : 𝟙_ _ ⟶ t.G) = 1 := by rw [Hom.one_def]; simp
    rw [MonObj.comp_pow, Category.comp_id, e₁, one_pow])
  obtain ⟨π, hπ⟩ := fac t.G (𝟙 t.G ^ p ^ 2) fun x hx => by rw [MonObj.comp_pow, Category.comp_id, hpow x hx]
  have hπψ : π ≫ ψ = 𝟙 B ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := hαhom a
    have := hαhom (H.bar a)
    have adjA : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G),
        lam m (u ≫ ψ ≫ α a) (v ≫ ψ) = lam m (u ≫ ψ) (v ≫ ψ ≫ α (H.bar a)) := by
      intro T u v
      rw [hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ α a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp k)} (x y : T ⟶ B), lam m (x ≫ α a) y = lam m x (y ≫ α (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M)
          (cubeLB B ![fst B B ≫ α a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine seesaw k B B _ M hB hB hM hMamp hN (val _ _ ?_) ?_ (val _ _ ?_)
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · have hs' : Surjective (𝟙 t.G ^ p ^ 2).left := (laws.mulN _ P (p ^ 2) hn).2.2.1
      have hs'' : Surjective ((𝟙 t.G ^ p ^ 2) ≫ ψ).left := by rw [Over.comp_left]; infer_instance
      refine dense_image_points ((𝟙 t.G ^ p ^ 2) ≫ ψ) _ fun u => val _ _ ?_
      have h := adjψ (toUnit B ≫ u) π
      rw [← Category.assoc π, hπψ, MonObj.pow_comp, lam_pow_right hM hΘ, lam_pow_right hM hΘ] at h
      rw [MonObj.pow_comp, MonObj.comp_pow, MonObj.comp_pow, MonObj.pow_comp, lam_pow_left hM hΘ,
        lam_pow_left hM hΘ]
      simpa only [Category.assoc, Category.id_comp] using h
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ := prim E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (α H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  have a₂ : Out.RelAmple t.G (PP.L.pull ψ.left) :=
    (amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hP' _) hfinal a₁
  have a₃ : Out.RelAmple B PP.L :=
    (amp _ t.G B ψ PP.L 1 one_pos hA hB hP' hf).2.2.1 inferInstance hs a₂
  have hc : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ t.G // x ≫ ψ = 1} = (p ^ 2) ^ g := by
    rw [← pow_mul, ← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hlam : LBIso (abelian₂ t.G (lbPow t.PP.L (p ^ 2))) (abelian₂ t.G (PP.L.pull ψ.left)) := by
    refine (cls_eq_iff (LB.isLB_linComb hn' _ _) (LB.isLB_linComb (pull_isLB hP' _) _ _)).1 ?_
    refine (cls_cube_two hn' _ _ _).trans (Eq.trans ?_ (cls_cube_two (pull_isLB hP' _) _ _ _).symm)
    rw [(cls_eq_iff hn' (pull_isLB hP' _)).2 hfinal]
  have a₄ : Out.KTriv B PP.L := princ k P (p ^ 2) B ψ PP.L hn hB hP' hψ hf he hs hc hlam
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, hψ, hf, he, hs, hker, fun a => (hα a).symm, hfinal⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientPrincipalTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeQuotient_principal_triple : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left) := by
  first | exact @GlobalTheory.exists_heckeQuotient_triple_of_laws | exact GlobalTheory.exists_heckeQuotient_triple_of_laws | (intros; apply GlobalTheory.exists_heckeQuotient_triple_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolFamOfGrpFam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem torsBasis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S : Scheme.{0}}

theorem torsBasis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact torsBasis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

theorem exists_polFam_of_grpFam : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)), N' ≠ 0 → Odd m → m ∣ N' → DenseP (objPrimes b Mat κ β v) → GrpFam b Mat κ β v m A L act Q → ∃ L' : LB A.left, PolFam b Mat κ β v A L' act Q := by
  intro hL hL2 o _ g N' J b Mat κ R _ _ _ β v m A _ L act Q hN0 hodd ⟨l, hl⟩ hD ⟨hab, hsm, hlb, hamp, hlab, hfib⟩
  have hun : IsUnit (m : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero, hl, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have := hab.comm
  obtain ⟨L', l1, l2, l3, l4, l5⟩ := GlobalTheory.OddDescent.exists_descended hL hL2 R A g m L
    (fun i => (Q i ^ l : Out.baseOver (Sp R) ⟶ A)) hab hsm hodd hun hlb hamp
    (fun i => by
      have e : l * m = N' := by rw [mul_comm, ← hl]
      have : (Q i ^ l) ^ m = 1 := by rw [← pow_mul, e, hlab.2.1]
      exact this)
    (fun K _ _ x => torsBasis_pow_linComb hl hN0 _ _ hlab.2.1 (hlab.2.2 K x))
    (fun r hr => hD r fun q hq hqp => hr q (by
      obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
      exact ⟨K, inferInstance, inferInstance, x, t.pol, ψ, hx, hψ.1, hi⟩) hqp)
  refine ⟨L', hab, hsm, l1, l2, l3, l4, hlab, fun K _ _ x s t ht => ?_⟩
  obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
  exact ⟨ψ, hψ, l5 K x t.pol ψ hψ.1 hi⟩

end GlobalTheory.ZM.NearBuild
end
