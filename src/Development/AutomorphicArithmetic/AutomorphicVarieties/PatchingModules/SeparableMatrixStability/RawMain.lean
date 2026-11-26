module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlChBar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PtDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapStar
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ms_single {B X Y : Type} [CommRing B] [Group X] [Group Y] (f : X →* Y) (a : X) (c : B) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

private theorem ms_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a : F.G₀) (c : B) :
    F.star O B n (MonoidAlgebra.single a c) =
      MonoidAlgebra.single (F.conj a)⁻¹ (c * ((F.eps O B a ^ (1 - (n : ℤ)) : Bˣ) : B)) := by
  unfold GFrame.star GFrame.starOp
  rw [MonoidAlgebra.lift_single, MulOpposite.unop_smul]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, MonoidAlgebra.smul_single, smul_eq_mul]

private theorem ms_add {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) (a b : MonoidAlgebra B F.G₀) :
    F.star O B n (a + b) = F.star O B n a + F.star O B n b := by
  unfold GFrame.star
  rw [map_add (f := _), MulOpposite.unop_add]

private theorem ms_zero {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (B : Type) [CommRing B] [Algebra O B] (n : ℕ) : F.star O B n 0 = 0 := by
  unfold GFrame.star
  rw [map_zero, MulOpposite.unop_zero]

theorem UpperTheory.V.Pa.map_star :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B : Type) [CommRing B] [Algebra O B], (∀ y, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.star O B n y) = G'.frame.star O B n (MonoidAlgebra.mapDomainRingHom B g.p₀ y)) ∧ (∀ v (ψ : Fin n → L.Gv v →* Bˣ) a, MonoidAlgebra.mapDomainRingHom B g.p₀ (G.frame.oEl v ψ a) = G'.frame.oEl v ψ a) ∧ (∀ (ph : G.G₀) (U : Fin n → B), MonoidAlgebra.mapDomainRingHom B g.p₀ (q1El ph U) = q1El (g.p₀ ph) U) ∧ ∀ (ph ta : G.G₀) (U : Fin n → B) i y, MonoidAlgebra.mapDomainRingHom B g.p₀ (q2El ph ta U i y) = q2El (g.p₀ ph) (g.p₀ ta) U i y := by
  intro l _ L G G' g n O _ _ B _ _
  refine ⟨fun y => ?_, fun v ψ a => ?_, fun ph U => ?_, fun ph ta U i y => ?_⟩
  · induction y using MonoidAlgebra.induction_linear with
    | zero => rw [ms_zero, map_zero, ms_zero]
    | add a b ha hb => rw [ms_add, map_add (f := _), map_add (f := _), ms_add, ha, hb]
    | single a c =>
      rw [ms_star, ms_single, ms_single, ms_star, map_inv, g.p₀_conj, g.eps_p₀]
  · unfold GFrame.oEl
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one, g.p₀_φ]
  · unfold q1El
    rw [map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, ms_single, map_one]
  · unfold q2El
    rw [map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2
      funext k
      simp only [Function.comp_apply]
      split_ifs
      · exact map_one _
      · simp only [map_sub, ms_single, map_one]
    · simp only [map_sub, ms_single, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PairDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_single {B G G' : Type} [CommRing B] [Group G] [Group G'] (f : G →* G') (a : G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a 1) = MonoidAlgebra.single (f a) 1 := by
  simp

theorem UpperTheory.V.Pa.pair_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (r' : Resid G'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → g.p.ker = PL l H → Glob.Compat g r r' → ∃ u' : Pair r' B, u'.D.comap g.p₀ = u.D ∧ u'.ψ = u.ψ := by
  intro l _ L G G' g n O _ _ _ _ _ r r' B _ _ _ u H _ hHo hHη hHχ hker hc
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hkill : ∀ k : G.G₀, g.p₀ k = 1 → u.D.Kills (MonoidAlgebra.single k 1 - 1) := by
    intro k hk
    have hk' : (k : G.Γ) ∈ PL l H := by
      rw [← hker, MonoidHom.mem_ker, ← g.coe_p₀, hk]; rfl
    have h1 := pl_chBar l L G n O r B u H hHo hHη hHχ ∅ k hk'
    refine UpperTheory.V.CA.d_closed u.D (maximalIdeal B) u.cont (u.D.CH ∪ ∅) ?_ _ h1
    rintro z (hz | hz)
    · refine (UpperTheory.V.CA.d_toDet u.D z).2.2.2.1 ((UpperTheory.V.CA.d_ker _ z).1.1 (UpperTheory.V.CA.d_ch_ker _ ?_))
      rw [UpperTheory.V.CA.d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    · exact hz.elim
  obtain ⟨D', hD'⟩ := gdet_desc n B G.G₀ G'.G₀ g.p₀ u.D g.p₀_surj hkill
  obtain ⟨-, hlam, htr, hmap, -, -⟩ := comap_lam n B G.G₀ G'.G₀ g.p₀ D'
  rw [hD'] at hlam htr hmap
  obtain ⟨hstar, hoEl, -, -⟩ := map_star l L G G' g n O B
  refine ⟨{ D := D', ψ := u.ψ, cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, hD', rfl⟩
  · intro i
    refine (g.adicCont_iff _ fun a => D'.lam i (MonoidAlgebra.single a 1)).1 ?_
    have : (fun a => D'.lam i (MonoidAlgebra.single (g.p₀ a) 1)) =
        fun a : G.G₀ => u.D.lam i (MonoidAlgebra.single a 1) := funext fun a => by
      rw [hlam, md_single]
    rw [this]
    exact u.cont i
  · obtain ⟨-, -, -, -, hrep, hinj⟩ := comap_lam n (ResidueField O) G.G₀ G'.G₀ g.p₀ r'.Dbar
    refine (hinj g.p₀_surj).1 _ ?_
    rw [← hmap]
    refine u.red.trans ?_
    unfold Resid.Dbar
    rw [hrep]
    congr 1
    ext a i j
    simp only [diagRep, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, hc1]
  · intro v i
    refine ⟨(u.psi v i).cont, fun a => ?_, fun a => ?_⟩
    · rw [← hc2]; exact (u.psi v i).red a
    · rw [← hc3]; exact (u.psi v i).mu a
  · intro i a
    obtain ⟨a, rfl⟩ := g.p₀_surj a
    rw [← md_single, ← hstar, ← hlam, ← hlam]
    exact u.P i a
  · intro v a h
    obtain ⟨h, rfl⟩ := g.p₀_surj h
    rw [← md_single, ← hoEl, ← map_mul, ← htr]
    exact u.Ord v a h
  · rintro w _ ⟨⟨a, ha, rfl⟩, ha'⟩ h
    obtain ⟨h, rfl⟩ := g.p₀_surj h
    have hmem : G.φu w a ∈ r.Ip w := by
      refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
      have := Subgroup.mem_iInf.1 ha' i
      rw [MonoidHom.mem_ker] at this ⊢
      rw [hc1, MonoidHom.comp_apply, g.p₀_φu]
      exact this
    have := u.I w _ hmem h
    rw [htr, map_mul, map_sub, map_one, md_single, md_single, g.p₀_φu] at this
    exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ResidDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.resid_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G.frame O n), (∀ a : G.G₀, g.p₀ a = 1 → ∀ i, r.chib i a = 1) → ∃ r' : Resid G'.frame O n, Glob.Compat g r r' ∧ ((∀ w, r.Ip w = G.frame.Iu w) → ∀ w, r'.Ip w = G'.frame.Iu w) := by
  intro l _ L G G' g n O _ _ _ r hker
  let c : Fin n → G'.frame.G₀ →* (ResidueField O)ˣ := fun i =>
    g.p₀.liftOfSurjective g.p₀_surj ⟨r.chib i, fun a ha => by
      rw [MonoidHom.mem_ker] at ha ⊢
      exact hker a ha i⟩
  have hca : ∀ i a, c i (g.p₀ a) = r.chib i a := fun i a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hc : ∀ i, (c i).comp g.p₀ = r.chib i := fun i => by
    ext a
    simp only [MonoidHom.comp_apply, hca]
  have hdiag : (diagRep c).comp g.p₀ = diagRep r.chib := by
    ext a
    simp only [MonoidHom.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, hca]
  have hD : (GDet.ofRep (diagRep c)).comap g.p₀ = GDet.ofRep (diagRep r.chib) := by
    rw [(comap_lam n (ResidueField O) _ _ g.p₀ (GDet.ofRep (diagRep c))).2.2.2.2.1 (diagRep c), hdiag]
  have key : ∀ (B : Type) [CommRing B] [Algebra (ResidueField O) B] (z : MonoidAlgebra B G.frame.G₀),
      (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z) =
        (GDet.ofRep (diagRep r.chib)).D B z := by
    intro B _ _ z
    calc (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z)
        = ((GDet.ofRep (diagRep c)).comap g.p₀).D B z := rfl
      _ = (GDet.ofRep (diagRep r.chib)).D B z := by rw [hD]
  let r' : Resid G'.frame O n :=
    { chib := c
      chib_open := fun i => by
        rw [← g.p₀_quot.isOpen_preimage]
        have hset : (g.p₀ ⁻¹' ((c i).ker : Set G'.frame.G₀)) = ((r.chib i).ker : Set G.frame.G₀) := by
          ext a
          simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, hca]
        rw [hset]
        exact r.chib_open i
      chib_inj := fun i j hij => by
        apply r.chib_inj
        rw [← hc i, ← hc j, hij]
      polar := by
        intro B _ _ _ _ y
        obtain ⟨x0, hx0⟩ := Finsupp.mapDomain_surjective (M := B) g.p₀_surj y.coeff
        have hx' : MonoidAlgebra.mapDomainRingHom B g.p₀ (MonoidAlgebra.ofCoeff x0) = y := by
          rw [MonoidAlgebra.mapDomainRingHom_apply]
          show MonoidAlgebra.ofCoeff (Finsupp.mapDomain _ x0) = y
          rw [hx0]
        rw [← hx', ← (map_star l L G G' g n O B).1 (MonoidAlgebra.ofCoeff x0), key, key]
        exact r.polar B _
      psib := r.psib
      psib_open := r.psib_open
      th := r.th
      th_comm := r.th_comm }
  refine ⟨r', ⟨fun i => (hc i).symm, rfl, rfl⟩, ?_⟩
  intro hIp w
  have hle : ∀ i, G.frame.Iu w ≤ (r.chib i).ker := by
    intro i
    have h1 := hIp w
    unfold Resid.Ip at h1
    exact (inf_eq_left.mp h1).trans (iInf_le _ i)
  unfold Resid.Ip
  apply inf_eq_left.mpr
  rw [le_iInf_iff]
  intro i
  rintro _ ⟨x, hx, rfl⟩
  show c i ((G'.φu w) x) = 1
  rw [← g.p₀_φu w x, hca]
  exact hle i ⟨x, hx, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AutDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa
open scoped TensorProduct

noncomputable section

private theorem gdet_comap_comap {n : ℕ} {A G G' G'' : Type} [CommRing A] [Group G] [Group G'] [Group G'']
    (D : GDet n A G'') (f : G →* G') (f' : G' →* G'') : (D.comap f').comap f = D.comap (f'.comp f) := by
  apply GDet.ext
  intro B _ _ x
  show (D.D B) ((MonoidAlgebra.mapDomainRingHom B f') ((MonoidAlgebra.mapDomainRingHom B f) x)) =
    (D.D B) (MonoidAlgebra.mapDomainRingHom B (f'.comp f) x)
  rw [MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

private theorem mapDom_single {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (a : G) (c : A) :
    MonoidAlgebra.mapDomainRingHom A f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  simp

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 G0' G G' : Glob l L} {n : ℕ} {O : Type} [CommRing O] [IsLocalRing O]
  [Algebra ℤ_[l] O] {r : Resid G0.frame O n} {r' : Resid G0'.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B]
  {u : Pair r B} {u' : Pair r' B} {J : Ideal B} {σ : Type} {D : ℕ}

@[reducible] private def baseDesc (b : TWBase u J σ D) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ) : TWBase u' J σ D where
  wt := b.wt
  wt_res k := by rw [← hr]; exact b.wt_res k
  lam := b.lam
  segmentWeightExponent k := by rw [hψ]; exact b.segmentWeightExponent k
  M := b.M
  smul_lam := b.smul_lam
  free := b.free
  fin := b.fin
  supp := b.supp

variable {b : TWBase u J σ D} {h : G.Hom G0} {h' : G'.Hom G0'} {q : ℕ} {ut : Fin q → Fin n → O} {N : ℕ}

@[reducible] private def ringDesc (A : TWRing b h ut N) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ)
    (rN' : Resid G'.frame O n) (hc : Glob.Compat h' rN' r') (p' : Pair rN' A.R) (hp : p'.ψ = A.p.ψ) :
    TWRing (baseDesc b hr hψ) h' ut N where
  rN := rN'
  compat := hc
  R := A.R
  p := p'
  s := A.s
  s_w k := by rw [hp]; exact A.s_w k
  U := A.U
  U_res := A.U_res
  M := A.M
  a := A.a
  le_a := A.le_a
  rk := A.rk
  e := A.e
  e_smul := A.e_smul

private def MapsP (A : TWRing b h ut N) (Nq : Fin q → ℕ) (P : Fin q → Polynomial B) : Prop :=
  ∃ (θ : A.R →ₐ[O] Sp P fun j i => algebraMap O B (ut j i))
    (φ : (Sp P fun j i => algebraMap O B (ut j i)) ⊗[B] b.M →+ A.X)
    (ψ : A.X →+ (Sp P fun j i => algebraMap O B (ut j i)) ⊗[B] b.M),
    (A.p.Maps θ.toRingHom ((u.D.comap h.p₀).map (algebraMap B _)) fun v i => pushCh (algebraMap B _) (u.ψ v i)) ∧
    (∀ z, θ (A.s z) = algebraMap B _ (b.lam (MvPowerSeries.constantCoeff z))) ∧
    (∀ j i, θ (A.U j i) = Sp.u _ _ j i) ∧
    (∀ (t : A.R) z, φ (θ t • z) = t • φ z) ∧ (∀ (t : A.R) z, ψ (t • z) = θ t • ψ z) ∧
    (∀ z, φ (ψ z) = fEl Nq A.U • z) ∧ ∀ z, ψ (φ z) = θ (fEl Nq A.U) • z

private theorem maps_desc (A : TWRing b h ut N) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ)
    (rN' : Resid G'.frame O n) (hc : Glob.Compat h' rN' r') (p' : Pair rN' A.R) (hp : p'.ψ = A.p.ψ)
    (g0 : G0.Hom G0') (g : G.Hom G') (comm : ∀ a, h'.p₀ (g.p₀ a) = g0.p₀ (h.p₀ a))
    (hD : u'.D.comap g0.p₀ = u.D) (hpD : p'.D.comap g.p₀ = A.p.D)
    (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (m : TWMaps Nq ph ta A ex) :
    Nonempty (TWMaps Nq (fun j => g.p₀ (ph j)) (fun j => g.p₀ (ta j)) (ringDesc A hr hψ rN' hc p' hp) ex) := by
  have H : MapsP A Nq fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1) :=
    ⟨m.θ, m.φ, m.ψ, m.θ_pair, m.theta_coefficientMap_eq, m.θ_U, m.φ_smul, m.ψ_smul, m.φψ, m.ψφ⟩
  have e : (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) =
      fun j => u'.D.chi (MonoidAlgebra.single (h'.p₀ (g.p₀ (ph j))) 1) := funext fun j => by
    rw [← hD, (comap_lam n B _ _ g0.p₀ u'.D).1, mapDom_single, comm]
  rw [e] at H
  obtain ⟨θ, φ, ψ, ⟨h1, h1'⟩, h2, h3, h4, h5, h6, h7⟩ := H
  have htr : ∀ y, p'.D.tr (MonoidAlgebra.mapDomainRingHom A.R g.p₀ y) = A.p.D.tr y := fun y => by
    rw [← hpD, (comap_lam n A.R _ _ g.p₀ p'.D).2.2.1]
  obtain ⟨-, -, s1, s2⟩ := map_star l L G G' g n O A.R
  refine ⟨⟨θ, ⟨?_, fun v i => ?_⟩, h2, h3, φ, ψ, h4, h5, h6, h7, fun j a x => ?_, fun j i a x => ?_⟩⟩
  · refine ((comap_lam n _ _ _ g.p₀ _).2.2.2.2.2 g.p₀_surj).1 _ ?_
    have e1 := (comap_lam n _ _ _ g.p₀ p'.D).2.2.2.1 _ θ.toRingHom
    have e2 := (comap_lam n _ _ _ g.p₀ (u'.D.comap h'.p₀)).2.2.2.1 _
      (algebraMap B (SpAt u' (fun j => h'.p₀ (g.p₀ (ph j))) ut))
    have e3 : (u'.D.comap h'.p₀).comap g.p₀ = u.D.comap h.p₀ := by
      rw [← hD, gdet_comap_comap, gdet_comap_comap]
      exact congrArg _ (MonoidHom.ext comm)
    rw [hpD] at e1
    rw [e3] at e2
    exact e1.symm.trans (h1.trans e2)
  · have := h1' v i
    rw [← hp, ← hψ] at this
    exact this
  · obtain ⟨a, rfl⟩ := g.p₀_surj a
    have := m.rel1 j a x
    rw [← htr, map_mul, mapDom_single, s1] at this
    exact this
  · obtain ⟨a, rfl⟩ := g.p₀_surj a
    have := m.rel2 j i a x
    rw [← htr, map_mul, mapDom_single, s2] at this
    exact this

end

private theorem apply_mem_openNormalSubgroup_of_mem_PL_comap (l : ℕ) {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] (f : Γ →* Γ') (hf : Continuous f) (H : OpenNormalSubgroup Γ') (a : Γ)
    (ha : a ∈ PL l (Subgroup.comap f (H.toOpenSubgroup : Subgroup Γ'))) :
    f a ∈ (H.toOpenSubgroup : Subgroup Γ') := by
  let U : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨(H.toOpenSubgroup : Subgroup Γ').comap f, H.isOpen'.preimage hf⟩
      isNormal' := Subgroup.Normal.comap H.isNormal' f }
  have hU : PL l (Subgroup.comap f (H.toOpenSubgroup : Subgroup Γ')) ≤ (U.toOpenSubgroup : Subgroup Γ) :=
    iInf_le_of_le U (iInf_le_of_le (fun k hk => ⟨0, by rw [pow_zero, pow_one]; exact hk⟩) le_rfl)
  exact hU ha

theorem UpperTheory.V.Pa.aut_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (r' : Resid Q.G0'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (J : Ideal B) (σ : Type) (D : ℕ), Adapted T (r := r) → Glob.Compat Q.g0 r r' → u'.D.comap Q.g0.p₀ = u.D → u'.ψ = u.ψ → TWAut u J σ D T → Nonempty (TWAut u' J σ D Q.grp) := by
  intro l _ L G0 T Q n O _ _ _ _ _ r r' B _ _ _ u u' J σ D hAd hC hD hψ W
  have hr : r.psib = r'.psib := hC.2.1
  have key : ∀ N : ℕ, ∃ (rN' : Resid (Q.GN' N).frame O n) (_ : Glob.Compat (Q.h' N) rN' r')
      (p' : Pair rN' (W.A N).R) (_ : p'.ψ = (W.A N).p.ψ), p'.D.comap (Q.gN N).p₀ = (W.A N).p.D := by
    intro N
    have hchi : ∀ (a : (T.GN N).G₀) (i : Fin n), (W.A N).rN.chib i a = r.chib i ((T.h N).p₀ a) :=
      fun a i => by rw [(W.A N).compat.1 i]; rfl
    have hH : ∀ a : (T.GN N).G₀,
        (a : (T.GN N).Γ) ∈ Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ) →
        ∀ i, (W.A N).rN.chib i a = 1 := by
      intro a ha i
      rw [hchi]
      exact hAd.1 ((T.h N).p₀ a) ha i
    obtain ⟨rN', hc1, _⟩ := resid_desc l L (T.GN N) (Q.GN' N) (Q.gN N) n O (W.A N).rN (by
      intro a ha i
      apply hH a _ i
      have hk : (a : (T.GN N).Γ) ∈ (Q.gN N).p.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val ha
      rw [Q.kerN N] at hk
      exact apply_mem_openNormalSubgroup_of_mem_PL_comap l (T.h N).p (T.h N).cont T.H _ hk)
    have hleη : Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ) ≤ (T.GN N).η.ker := by
      intro a ha
      rw [MonoidHom.mem_ker, ← (T.h N).η a]
      exact T.H_η _ ha
    obtain ⟨p', hpD, hp⟩ := pair_desc l L (T.GN N) (Q.GN' N) (Q.gN N) n O (W.A N).rN rN' (W.A N).R (W.A N).p
      (Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ))
      (T.H.isOpen'.preimage (T.h N).cont) hleη hH (Q.kerN N) hc1
    refine ⟨rN', ⟨fun i => ?_, ?_, ?_⟩, p', hp, hpD⟩
    · refine MonoidHom.ext fun b => ?_
      obtain ⟨a, rfl⟩ := (Q.gN N).p₀_surj b
      show rN'.chib i ((Q.gN N).p₀ a) = r'.chib i ((Q.h' N).p₀ ((Q.gN N).p₀ a))
      rw [Q.comm₀ N a]
      have e1 : (W.A N).rN.chib i a = rN'.chib i ((Q.gN N).p₀ a) := by rw [hc1.1 i]; rfl
      have e2 : r.chib i ((T.h N).p₀ a) = r'.chib i (Q.g0.p₀ ((T.h N).p₀ a)) := by rw [hC.1 i]; rfl
      rw [← e1, hchi, e2]
    · exact hc1.2.1.symm.trans ((W.A N).compat.2.1.trans hr)
    · exact hc1.2.2.symm.trans ((W.A N).compat.2.2.trans hC.2.2)
  choose rN' hc p' hp hpD using key
  refine ⟨⟨baseDesc W.b hr hψ, W.ut, ?_, fun N => ringDesc (W.A N) hr hψ (rN' N) (hc N) (p' N) (hp N),
    W.ex, fun N => ?_⟩⟩
  · intro j i
    rw [W.ut_res j i, hC.1 i]
    rfl
  · exact (maps_desc (W.A N) hr hψ (rN' N) (hc N) (p' N) (hp N) Q.g0 (Q.gN N) (Q.comm₀ N) hD (hpD N)
      (T.Nq N) (T.ph N) (T.ta N) W.ex (W.m N)).some
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.NonssDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_surj {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p) :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom R p) := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | single g c =>
    obtain ⟨g', rfl⟩ := hp g
    exact ⟨MonoidAlgebra.single g' c, by simp⟩

private theorem md_ker {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (J : TwoSidedIdeal (MonoidAlgebra R G)) (hJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z = 0) : z ∈ J := by
  choose s hs using hp
  have key : ∀ z : MonoidAlgebra R G,
      z - MonoidAlgebra.mapDomain s (MonoidAlgebra.mapDomainRingHom R p z) ∈ J := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), MonoidAlgebra.mapDomain_add, add_sub_add_comm]
      exact J.add_mem ha hb
    | single g c =>
      have h := J.mul_mem_left (MonoidAlgebra.single (s (p g)) c) _ (hJ ((s (p g))⁻¹ * g) (by simp [hs]))
      rw [mul_sub, MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_inv_cancel_left] at h
      simpa using h
  have := key z
  rw [hz] at this
  simpa using this

private theorem md_span {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (J : TwoSidedIdeal (MonoidAlgebra R G)) (hJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J)
    (S : Set (MonoidAlgebra R G')) (hS : ∀ y ∈ S, ∃ x ∈ J, MonoidAlgebra.mapDomainRingHom R p x = y)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z ∈ TwoSidedIdeal.span S) : z ∈ J := by
  have key : ∀ y ∈ TwoSidedIdeal.span S, ∃ x ∈ J, MonoidAlgebra.mapDomainRingHom R p x = y := by
    intro y hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y hy => exact hS y hy
    | zero => exact ⟨0, J.zero_mem, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨b', h2, rfl⟩ := hb
      exact ⟨a' + b', J.add_mem h1 h2, map_add _ _ _⟩
    | neg a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      exact ⟨-a', J.neg_mem h1, map_neg _ _⟩
    | left_absorb c a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨c', rfl⟩ := md_surj (R := R) p hp c
      exact ⟨c' * a', J.mul_mem_left _ _ h1, map_mul _ _ _⟩
    | right_absorb c a _ ha =>
      obtain ⟨a', h1, rfl⟩ := ha
      obtain ⟨c', rfl⟩ := md_surj (R := R) p hp c
      exact ⟨a' * c', J.mul_mem_right _ _ h1, map_mul _ _ _⟩
  obtain ⟨x, hx, e⟩ := key _ hz
  have := J.add_mem (md_ker p hp J hJ (z - x) (by rw [map_sub, e, sub_self])) hx
  rwa [sub_add_cancel] at this

private theorem nonSS_down {R G G' : Type} [CommRing R] [Group G] [Group G'] (p : G →* G') (hp : Function.Surjective p)
    (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R G'))
    (hk : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ I)
    (hI : ∀ z, MonoidAlgebra.mapDomainRingHom R p z ∈ I' → z ∈ I) (Q : Ideal R) :
    NonSS I (RingHom.id R) Q → NonSS I' (RingHom.id R) Q := by
  rintro ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  rw [RingHom.comp_id] at hs ⊢
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G f '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' f '' I') with hJ'
  have hcomm : ∀ w : MonoidAlgebra R G,
      MonoidAlgebra.mapDomainRingHom κ p (MonoidAlgebra.mapRingHom G f w) =
        MonoidAlgebra.mapRingHom G' f (MonoidAlgebra.mapDomainRingHom R p w) := by
    intro w
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hkJ : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ J := fun k h =>
    TwoSidedIdeal.subset_span ⟨_, hk k h, by rw [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one]⟩
  have hpre : ∀ z, MonoidAlgebra.mapDomainRingHom κ p z ∈ J' → z ∈ J := by
    refine md_span p hp J hkJ _ ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := md_surj (R := R) p hp y
    exact ⟨_, TwoSidedIdeal.subset_span ⟨x, hI x hy, rfl⟩, hcomm x⟩
  have hs' := md_surj (R := κ) p hp
  have hle : RingHom.ker (MonoidAlgebra.mapDomainRingHom κ p) ≤ RingHom.ker J.ringCon.mk' := by
    intro z hz
    rw [RingHom.mem_ker] at hz ⊢
    have h1 : z - 0 ∈ J := by rw [sub_zero]; exact md_ker p hp J hkJ z hz
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h1)
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    (MonoidAlgebra.mapDomainRingHom κ p).liftOfSurjective hs' ⟨J.ringCon.mk', hle⟩
  have hψ : ∀ x, ψ (MonoidAlgebra.mapDomainRingHom κ p x) = J.ringCon.mk' x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    obtain ⟨a, rfl⟩ := hs' a
    obtain ⟨b, rfl⟩ := hs' b
    have h1 := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    rw [← map_sub] at h1
    rw [hψ, hψ]
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (hpre _ h1))
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := RingCon.mk'_surjective _ y
  exact ⟨((MonoidAlgebra.mapDomainRingHom κ p x : MonoidAlgebra κ G') : J'.ringCon.Quotient), hψ x⟩

private theorem closure_down {R G G' : Type} [CommRing R] [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    (p : G →* G') (hp : Function.Surjective p) (ho : IsOpenMap p) (m : Ideal R)
    (S : Set (MonoidAlgebra R G)) (S' : Set (MonoidAlgebra R G'))
    (hk : ∀ k, p k = 1 → MonoidAlgebra.single k 1 - 1 ∈ closureIdeal m S)
    (hS : ∀ y ∈ S', ∃ x ∈ S, MonoidAlgebra.mapDomainRingHom R p x = y)
    (z : MonoidAlgebra R G) (hz : MonoidAlgebra.mapDomainRingHom R p z ∈ closureIdeal m S') : z ∈ closureIdeal m S := by
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf] at hk hz ⊢
  intro N V
  let V' : OpenNormalSubgroup G' :=
    { toSubgroup := V.toSubgroup.map p
      isOpen' := ho _ V.isOpen'
      isNormal' := V.isNormal'.map p hp }
  refine md_span p hp _ (fun k h => hk k h N V) _ ?_ z (hz N V')
  rintro y ((hy | ⟨a, ha, rfl⟩) | ⟨_, ⟨h, hh, rfl⟩, rfl⟩)
  · obtain ⟨x, hx, e⟩ := hS y hy
    exact ⟨x, TwoSidedIdeal.subset_span (Or.inl (Or.inl hx)), e⟩
  · exact ⟨MonoidAlgebra.single 1 a, TwoSidedIdeal.subset_span (Or.inl (Or.inr ⟨a, ha, rfl⟩)), by simp⟩
  · exact ⟨MonoidAlgebra.single h 1 - 1, TwoSidedIdeal.subset_span (Or.inr ⟨h, hh, rfl⟩), by
      rw [map_sub, map_one]; simp⟩

theorem UpperTheory.V.Pa.nonss_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (r' : Resid G'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → g.p.ker = PL l H → Glob.Compat g r r' → u'.D.comap g.p₀ = u.D → u'.ψ = u.ψ → ∀ q : Ideal B, (NonSS (augmentationIdealKernel u) (RingHom.id B) q → NonSS (augmentationIdealKernel u') (RingHom.id B) q) ∧ (DiscSt u.D q ↔ DiscSt u'.D q) := by
  intro l _ L G G' g n O _ _ _ _ _ r r' B _ _ _ u u' H _ hHo hHle hHchi hker hcomp hD hψ q
  refine ⟨?_, ?_⟩
  · have hk : ∀ k : G.G₀, g.p₀ k = 1 → MonoidAlgebra.single k 1 - 1 ∈ u.D.chBar (pairGens u) := fun k h =>
      pl_chBar l L G n O r B u H hHo hHle hHchi _ k (by
        rw [← hker, MonoidHom.mem_ker]; exact congrArg Subtype.val h)
    have ho : IsOpenMap g.p₀ := (MonoidHom.isOpenQuotientMap_of_isQuotientMap g.p₀_quot).isOpenMap
    obtain ⟨hst, hoel, -⟩ := map_star l L G G' g n O B
    have hCH := ((comap_lam n B _ _ g.p₀ u'.D).2.2.2.2.2 g.p₀_surj).2
    rw [hD] at hCH
    refine nonSS_down g.p₀ g.p₀_surj _ _ hk (fun z hz => ?_) q
    refine closure_down g.p₀ g.p₀_surj ho _ _ _ hk ?_ z hz
    rintro y (hy | ⟨v, a, h⟩ | ⟨w, _, ⟨⟨a, ha, rfl⟩, hb⟩, h⟩)
    · rw [← hCH] at hy
      obtain ⟨x, hx, e⟩ := hy
      exact ⟨x, Or.inl hx, e⟩
    · rw [hψ] at h
      rcases h with rfl | rfl
      · exact ⟨_, Or.inr (Or.inl ⟨v, a, Or.inl rfl⟩), hoel v _ a⟩
      · exact ⟨_, Or.inr (Or.inl ⟨v, a, Or.inr rfl⟩), by rw [hst]; exact congrArg _ (hoel v _ a)⟩
    · have hm : G.φu w a ∈ r.Ip w := by
        refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
        have hb' : r'.chib i (G'.φu w a) = 1 := Subgroup.mem_iInf.1 hb i
        have e1 : r.chib i (G.φu w a) = r'.chib i (g.p₀ (G.φu w a)) := DFunLike.congr_fun (hcomp.1 i) _
        rw [g.p₀_φu] at e1
        exact e1.trans hb'
      have e : MonoidAlgebra.mapDomainRingHom B g.p₀ (MonoidAlgebra.single (G.φu w a) 1) =
          MonoidAlgebra.single (G'.φu w a) 1 := by
        rw [← g.p₀_φu]; simp
      rcases h with rfl | rfl
      · exact ⟨_, Or.inr (Or.inr ⟨w, _, hm, Or.inl rfl⟩), by rw [map_sub, map_one, e]⟩
      · exact ⟨_, Or.inr (Or.inr ⟨w, _, hm, Or.inr rfl⟩), by rw [map_sub, map_one, hst, e]⟩
  · rw [← hD]
    exact (BC.discSt_map n B B _ u'.D).2.1 _ g.p₀ g.p₀_surj q
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TwquotEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomDesc
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.hom_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (A A' B B' : Glob l L) (a : A.Hom A') (b : B.Hom B') (h : A.Hom B), a.p.ker ≤ (b.p.comp h.p).ker → ∃ h' : A'.Hom B', ∀ x, h'.p (a.p x) = b.p (h.p x) := by
  intro l _ L A A' B B' a b h hk
  have hT1 : T1Space A'.Γ := by
    refine ⟨fun x => ?_⟩
    have h1 : IsPreconnected (closure ({x} : Set A'.Γ)) := isPreconnected_singleton.closure
    have h2 := h1.subsingleton
    have h3 : closure ({x} : Set A'.Γ) = {x} :=
      h2.eq_singleton_of_mem (subset_closure (Set.mem_singleton x))
    exact closure_eq_iff_isClosed.mp h3
  have hT2 : T2Space A'.Γ := inferInstance
  let q : A'.Γ →* B'.Γ := a.p.liftOfRightInverse (Function.surjInv a.surj)
    (Function.rightInverse_surjInv a.surj) ⟨b.p.comp h.p, hk⟩
  have hq : ∀ x, q (a.p x) = b.p (h.p x) := fun x =>
    a.p.liftOfRightInverse_comp_apply _ _ ⟨b.p.comp h.p, hk⟩ x
  have hquot : Topology.IsQuotientMap a.p :=
    a.cont.isClosedMap.isQuotientMap a.cont a.surj
  refine ⟨⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hq⟩
  · rw [hquot.continuous_iff]
    have : (q : A'.Γ → B'.Γ) ∘ a.p = fun x => b.p (h.p x) := funext hq
    rw [this]
    exact b.cont.comp h.cont
  · intro y
    obtain ⟨z, rfl⟩ := b.surj y
    obtain ⟨x, rfl⟩ := h.surj z
    exact ⟨a.p x, hq x⟩
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.η, h.η, a.η]
  · rw [← a.c, hq, h.c, b.c]
  · intro g
    obtain ⟨x, rfl⟩ := a.surj g
    rw [hq, b.ε, h.ε, a.ε]
  · intro v g
    rw [← a.φ, hq, h.φ, b.φ]
  · intro v g
    rw [← a.φu, hq, h.φu, b.φu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.QuotEx
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem pl_le_ker {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ)
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (h1 : ∀ a ∈ H, PadicInt.toZMod ((ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1) :
    PL l H ≤ ε.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have key : ∀ k : ℕ, PadicInt.toZModPow k ((ε x : ℤ_[l])) = 1 := by
    intro k
    let χ : Γ →* (ZMod (l ^ k))ˣ :=
      (Units.map (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)).toMonoidHom).comp ε
    have hmemχ : ∀ g, g ∈ χ.ker ↔
        (ε g : ℤ_[l]) ∈ Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(k : ℤ))) := by
      intro g
      rw [MonoidHom.mem_ker, Metric.mem_closedBall, dist_eq_norm,
        PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_one, sub_eq_zero, Units.ext_iff]
      rfl
    have hopen : IsOpen (χ.ker : Set Γ) := by
      have hset : (χ.ker : Set Γ) =
          (fun g => (ε g : ℤ_[l])) ⁻¹' Metric.closedBall 1 ((l : ℝ) ^ (-(k : ℤ))) := by
        ext g
        exact hmemχ g
      rw [hset]
      exact (IsUltrametricDist.isOpen_closedBall _
        (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))).preimage
        (Units.continuous_val.comp hε)
    let U : OpenNormalSubgroup Γ := ⟨⟨χ.ker, hopen⟩, χ.normal_ker⟩
    have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨k, ?_⟩
      show h ^ l ^ k ∈ χ.ker
      rw [hmemχ, map_pow, Units.val_pow_eq_pow_val, Metric.mem_closedBall, dist_eq_norm,
        PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
      have hd : (l : ℤ_[l]) ∣ (ε h : ℤ_[l]) - 1 := by
        rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
          RingHom.mem_ker, map_sub, map_one, h1 h hh, sub_self]
      have hp := dvd_sub_pow_of_dvd_sub hd k
      rw [one_pow] at hp
      exact (pow_dvd_pow _ (Nat.le_succ k)).trans hp
    have hle : PL l H ≤ (U.toOpenSubgroup : Subgroup Γ) := by
      unfold PL
      exact (iInf_le _ U).trans (iInf_le _ hcond)
    have hxU : x ∈ χ.ker := hle hx
    rw [MonoidHom.mem_ker] at hxU
    have hv := congrArg Units.val hxU
    simpa [χ] using hv
  exact Units.ext (PadicInt.ext_of_toZModPow.mp (fun k => by rw [key k, Units.val_one, map_one]))

theorem UpperTheory.V.Pa.quot_ex :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a ∈ H, PadicInt.toZMod ((G.ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1) → ∃ (G' : Glob l L) (g : G.Hom G'), g.p.ker = PL l H := by
  intro l _ L G H _ hH hη hε1
  have hN : (PL l H).Normal := by
    constructor
    intro x hx g
    simp only [PL, Subgroup.mem_iInf] at hx ⊢
    intro U hU
    exact U.isNormal'.conj_mem _ (hx U hU) g
  have hC : IsClosed (PL l H : Set G.Γ) := by
    simp only [PL, Subgroup.coe_iInf]
    exact isClosed_iInter fun U => isClosed_iInter fun _ => U.toOpenSubgroup.isClosed
  have hKH : PL l H ≤ H := by
    let U : OpenNormalSubgroup G.Γ := ⟨⟨H, hH⟩, inferInstance⟩
    have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨0, ?_⟩
      change h ^ l ^ 0 ∈ H
      simpa using hh
    exact (iInf_le _ U).trans (iInf_le _ hcond)
  haveI := hN
  let π : G.Γ →* G.Γ ⧸ PL l H := QuotientGroup.mk' (PL l H)
  have hπc : Continuous π := QuotientGroup.continuous_mk
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπo : IsOpenMap π := QuotientGroup.isOpenMap_coe
  have hπq : Topology.IsQuotientMap π := hπo.isQuotientMap hπc hπs
  haveI : TotallyDisconnectedSpace (G.Γ ⧸ PL l H) := (totallyDisconnected_quot G.Γ _ hC).1
  let η' : G.Γ ⧸ PL l H →* ℤˣ := QuotientGroup.lift (PL l H) G.η (hKH.trans hη)
  let ε' : G.Γ ⧸ PL l H →* ℤ_[l]ˣ :=
    QuotientGroup.lift (PL l H) G.ε (pl_le_ker H G.ε G.ε_cont hε1)
  have hηo : IsOpen (η'.ker : Set (G.Γ ⧸ PL l H)) := by
    have hset : (η'.ker : Set (G.Γ ⧸ PL l H)) = π '' (G.η.ker : Set G.Γ) := by
      ext y
      obtain ⟨x, rfl⟩ := hπs y
      constructor
      · intro hy
        exact ⟨x, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        show η' (π x) = 1
        rw [← hzx]
        exact hz
    rw [hset]
    exact hπo _ G.η_open
  have hεc : Continuous ε' := by
    rw [hπq.continuous_iff]
    exact G.ε_cont
  let r : G.η.ker →* η'.ker :=
    (π.comp G.η.ker.subtype).codRestrict η'.ker (fun x => by
      show η' (π x) = 1
      exact x.2)
  have hrc : Continuous r := continuous_induced_rng.2 (hπc.comp continuous_subtype_val)
  let G' : Glob l L :=
    { Γ := G.Γ ⧸ PL l H
      η := η'
      η_open := hηo
      c := π G.c
      c_sq := by rw [← map_mul, G.c_sq, map_one]
      η_c := G.η_c
      ε := ε'
      ε_cont := hεc
      φ := fun v => r.comp (G.φ v)
      φ_cont := fun v => hrc.comp (G.φ_cont v)
      φu := fun u => r.comp (G.φu u)
      φu_cont := fun u => hrc.comp (G.φu_cont u) }
  refine ⟨G', ⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
  exact QuotientGroup.ker_mk' _
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_desc {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (g : G.Hom G')
    (H : OpenNormalSubgroup G.Γ) (hk : g.p.ker ≤ H.toSubgroup) :
    ∃ H' : OpenNormalSubgroup G'.Γ, H'.toSubgroup.comap g.p = H.toSubgroup := by
  have e : (H.toSubgroup.map g.p).comap g.p = H.toSubgroup := Subgroup.comap_map_eq_self hk
  have hq : Topology.IsQuotientMap g.p := g.cont.isClosedMap.isQuotientMap g.cont g.surj
  have ho : IsOpen (H.toSubgroup.map g.p : Set G'.Γ) := by
    rw [← hq.isOpen_preimage, ← Subgroup.coe_comap, e]
    exact H.toOpenSubgroup.isOpen
  exact ⟨{ toSubgroup := H.toSubgroup.map g.p, isOpen' := ho, isNormal' := H.isNormal'.map _ g.surj }, e⟩

theorem UpperTheory.V.Pa.twquot_ex :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), Nonempty (TWQuot T) := by
  intro l _ L G0 T
  haveI hn : T.H.toSubgroup.Normal := T.H.isNormal'
  have ho : IsOpen (T.H.toSubgroup : Set G0.Γ) := T.H.toOpenSubgroup.isOpen
  have hoN : ∀ N, IsOpen (T.H.toSubgroup.comap (T.h N).p : Set (T.GN N).Γ) := fun N => ho.preimage (T.h N).cont
  obtain ⟨G0', g0, ker0⟩ := quot_ex l L G0 T.H.toSubgroup ho (fun a ha => T.H_η a ha) (fun a ha => T.H_ε a ha)
  have hN : ∀ N, ∃ (G' : Glob l L) (g : (T.GN N).Hom G'), g.p.ker = PL l (T.H.toSubgroup.comap (T.h N).p) :=
    fun N => quot_ex l L (T.GN N) _ (hoN N)
      (fun a ha => show (T.GN N).η a = 1 by rw [← (T.h N).η]; exact T.H_η _ ha)
      (fun a ha => by rw [← (T.h N).ε]; exact T.H_ε _ ha)
  choose GN' gN kerN using hN
  have hmap : ∀ N, (gN N).p.ker.map (T.h N).p = g0.p.ker := fun N => by
    rw [kerN, ker0]
    exact pl_map l _ _ (T.h N).p T.H.toSubgroup ho (T.h N).cont (T.h N).surj
  have hd : ∀ N, ∃ h' : (GN' N).Hom G0', ∀ x, h'.p ((gN N).p x) = g0.p ((T.h N).p x) := fun N =>
    hom_desc l L _ _ _ _ (gN N) g0 (T.h N) fun a ha => by
      have : (T.h N).p a ∈ g0.p.ker := hmap N ▸ Subgroup.mem_map_of_mem _ ha
      exact this
  choose h' comm using hd
  obtain ⟨H', hH'⟩ := exists_desc g0 T.H (ker0 ▸ (pl_props l G0.Γ T.H.toSubgroup ho).2.2.1)
  haveI hn' : H'.toSubgroup.Normal := H'.isNormal'
  have ho' : IsOpen (H'.toSubgroup : Set G0'.Γ) := H'.toOpenSubgroup.isOpen
  have hiff : ∀ a, g0.p a ∈ H' ↔ a ∈ T.H := fun a => by
    show a ∈ H'.toSubgroup.comap g0.p ↔ a ∈ T.H.toSubgroup
    rw [hH']
  have hcN : ∀ N, (H'.toSubgroup.comap (h' N).p).comap (gN N).p = T.H.toSubgroup.comap (T.h N).p := fun N => by
    ext a
    show (h' N).p ((gN N).p a) ∈ H' ↔ (T.h N).p a ∈ T.H
    rw [comm, hiff]
  refine ⟨{ G0' := G0', g0 := g0, ker0 := ker0, GN' := GN', gN := gN, kerN := kerN, h' := h', comm := comm
            H' := H', H'_iff := hiff, ph_lim := fun V j => ?_, ker_le := fun N => ?_, fin0 := ?_
            finN := fun N => ?_, pl0 := ?_, plN := fun N => ?_ }⟩
  · let V' : OpenNormalSubgroup G0.Γ :=
      { toOpenSubgroup := V.toOpenSubgroup.comap g0.p g0.cont
        isNormal' := Subgroup.Normal.comap V.isNormal' g0.p }
    refine T.ph_lim V' j fun a ha => ?_
    rw [← ker0, MonoidHom.mem_ker] at ha
    show g0.p a ∈ V.toSubgroup
    rw [ha]; exact one_mem _
  · intro x hx
    obtain ⟨a, rfl⟩ := (gN N).surj x
    have h1 : (T.h N).p a ∈ (gN N).p.ker.map (T.h N).p := by
      rw [hmap, MonoidHom.mem_ker, ← comm]; exact hx
    obtain ⟨b, hb, hba⟩ := h1
    have h2 : a * b⁻¹ ∈ (T.h N).p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, mul_inv_cancel]
    have h3 : (gN N).p a = (gN N).p (a * b⁻¹) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hb, inv_one, mul_one]
    rw [h3]
    have h4 : (Subgroup.normalClosure (Set.range fun j => (T.ta N j : (T.GN N).Γ)) ⊔
        PL l (T.H.toSubgroup.comap (T.h N).p)).topologicalClosure ≤
        (Subgroup.normalClosure (Set.range fun j => (gN N).p (T.ta N j))).topologicalClosure.comap (gN N).p := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
        ((Subgroup.isClosed_topologicalClosure _).preimage (gN N).cont)
      · refine le_trans ?_ (Subgroup.comap_mono (Subgroup.le_topologicalClosure _))
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨j, rfl⟩
        exact Subgroup.subset_normalClosure ⟨j, rfl⟩
      · rw [← kerN]; exact MonoidHom.ker_le_comap _ _
    exact h4 (T.ker_le N h2)
  · exact (homl_desc l _ _ g0.p H'.toSubgroup g0.cont g0.surj (hH' ▸ T.fin0)).1
  · have := homl_desc l _ _ (gN N).p (H'.toSubgroup.comap (h' N).p) (gN N).cont (gN N).surj
      (by rw [hcN]; exact (T.finN N).1)
    rw [hcN] at this
    exact ⟨this.1, this.2.trans (T.finN N).2⟩
  · rw [← pl_map l _ _ g0.p H'.toSubgroup ho' g0.cont g0.surj, hH', ← ker0, Subgroup.map_eq_bot_iff]
  · rw [← pl_map l _ _ (gN N).p (H'.toSubgroup.comap (h' N).p) (ho'.preimage (h' N).cont) (gN N).cont (gN N).surj,
      hcN, ← kerN, Subgroup.map_eq_bot_iff]
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.raw_main :
    CoreBC → Raw := by
  intro core l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A hl hA hgen h x hcard
  obtain ⟨Q⟩ := twquot_ex l L G0 T
  have hopen : IsOpen (T.H.toSubgroup : Set G0.Γ) := T.H.toOpenSubgroup.isOpen
  have hle : T.H.toSubgroup ≤ G0.η.ker := fun a ha => T.H_η a ha
  have hPL : PL l T.H.toSubgroup ≤ T.H.toSubgroup := (pl_props l G0.Γ T.H.toSubgroup hopen).2.2.1
  obtain ⟨r', hc, hIp⟩ := resid_desc l L G0 Q.G0' Q.g0 n O r (fun a ha i => hA.1 a (hPL (by
    rw [← Q.ker0, MonoidHom.mem_ker, ← Glob.Hom.coe_p₀, ha]; rfl)) i)
  obtain ⟨u', hD, hψ⟩ := pair_desc l L G0 Q.G0' Q.g0 n O r r' B u T.H.toSubgroup hopen hle hA.1 Q.ker0 hc
  obtain ⟨A'⟩ := aut_desc l L G0 T Q n O r r' B u u' J Empty D hA hc hD hψ A
  choose x' hker hK using fun i => pt_desc l L G0 T Q n O r r' B u u' (D + n * T.q) (x i) hA hc hD hψ
  have hns := nonss_desc l L G0 Q.G0' Q.g0 n O r r' B u u' T.H.toSubgroup hopen hle hA.1 Q.ker0 hc hD hψ
  have hA' : Adapted Q.grp (r := r') := by
    refine ⟨fun g hg i => ?_, hIp hA.2⟩
    obtain ⟨a, rfl⟩ := Q.g0.p₀_surj g
    have := hA.1 a ((Q.H'_iff a).1 hg) i
    rw [hc.1 i] at this
    exact this
  have hsub : pairVals u ⊆ pairVals u' := by
    rintro b (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
    · refine Or.inl ⟨i, Q.g0.p₀ g, ?_⟩
      rw [← hD, (comap_lam n B _ _ Q.g0.p₀ u'.D).2.1]
      congr 1
      exact MonoidAlgebra.mapDomain_single
    · exact Or.inr ⟨v, i, g, by rw [hψ]⟩
  have hgen' : GenBy O (pairVals u') := fun N b =>
    (hgen N b).imp fun a ha => ⟨Algebra.adjoin_mono hsub ha.1, ha.2⟩
  have main := core l L Q.G0' Q.grp n O r' B u' J D A' hl Q.proL hA' hgen' h x'
    (fun i => by rw [hK i, hK 0]; exact hcard i)
  have hfun : (fun i => RingHom.ker (x' i).f) = fun i => RingHom.ker (x i).f := funext hker
  rw [hfun] at main
  intro e he hq q hqp hqle hst
  refine main e (fun i => ⟨(he i).1, (hns _).1 (he i).2.1, (he i).2.2⟩) ?_ q hqp hqle ?_
  · obtain ⟨q₁, h1, h2, h3⟩ := hq
    exact ⟨q₁, h1, (hns _).2.1 h2, h3⟩
  · exact hst.imp (hns q).2.1 (hns q).1
