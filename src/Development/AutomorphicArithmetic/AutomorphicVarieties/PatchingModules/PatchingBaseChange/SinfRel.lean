module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime]

structure SinfRel (l : ℕ) {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {D q n : ℕ}
    (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) :
    Prop where
  X : ∀ p, τS (Til.ι O O' _ (MvPowerSeries.X p)) = MvPowerSeries.X p
  C : ∀ a : abelian₂ O Empty D, τS (Til.ι O O' _ (MvPowerSeries.C a)) = MvPowerSeries.C (lamEmb O O' D a)
  cc : ∀ c : Sinf O Empty D q n →ₐ[O] abelian₂ O Empty D, (∀ z, c z = MvPowerSeries.constantCoeff z) →
    ∀ z, MvPowerSeries.constantCoeff (τS z) = τ (Til.map O' c z)
  del : ∀ a : Fin q → ℕ, delIdeal l (abelian₂ O' Unit D) n a =
    (delIdeal l (abelian₂ O Empty D) n a).map ((τS.toRingEquiv : _ →+* Sinf O' Unit D q n).comp (Til.ι O O' _))

structure RingRel {L : Loc} {G0 G : Glob l L} {O O' : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CommRing O']
    [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] {n : ℕ} {r : Resid G0.frame O n} {r' : Resid G0.frame O' n}
    {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {B' : Type} [CommRing B'] [Algebra O' B'] [IsCO O' B']
    {u : Pair r B} {u' : Pair r' B'} {J : Ideal B} {J' : Ideal B'} {D : ℕ} {b : TWBase u J Empty D}
    {b' : TWBase u' J' Unit D} {h : G.Hom G0} {q : ℕ} {ut : Fin q → Fin n → O} {ut' : Fin q → Fin n → O'} {N : ℕ}
    (A : TWRing b h ut N) (A' : TWRing b' h ut' N)
    (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) where
  ρ : Til O O' A.R ≃ₐ[O'] A'.R
  maps : A.p.Maps ((ρ.toRingEquiv : _ →+* A'.R).comp (Til.ι O O' A.R)) A'.p.D A'.p.ψ
  s : ∀ z, A'.s (τS z) = ρ (Til.map O' A.s z)
  U : ∀ j i, A'.U j i = ρ (Til.ι O O' A.R (A.U j i))
  ν : Til O O' A.R ⊗[A.R] A.M ≃+ A'.M
  ν_smul : ∀ t m, ν (t • m) = ρ t • ν m

end UpperTheory.V.Pa
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem gdet_ofRep_diagRep_map_eq_ofRep_pushCh {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G]
    (χ : Fin n → G →* Aˣ) (f : A →+* A') :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep (fun i => pushCh f (χ i))) := by
  refine GDet.ext fun B _ _ x => ?_
  simp only [GDet.map, GDet.ofRep, GDet.repAlg]
  congr 4
  apply congrArg
  refine MonoidHom.ext fun s => ?_
  ext i j
  simp [diagRep, pushCh, Matrix.diagonal_apply, RingHom.algebraMap_toAlgebra]
  split_ifs <;> simp

private theorem gdet_map_chi_mapRingHom_eq_map_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (x : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  letI : Algebra A (Polynomial A') := ((algebraMap A' (Polynomial A')).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial A' :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have key := D.nat (Polynomial A) (Polynomial A') φ
    (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
  have e : (MonoidAlgebra.mapRingHom G (φ : Polynomial A →+* Polynomial A'))
        (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
      = MonoidAlgebra.single 1 Polynomial.X
          - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.mapRingHom G f x) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · simp [φ, Polynomial.mapRingHom]
    · ext g
      simp [φ, Polynomial.mapRingHom, MonoidAlgebra.mapRingHom]
  rw [e] at key
  exact key

private theorem gdet_map_lam_mapRingHom_eq_lam {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (i : ℕ) (x : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f x) = f (D.lam i x) := by
  simp only [GDet.lam, gdet_map_chi_mapRingHom_eq_map_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

private theorem adicCont_maximalIdeal_comp_of_isLocalHom {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (g : R →+* R') [IsLocalHom g] {φ : Γ → R}
    (h : AdicCont (maximalIdeal R) φ) : AdicCont (maximalIdeal R') (fun x => g (φ x)) := by
  intro N
  have hm : (maximalIdeal R).map g ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit g x hx
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap g := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have := (h N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) g hle)
  convert this using 1
  funext x
  simp [Ideal.quotientMap_mk]

private theorem res_eq_zero_of_mem_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (x : R) (hx : x ∈ maximalIdeal R) : res O R x = 0 := by
  show ((RingEquiv.ofBijective _ _).symm.toRingHom.comp (residue R)) x = 0
  simp [(IsLocalRing.residue_eq_zero_iff x).mpr hx]

theorem UpperTheory.V.Pa.BC.pair_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n) (r' : Resid F O' n), RBC r r' → ∀ (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O' R'] [IsCO O' R'] (g : R →+* R') [IsLocalHom g], (∀ a, g (algebraMap O R a) = algebraMap O' R' (algebraMap O O' a)) → ∀ p : Pair r R, (∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x)) ∧ ∃ p' : Pair r' R', p.Maps g p'.D p'.ψ := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r r' hr R R' _ _ _ _ _ _ g _ hg p
  have hres : ∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    have hx : x = algebraMap O R a + (x - algebraMap O R a) := by ring
    have h2 : g (x - algebraMap O R a) ∈ maximalIdeal R' := map_nonunit g _ ha
    rw [hx, map_add (f := _), map_add (f := _), map_add (f := _), hg, res_eq_zero_of_mem_maximalIdeal _ h2, res_eq_zero_of_mem_maximalIdeal _ ha, add_zero, add_zero,
      AlgHom.commutes, AlgHom.commutes, ResidueField.algebraMap_eq, ResidueField.algebraMap_eq,
      ResidueField.map_residue]
  have hs1 : ∀ h : F.G₀, (MonoidAlgebra.single h (1 : R') : MonoidAlgebra R' F.G₀)
      = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1) := by
    intro h
    simp [MonoidAlgebra.mapRingHom_single]
  refine ⟨hres, ⟨⟨p.D.map g, fun v i => pushCh g (p.ψ v i), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl⟩⟩
  · intro i
    have key : (fun h : F.G₀ => (p.D.map g).lam i (MonoidAlgebra.single h 1))
        = fun h => g (p.D.lam i (MonoidAlgebra.single h 1)) := by
      funext h
      rw [hs1, gdet_map_lam_mapRingHom_eq_lam]
    show AdicCont _ _
    rw [key]
    exact adicCont_maximalIdeal_comp_of_isLocalHom g (p.cont i)
  · have hrg : ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O').comp g
        = (ResidueField.map (algebraMap O O')).comp ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) :=
      RingHom.ext hres
    have e1 : (p.D.map g).map ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O')
        = (p.D.map ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O)).map
            (ResidueField.map (algebraMap O O')) := by
      refine GDet.ext fun B _ _ x => ?_
      simp only [GDet.map]
      congr 2
      congr 1
      refine RingHom.ext fun y => ?_
      show algebraMap (ResidueField O') B (res O' R' (g y)) = algebraMap (ResidueField O') B (ResidueField.map (algebraMap O O') (res O R y))
      rw [hres]
    rw [e1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (diagRep r'.chib)
    rw [gdet_ofRep_diagRep_map_eq_ofRep_pushCh]
    congr 2
    funext i
    exact (hr.1 i).symm
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · have := adicCont_maximalIdeal_comp_of_isLocalHom g (p.psi v i).cont
      simpa [pushCh] using this
    · intro x
      have h1 := (p.psi v i).red x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [hres, h1, hr.2.1 v i]
      simp [pushCh]
    · intro x
      have h1 := (p.psi v i).mu x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [h1, hg, hr.2.2 v i]
      simp [pushCh]
  · intro i h
    have he : ∀ y : F.G₀, Units.map (g : R →* R') (F.eps O R y) = F.eps O' R' y := by
      intro y
      ext
      simp [GFrame.eps, pushCh, hg, ← IsScalarTower.algebraMap_apply]
    have hs : F.star O' R' n (MonoidAlgebra.single h 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n (MonoidAlgebra.single h 1)) := by
      simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.mapRingHom_single, ← he]
      rw [← map_zpow]
      rfl
    rw [hs, hs1, gdet_map_lam_mapRingHom_eq_lam, gdet_map_lam_mapRingHom_eq_lam, p.P]
  · intro v gg h
    have e : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh g (p.ψ v i)) gg
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) gg) := by
      rw [map_mul, ← hs1]
      congr 1
      simp [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def, pushCh,
        MonoidAlgebra.mapRingHom_single]
    have h0 := p.Ord v gg h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
  · intro u x hx h
    have hx' : x ∈ r.Ip u := by
      simp only [Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx ⊢
      refine ⟨hx.1, fun i => ?_⟩
      have h2 := hx.2 i
      rw [hr.1 i] at h2
      ext
      have h3 := congrArg (fun u : (ResidueField O')ˣ => (u : ResidueField O')) h2
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h3
      apply (ResidueField.map (algebraMap O O')).injective
      rw [h3, Units.val_one, map_one]
    have e : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single x 1 - 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * (MonoidAlgebra.single x 1 - 1)) := by
      simp [MonoidAlgebra.mapRingHom_single]
    have h0 := p.I u x hx' h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.StarMap
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.star_map :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing O'] [Algebra ℤ_[l] O'] (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O' R'] (g : R →+* R'), (∀ a : ℤ_[l], g (algebraMap O R (algebraMap ℤ_[l] O a)) = algebraMap O' R' (algebraMap ℤ_[l] O' a)) → (pushCh g (F.eps O R) = F.eps O' R') ∧ (∀ n y, MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n y) = F.star O' R' n (MonoidAlgebra.mapRingHom F.G₀ g y)) ∧ ∀ (n : ℕ) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ) (γ : Fin n → F.Gv v), MonoidAlgebra.mapRingHom F.G₀ g (F.oEl v ψ γ) = F.oEl v (fun i => pushCh g (ψ i)) γ := by
  intro l _ F O O' _ _ _ _ R R' _ _ _ _ g hg
  have h1 : pushCh g (F.eps O R) = F.eps O' R' := by
    ext x
    simp [GFrame.eps, pushCh, hg]
  have hs : ∀ (S : Type) [CommRing S] [Algebra O S] (n : ℕ) (h : F.G₀) (r : S), F.star O S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hs' : ∀ (S : Type) [CommRing S] [Algebra O' S] (n : ℕ) (h : F.G₀) (r : S), F.star O' S n (MonoidAlgebra.single h r) = MonoidAlgebra.single (F.conj h)⁻¹ (r * ((F.eps O' S h ^ (1 - (n : ℤ)) : Sˣ) : S)) := by
    intro S _ _ n h r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hadd : ∀ (n : ℕ) (a b : MonoidAlgebra R F.G₀), F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro n a b
    simp [GFrame.star]
  have hadd' : ∀ (n : ℕ) (a b : MonoidAlgebra R' F.G₀), F.star O' R' n (a + b) = F.star O' R' n a + F.star O' R' n b := by
    intro n a b
    simp [GFrame.star]
  have hz : ∀ (n : ℕ), F.star O R n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have hz' : ∀ (n : ℕ), F.star O' R' n 0 = 0 := by
    intro n
    simp [GFrame.star]
  have he : ∀ (h : F.G₀) (k : ℤ), g ((F.eps O R h ^ k : Rˣ) : R) = ((F.eps O' R' h ^ k : R'ˣ) : R') := by
    intro h k
    rw [← h1, pushCh, MonoidHom.comp_apply, ← map_zpow (Units.map (g : R →* R'))]
    rfl
  refine ⟨h1, ?_, ?_⟩
  · intro n y
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [hz, map_zero, hz']
    | add a b ha hb => rw [hadd, map_add (f := _), ha, hb, map_add (f := _), hadd']
    | single h r =>
      rw [hs, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, hs', map_mul, he]
  · intro n v ψ γ
    simp only [GFrame.oEl, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Function.comp_def, map_sub, MonoidAlgebra.mapRingHom_single, pushCh]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.DiscStMap
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem tr_map {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : GDet n R G)
    (f : R →+* R') (x : G) :
    (D.map f).tr (MonoidAlgebra.single x 1) = f (D.tr (MonoidAlgebra.single x 1)) := by
  have h := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single x 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one] at h
  exact h

private theorem tr_comap {n : ℕ} {R G G' : Type} [CommRing R] [Group G] [Group G'] (D : GDet n R G)
    (p : G' →* G) (x : G') :
    (D.comap p).tr (MonoidAlgebra.single x 1) = D.tr (MonoidAlgebra.single (p x) 1) := by
  unfold GDet.tr GDet.lam GDet.comap GDet.chi
  simp only [MonoidAlgebra.mapRingHom_single, map_one, MonoidHom.coe_comp, Function.comp_apply]
  have hY : ((MonoidAlgebra.mapDomainRingHom (Polynomial R) p :
        MonoidAlgebra (Polynomial R) G' →+* MonoidAlgebra (Polynomial R) G) :
        MonoidAlgebra (Polynomial R) G' →* MonoidAlgebra (Polynomial R) G)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) =
      MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single (p x) 1 := by
    change (MonoidAlgebra.mapDomainRingHom (Polynomial R) p)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) = _
    rw [map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]
  exact congrArg (fun y => (-1) ^ 1 * ((D.D (Polynomial R)) y).coeff (n - 1)) hY

theorem UpperTheory.V.Pa.BC.discSt_map :
    ∀ (n : ℕ) (R R' G : Type) [CommRing R] [CommRing R'] [Group G] (D : GDet n R G), (∀ (g : R →+* R') (Q : Ideal R'), DiscSt (D.map g) Q ↔ DiscSt D (Q.comap g)) ∧ (∀ (G' : Type) [Group G'] (p : G' →* G), Function.Surjective p → ∀ Q : Ideal R, DiscSt (D.comap p) Q ↔ DiscSt D Q) ∧ ∀ Q Q' : Ideal R, Q ≤ Q' → DiscSt D Q' → DiscSt D Q := by
  intro n R R' G _ _ _ D
  refine ⟨fun g Q => ?_, fun G' _ p hp Q => ?_, fun Q Q' hQ hD => ?_⟩
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G,
        (Matrix.of fun i j => (D.map g).tr (MonoidAlgebra.single (a i * b j) 1)).det =
        g ((Matrix.of fun i j => D.tr (MonoidAlgebra.single (a i * b j) 1)).det) := by
      intro a b
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [RingHom.mapMatrix_apply, tr_map]
    simp only [key, Ideal.mem_comap]
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G',
        (Matrix.of fun i j => (D.comap p).tr (MonoidAlgebra.single (a i * b j) 1)) =
        Matrix.of fun i j => D.tr (MonoidAlgebra.single (p (a i) * p (b j)) 1) := by
      intro a b
      ext i j
      simp [tr_comap]
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨fun i => p (a i), fun j => p (b j), by simpa only [key] using h⟩
    · rintro ⟨a, b, h⟩
      refine ⟨fun i => Function.surjInv hp (a i), fun j => Function.surjInv hp (b j), ?_⟩
      simp only [key, Function.surjInv_eq hp]
      exact h
  · obtain ⟨a, b, h⟩ := hD
    exact ⟨a, b, fun hq => h (hQ hq)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSMono
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.nonSS_mono :
    ∀ (R R' S G G' : Type) [CommRing R] [CommRing R'] [CommRing S] [Group G] [Group G'] (p : G' →* G) (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R' G')) (φ : R →+* S) (φ' : R' →+* S) (Q : Ideal S), Function.Surjective p → (∀ z ∈ I', MonoidAlgebra.mapDomainRingHom S p (MonoidAlgebra.mapRingHom G' φ' z) ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I)) → NonSS I φ Q → NonSS I' φ' Q := by
  intro R R' S G G' _ _ _ _ _ p I I' φ φ' Q hp hI ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (f.comp φ) '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' (f.comp φ') '' I') with hJ'
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    J.ringCon.mk'.comp (MonoidAlgebra.mapDomainRingHom κ p)
  have hψs : Function.Surjective ψ := by
    have h1 : Function.Surjective (MonoidAlgebra.mapDomainRingHom κ p) := by
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
    exact (RingCon.mk'_surjective _).comp h1
  have hcomm : ∀ w : MonoidAlgebra S G',
      MonoidAlgebra.mapDomainRingHom κ p (MonoidAlgebra.mapRingHom G' f w) =
        MonoidAlgebra.mapRingHom G f (MonoidAlgebra.mapDomainRingHom S p w) := by
    intro w
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hcomp : ∀ (T H : Type) [CommRing T] [Group H] (θ : T →+* S) (z : MonoidAlgebra T H),
      MonoidAlgebra.mapRingHom H (f.comp θ) z =
        MonoidAlgebra.mapRingHom H f (MonoidAlgebra.mapRingHom H θ z) := by
    intro T H _ _ θ z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I) ≤
      J.comap (MonoidAlgebra.mapRingHom G f) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, ← hcomp]
    exact TwoSidedIdeal.subset_span ⟨y, hy, rfl⟩
  have hle' : J' ≤ J.comap (MonoidAlgebra.mapDomainRingHom κ p) := by
    rw [hJ', TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hcomp, hcomm, ← TwoSidedIdeal.mem_comap]
    exact hle (hI z hz)
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    have h1 : a - b ∈ J' := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    have h2 := hle' h1
    rw [TwoSidedIdeal.mem_comap, map_sub] at h2
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h2)
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := hψs y
  exact ⟨(x : J'.ringCon.Quotient), rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ResidBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem star_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [CommRing O']
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] (B : Type) [CommRing B] [Algebra O B] [Algebra O' B]
    (h : ∀ a : ℤ_[l], algebraMap O B (algebraMap ℤ_[l] O a) = algebraMap O' B (algebraMap ℤ_[l] O' a))
    (n : ℕ) (y : MonoidAlgebra B F.G₀) : F.star O B n y = F.star O' B n y := by
  have he : F.eps O B = F.eps O' B := by
    ext g
    simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.coe_comp, Function.comp_apply]
    exact h _
  have hop : F.starOp O B n = F.starOp O' B n := by
    ext g
    simp [GFrame.starOp, he]
  unfold GFrame.star
  rw [hop]

private theorem diag_map {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (χ : Fin n → H →* Aˣ) :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep fun i => pushCh f (χ i)) := by
  rw [(UpperTheory.V.CA.d_gmap (GDet.ofRep (diagRep χ))).2.2.2 f (diagRep χ)]
  congr 1
  ext g a b
  by_cases hab : a = b
  · subst hab
    simp [diagRep]
  · simp [diagRep, hab]

private theorem push_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker :=
  MonoidHom.ker_comp_of_injective _ _ (Units.map_injective hf)

theorem UpperTheory.V.Pa.BC.resid_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n), (∃ r' : Resid F O' n, RBC r r') ∧ ∀ r' : Resid F O' n, RBC r r' → (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧ ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r
  let φ : ResidueField O →+* ResidueField O' := ResidueField.map (algebraMap O O')
  have hφ : Function.Injective φ := φ.injective
  have hker : ∀ {H : Type} [Group H] (χ : H →* (ResidueField O)ˣ), (pushCh φ χ).ker = χ.ker :=
    fun χ => push_ker φ hφ χ
  have hpolar : F.IsPolar O' (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))) := by
    intro B _ _ _ _ y
    letI : Algebra (ResidueField O) B := ((algebraMap (ResidueField O') B).comp φ).toAlgebra
    letI : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
    haveI : IsScalarTower O (ResidueField O) B := IsScalarTower.of_algebraMap_eq (fun a => by
      show algebraMap O' B (algebraMap O O' a) = algebraMap (ResidueField O') B (φ (algebraMap O (ResidueField O) a))
      rw [ResidueField.algebraMap_eq, ResidueField.map_residue, ← ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply O' (ResidueField O') B])
    have hp := r.polar B y
    have hs := star_eq F O' O B (fun a => by
      show algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (algebraMap O O' (algebraMap ℤ_[l] O a))
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] O O']) n y
    rw [hs]
    have hd : ∀ x, (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))).D B x =
        (GDet.ofRep (diagRep r.chib)).D B x := by
      intro x
      rw [← diag_map φ r.chib]
      rfl
    rw [hd, hd]
    exact hp
  have hmain : ∀ r' : Resid F O' n, RBC r r' →
      (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧
        ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
    intro r' ⟨hc, _, _⟩
    refine ⟨fun u => ?_, ?_, fun i g => ?_⟩
    · rw [Resid.Ip, Resid.Ip]
      congr 2
      funext i
      rw [hc i]
      exact hker _
    · have hfun : r'.chib = fun i => pushCh φ (r.chib i) := funext hc
      simp only [Resid.Dbar]
      rw [hfun, diag_map]
    · rw [hc i]
      show Units.map (φ : ResidueField O →* ResidueField O') (r.chib i g) = 1 ↔ _
      rw [← map_one (Units.map (φ : ResidueField O →* ResidueField O')),
        (Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ).eq_iff]
  refine ⟨⟨⟨fun i => pushCh φ (r.chib i), fun i => ?_, fun i j hij => ?_, hpolar,
    fun v i => pushCh φ (r.psib v i), fun v i => ?_, fun v i => pushCh (algebraMap O O') (r.th v i),
    fun v i g hg => ?_⟩, fun i => rfl, fun v i => rfl, fun v i => rfl⟩, hmain⟩
  · rw [hker]; exact r.chib_open i
  · apply r.chib_inj
    exact MonoidHom.ext fun g =>
      Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ (DFunLike.congr_fun hij g)
  · rw [hker]; exact r.psib_open v i
  · show Units.map (algebraMap O O' : O →* O') (r.th v i g) = 1
    rw [r.th_comm v i g hg, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SpFin
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem spf_nilp {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) (x : Q)
    (hx : ∀ y, IsUnit (x * y + 1)) (f : Polynomial k) (hf : f ≠ 0) (h : f.eval₂ φ x = 0) :
    IsNilpotent x := by
  obtain ⟨g, hg, hd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf 0
  rw [map_zero, sub_zero] at hg hd
  rw [Polynomial.X_dvd_iff] at hd
  have hu : IsUnit (g.eval₂ φ x) := by
    have e : g.eval₂ φ x = φ (g.coeff 0) * (x * (φ (g.coeff 0)⁻¹ * g.divX.eval₂ φ x) + 1) := by
      have e1 : φ (g.coeff 0) * φ (g.coeff 0)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hd, map_one]
      conv_lhs => rw [← Polynomial.X_mul_divX_add g]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
      linear_combination (-(x * g.divX.eval₂ φ x)) * e1
    rw [e]
    exact ((Ne.isUnit hd).map φ).mul (hx _)
  rw [hg, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
  exact ⟨_, hu.mul_left_eq_zero.1 h⟩

private theorem spf_nilp2 {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) {n : ℕ} (x : Fin n → Q)
    (c : Fin n → k) (f : Polynomial k)
    (h : ∏ i, (Polynomial.X - Polynomial.C (φ (c i) + x i)) = f.map φ) (i : Fin n)
    (hx : ∀ y, IsUnit (x i * y + 1)) : IsNilpotent (x i) := by
  classical
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · exact ⟨1, Subsingleton.elim _ _⟩
  have hmon : (∏ j, (Polynomial.X - Polynomial.C (φ (c j) + x j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at h
    exact hmon.ne_zero h
  have hroot : f.eval₂ φ (φ (c i) + x i) = 0 := by
    rw [← Polynomial.eval_map, ← h, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine spf_nilp φ (x i) hx (f.comp (Polynomial.X + Polynomial.C (c i))) ?_ ?_
  · intro h0
    apply hf
    rwa [← Polynomial.taylor_apply, Polynomial.taylor_eq_zero] at h0
  · rw [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, add_comm]
    exact hroot

theorem UpperTheory.V.Pa.BC.sp_fin :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), Module.Finite B (Sp P ut) ∧ IsNoetherianRing (Sp P ut) := by
  intro B _ _ _ _ q n P ut
  classical
  let k := ResidueField B
  let J := spIdeal P ut
  let Jb : Ideal (MvPowerSeries (Fin q × Fin n) k) := Ideal.map (MvPowerSeries.map (residue B)) J
  let π := Ideal.Quotient.mk Jb
  let φ : k →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) := π.comp MvPowerSeries.C
  let ψ : MvPowerSeries (Fin q × Fin n) B →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) :=
    π.comp (MvPowerSeries.map (residue B))
  have hunit : ∀ (p : Fin q × Fin n) (y : MvPowerSeries (Fin q × Fin n) k ⧸ Jb),
      IsUnit (π (MvPowerSeries.X p) * y + 1) := by
    intro p y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one π, ← map_add (f := _)]
    apply IsUnit.map
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hnil : ∀ p : Fin q × Fin n, IsNilpotent (π (MvPowerSeries.X p)) := by
    rintro ⟨j, i⟩
    refine spf_nilp2 φ (fun i => π (MvPowerSeries.X (j, i))) (fun i => residue B (ut j i))
      ((P j).map (residue B)) ?_ i (hunit _)
    have hD : (∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))) -
        (P j).map MvPowerSeries.C).map ψ = 0 := by
      ext k'
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      show π _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, k', rfl⟩)
    rw [Polynomial.map_sub, sub_eq_zero, Polynomial.map_prod, Polynomial.map_map] at hD
    have hC : ψ.comp MvPowerSeries.C = φ.comp (residue B) := by
      ext b
      simp [ψ, φ, MvPowerSeries.map_C]
    rw [hC, ← Polynomial.map_map] at hD
    rw [← hD]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [ψ, φ, MvPowerSeries.map_C, MvPowerSeries.map_X]
  have hle : Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k))) ≤ nilradical _ := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact mem_nilradical.2 (hnil p)
  have hfg : (Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)))).FG := by
    rw [Ideal.map_span]
    exact Submodule.fg_span ((Set.finite_range _).image _)
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  have hpow : Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N ≤ Jb := by
    have h0 : Ideal.map π (Ideal.span (Set.range
        (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N) = ⊥ := by
      rw [Ideal.map_pow, hN, Ideal.zero_eq_bot]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h0
    exact h0
  have hfin : Module.Finite B (MvPowerSeries (Fin q × Fin n) B ⧸ J) :=
    GlobalTheory.FormalIsogeny.finite_quotient_of_residue J (GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le hpow)
  have hfin' : Module.Finite B (Sp P ut) := hfin
  refine ⟨hfin', ?_⟩
  have hB : IsNoetherian B (Sp P ut) := inferInstance
  exact isNoetherian_of_tower B hB
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilCo
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BaseChangeResidueSurjective
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem base_change_residue_surjective (O' R T : Type) [CommRing O'] [IsLocalRing O'] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing T] [Algebra O' T] [Algebra R T]
    [Module.Finite R T] (φ : T →+* ResidueField O') (hφ : ∀ a, φ (algebraMap O' T a) = residue O' a)
    (hm : ∀ r ∈ maximalIdeal R, φ (algebraMap R T r) = 0)
    (hs : ∀ x : T, ∃ a : O', x - algebraMap O' T a ∈ (maximalIdeal R).map (algebraMap R T)) :
    IsCO O' T := by
  have hJ : (maximalIdeal R).map (algebraMap R T) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.jacobson, Submodule.mem_sInf]
    rintro P ⟨-, hP⟩
    have h1 : Ideal.comap (algebraMap R T) P = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) P)
    rw [← Ideal.mem_comap, h1]
    exact hr
  haveI : Nontrivial T := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg φ h
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have key : ∀ (u y : T), IsUnit u → y ∈ Ideal.jacobson (⊥ : Ideal T) → IsUnit (u + y) := by
    intro u y hu hy
    obtain ⟨v, rfl⟩ := hu
    have h3 := (Ideal.mem_jacobson_bot.mp hy) ↑v⁻¹
    have e : (v : T) + y = v * (y * ↑v⁻¹ + 1) := by
      rw [mul_add, mul_one, mul_comm y, ← mul_assoc, Units.mul_inv, one_mul, add_comm]
    rw [e]
    exact v.isUnit.mul h3
  haveI : IsLocalRing T := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
    obtain ⟨a, ha⟩ := hs x
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
    · left
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ ha)
      rwa [add_sub_cancel] at h4
    · right
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ (neg_mem ha))
      convert h4 using 1
      rw [map_sub, map_one]
      ring
  have hR : IsCL R R := by
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [Algebra.algebraMap_self]
      infer_instance
    · infer_instance
  have hT : IsCL R T := cl_fin R R T hR
  haveI : IsNoetherianRing T := hT.noeth
  refine ⟨hT.complete, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    have h5 := ha.map φ
    rw [hφ] at h5
    exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mp h5.ne_zero
  · intro x
    obtain ⟨a, ha⟩ := hs x
    refine ⟨a, ?_⟩
    have h6 : (maximalIdeal R).map (algebraMap R T) ≤ maximalIdeal T := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h7 := hu.map φ
      rw [hm r hr] at h7
      exact not_isUnit_zero h7
    exact h6 ha

theorem UpperTheory.V.CA.cl_bc :
    ∀ (O O' R : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [Module.Finite O O'] [IsLocalHom (algebraMap O O')] [CommRing R] [Algebra O R] [IsCO O R], IsCO O' (TensorProduct O O' R) := by
  intro O O' R _ _ _ _ _ _ _ _ _ _
  letI : Algebra R (TensorProduct O O' R) := Algebra.TensorProduct.rightAlgebra
  have hR : ∀ r : R, algebraMap R (TensorProduct O O' R) r = 1 ⊗ₜ r := fun r => rfl
  have hL : ∀ x : O', algebraMap O' (TensorProduct O O' R) x = x ⊗ₜ 1 := fun x => rfl
  haveI : Module.Finite R (TensorProduct O O' R) := by
    let c := Algebra.TensorProduct.comm O R O'
    let e : TensorProduct O R O' →ₗ[R] TensorProduct O O' R :=
      { toFun := c
        map_add' := map_add c
        map_smul' := fun r y => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1 }
    exact Module.Finite.of_surjective e c.surjective
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  let f : O' →ₐ[O] ResidueField O' := IsScalarTower.toAlgHom O O' (ResidueField O')
  let g : R →ₐ[O] ResidueField O' :=
    (IsScalarTower.toAlgHom O (ResidueField O) (ResidueField O')).comp (res O R)
  let φ : TensorProduct O O' R →+* ResidueField O' := (Algebra.TensorProduct.productMap f g).toRingHom
  refine base_change_residue_surjective O' R (TensorProduct O O' R) φ ?_ ?_ ?_
  · intro a
    simp [φ, f, g]
  · intro r hr
    have h1 : res O R r = 0 := (res_eq_zero_iff O R r).mpr hr
    show Algebra.TensorProduct.productMap f g (algebraMap R (TensorProduct O O' R) r) = 0
    rw [hR, Algebra.TensorProduct.productMap_apply_tmul]
    simp [g, h1]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul o r =>
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) r
      refine ⟨algebraMap O O' c * o, ?_⟩
      have e2 : o ⊗ₜ[O] r - algebraMap O' (TensorProduct O O' R) (algebraMap O O' c * o) =
          algebraMap O' (TensorProduct O O' R) o * algebraMap R (TensorProduct O O' R) (r - algebraMap O R c) := by
        rw [hR, hL, hL, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub,
          ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      rw [e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc)
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      have e3 : x + y - algebraMap O' (TensorProduct O O' R) (a + b) =
          (x - algebraMap O' (TensorProduct O O' R) a) + (y - algebraMap O' (TensorProduct O O' R) b) := by
        rw [map_add (f := _)]
        ring
      rw [e3]
      exact add_mem ha hb
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_co :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsCO O R], ∃ _ : IsCO O' (Til O O' R), IsLocalHom (Til.ι O O' R) ∧ Til.s O O' R ∈ maximalIdeal (Til O O' R) := by
  intro O O' _ _ _ _ _ _ _ R _ _ _
  haveI hT := UpperTheory.V.CA.cl_bc O O' R
  let f : R →+* O' ⊗[O] R := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom
  have hint : f.IsIntegral := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact f.isIntegralElem_zero
    | tmul o r =>
      have ho : IsIntegral O ((Algebra.TensorProduct.includeLeft : O' →ₐ[O] O' ⊗[O] R) o) :=
        (Algebra.IsIntegral.isIntegral (R := O) o).map _
      rw [Algebra.TensorProduct.includeLeft_apply] at ho
      obtain ⟨p, hp, hpe⟩ := ho
      have h1 : f.IsIntegralElem (o ⊗ₜ[O] (1 : R)) := by
        refine ⟨p.map (algebraMap O R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hc : f.comp (algebraMap O R) = algebraMap O (O' ⊗[O] R) :=
          (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).comp_algebraMap
        rw [hc]
        exact hpe
      have he : o ⊗ₜ[O] r = (o ⊗ₜ[O] (1 : R)) * f r := by
        show _ = _ * ((1 : O') ⊗ₜ[O] r)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [he]
      exact RingHom.IsIntegralElem.mul f h1 f.isIntegralElem_map
    | add x y hx hy => exact RingHom.IsIntegralElem.add f hx hy
  have hloc : IsLocalHom f := by
    refine ((IsLocalRing.local_hom_tfae f).out 1 5).mpr ?_
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hint (maximalIdeal (O' ⊗[O] R))
    exact IsLocalRing.eq_maximalIdeal this
  haveI hco : IsCO O' (Til O O' R) := UpperTheory.V.Alg.co_mvps O' (O' ⊗[O] R) Unit
  refine ⟨hco, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have hr' : IsUnit (PowerSeries.C ((1 : O') ⊗ₜ[O] r) : PowerSeries (O' ⊗[O] R)) := hr
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at hr'
    exact hloc.map_nonunit r hr'
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    show ¬ IsUnit (PowerSeries.X : PowerSeries (O' ⊗[O] R))
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.GenBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.gen_bc :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (S : Set B) (S' : Set (Til O O' B)), IsLocalHom (Til.ι O O' B) → Til.s O O' B ∈ maximalIdeal (Til O O' B) → (∀ a ∈ S, Til.ι O O' B a ∈ S') → Til.s O O' B ∈ S' → GenBy O S → GenBy O' S' := by
  intro O O' _ _ _ _ _ _ _ B _ _ _ _ S S' hloc hs hS hsS hgen N
  let P : Til O O' B → Prop := fun x => ∃ a ∈ Algebra.adjoin O' S', x - a ∈ maximalIdeal (Til O O' B) ^ N
  have Pmem : ∀ x ∈ Algebra.adjoin O' S', P x := fun x hx => ⟨x, hx, by simp⟩
  have Padd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have : x + y - (a + b) = (x - a) + (y - b) := by ring
    rw [this]
    exact add_mem hx hy
  have Pmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    have : x * y - a * b = x * (y - b) + (x - a) * b := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hx)
  have hadj : ∀ a ∈ Algebra.adjoin O S, Til.ι O O' B a ∈ Algebra.adjoin O' S' := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hS x hx)
    | algebraMap r => rw [Til.ι_algebraMap]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hmap : Ideal.map (Til.ι O O' B) (maximalIdeal B ^ N) ≤ maximalIdeal (Til O O' B) ^ N := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (Til.ι O O' B) x hx
  have Pι : ∀ b, P (Til.ι O O' B b) := by
    intro b
    obtain ⟨a, ha, hb⟩ := hgen N b
    refine ⟨_, hadj a ha, ?_⟩
    rw [← map_sub]
    exact hmap (Ideal.mem_map_of_mem _ hb)
  have PC : ∀ t, P (Til.C O O' B t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add (f := _)]; exact Padd _ _ hx hy
    | tmul o b =>
      have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
        PowerSeries.algebraMap_apply
      have e : Til.C O O' B (o ⊗ₜ[O] b) = algebraMap O' (Til O O' B) o * Til.ι O O' B b := by
        rw [h]
        show _ = Til.C O O' B _ * Til.C O O' B ((1 : O') ⊗ₜ[O] b)
        rw [← map_mul]
        congr 1
        simp
      rw [e]
      exact Pmul _ _ (Pmem _ (Subalgebra.algebraMap_mem _ _)) (Pι b)
  have hsA : Til.s O O' B ∈ Algebra.adjoin O' S' := Algebra.subset_adjoin hsS
  have hdec : ∀ f : Til O O' B, ∃ (g : Til O O' B) (c : O' ⊗[O] B), f = Til.s O O' B * g + Til.C O O' B c :=
    fun f => ⟨_, _, PowerSeries.eq_X_mul_shift_add_const (R := O' ⊗[O] B) f⟩
  have key : ∀ (k : ℕ) (f : Til O O' B), ∃ g h, P g ∧ f = g + Til.s O O' B ^ k * h := by
    intro k f
    induction k with
    | zero => exact ⟨0, f, Pmem _ (zero_mem _), by simp⟩
    | succ k ih =>
      obtain ⟨g, h, hg, e⟩ := ih
      obtain ⟨h', c, e'⟩ := hdec h
      refine ⟨g + Til.s O O' B ^ k * Til.C O O' B c, h',
        Padd _ _ hg (Pmul _ _ (Pmem _ (pow_mem hsA k)) (PC c)), ?_⟩
      rw [e, e']
      ring
  intro f
  obtain ⟨g, h, hg, e⟩ := key N f
  rw [e]
  refine Padd _ _ hg ⟨0, zero_mem _, ?_⟩
  rw [sub_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs N)
end
