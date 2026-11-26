module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivial
open Matrix

namespace GlobalTheory.ZarhinFam

theorem zpow_finset_sum' {G ι : Type} [CommGroup G] (a : G) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ k ∈ s, e k) = ∏ k ∈ s, a ^ e k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, _root_.zpow_add, ih]

theorem prod_prod_zpow_mul {G : Type} [CommGroup G] (P Q : Matrix (Fin 4) (Fin 4) ℤ) (w : Fin 4 → G)
    (a : Fin 4) : ∏ k, (∏ i, w i ^ Q k i) ^ P a k = ∏ i, w i ^ (P * Q) a i := by
  simp_rw [← Finset.prod_zpow, ← _root_.zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, zpow_finset_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem prod_zpow_smul_one {G : Type} [CommGroup G] (c : ℤ) (w : Fin 4 → G) (a : Fin 4) :
    ∏ i, w i ^ (c • (1 : Matrix (Fin 4) (Fin 4) ℤ)) a i = w a ^ c := by
  simp [Matrix.smul_apply, Matrix.one_apply]

theorem zarhin_kernel_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  intro d GA GB _ _ f g hd hgf u v hA hB hC
  have hxx : quat d * (quat d)ᵀ = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_mul_transpose d
  have hxtx : (quat d)ᵀ * quat d = (((d - 1 : ℕ) : ℤ)) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
    quat_transpose_mul d
  have hd1 : d = (d - 1) + 1 := by omega
  have hv : ∀ k, v k = 1 := by
    intro k
    have E : ∏ i, (f (u i) * ∏ j, v j ^ quat d j i) ^ quat d k i = 1 := by
      simp [hA]
    rw [Finset.prod_congr rfl fun i _ => mul_zpow (f (u i)) (∏ j, v j ^ quat d j i) (quat d k i),
      Finset.prod_mul_distrib] at E
    have E2 : ∏ i, (∏ j, v j ^ (quat d)ᵀ i j) ^ quat d k i = v k ^ (((d - 1 : ℕ) : ℤ)) := by
      rw [prod_prod_zpow_mul, hxx, prod_zpow_smul_one]
    simp only [Matrix.transpose_apply] at E2
    have hF : f (∏ i, u i ^ quat d k i) = ∏ i, f (u i) ^ quat d k i := by
      simp [map_prod, map_zpow]
    rw [E2, ← hF, zpow_natCast] at E
    have hBk := hB k
    rw [show v k ^ d = v k ^ (d - 1) * v k by rw [← pow_succ, ← hd1], ← mul_assoc, E, one_mul] at hBk
    exact hBk
  refine ⟨?_, hv⟩
  have hxu := hC hv
  intro l
  have E : ∏ k, (∏ i, u i ^ quat d k i) ^ (quat d)ᵀ l k = 1 := by
    simp [hxu]
  rw [prod_prod_zpow_mul, hxtx, prod_zpow_smul_one, zpow_natCast] at E
  have hfu : f (u l) = 1 := by
    have h := hA l
    simpa [hv] using h
  have hdu : u l ^ d = 1 := by
    rw [← hgf, hfu, map_one]
  rw [show u l ^ d = u l ^ (d - 1) * u l by rw [← pow_succ, ← hd1], E, one_mul] at hdu
  exact hdu

end GlobalTheory.ZarhinFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivialStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (exact GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (intros; apply GlobalTheory.ZarhinFam.zarhin_kernel_trivial  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinKerA

variable {S : Scheme.{0}}

theorem mkZ_pa' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) : mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) : mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem pull_zCls {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (w w' : Y ⟶ Zob A B) :
    CechPic.pull (lift w w').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (w ≫ pa A B i) (w' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w ≫ pa A B i) (w' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w' ≫ pa A B i) (w ≫ pb A B j)) +
      ∑ j, evc hQ (w' ≫ pb A B j ≫ mu) (w ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx i
  have hP := c.isLB
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hQd : IsDual c.A B Q := hZ.2.1
  have hQd' : IsDual B c.A (swap Q) := hZ.2.2.1
  have hs : (swap Q).IsLB := hQd'.isLB
  haveI : IsMonHom mu := hZ.2.2.2.2.1

  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _
      (pull_isLB (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _)]
    exact (cls_eq_zero_iff _).2 hx

  let inc : c.A ⟶ Zob c.A B := mkZ c.A B (fun k => if k = i then 𝟙 c.A else 1) (fun _ => 1)
  have h1 := congrArg (CechPic.pull (lift (fst c.A T ≫ inc) (snd c.A T)).left) h0
  rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst, pull_zCls] at h1
  have hpa : ∀ k, (fst c.A T ≫ inc) ≫ pa c.A B k = if k = i then fst c.A T else 1 := by
    intro k
    rw [Category.assoc, mkZ_pa']
    split_ifs <;> simp [MonObj.comp_one]
  have hpb : ∀ j, (fst c.A T ≫ inc) ≫ pb c.A B j = 1 := by
    intro j
    rw [Category.assoc, mkZ_pb', MonObj.comp_one]
  have z1 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hP a (1 : Y ⟶ c.A) = 0 := fun a => evc_one_right hP c.rig₂ a
  have z2 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hQ a (1 : Y ⟶ B) = 0 := fun a => evc_one_right hQ hQd.zero a
  have z3 : ∀ {Y : Over S} (b : Y ⟶ B), evc hQ (1 : Y ⟶ c.A) b = 0 := fun b => hQd.additive.evc_one hQ b
  have s1 : (∑ k, evc hP ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pa c.A B k)) =
      evc hP ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [hpa, if_neg hk, z1]) (fun hi => absurd (Finset.mem_univ i) hi),
      hpa, if_pos rfl]
  have s2 : (∑ k, ∑ j, quat d j k • evc hQ ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pb c.A B j)) = 0 := by
    simp only [hpb, z2, smul_zero, Finset.sum_const_zero]
  have s3 : (∑ k, ∑ j, quat d j k • evc hQ ((fst c.A T ≫ inc) ≫ pa c.A B k) ((snd c.A T ≫ x) ≫ pb c.A B j)) =
      ∑ j, quat d j i • evc hQ (fst c.A T) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp only [hpa, if_neg hk, z3, smul_zero, Finset.sum_const_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [hpa, if_pos rfl]
  have s4 : (∑ j, evc hQ ((fst c.A T ≫ inc) ≫ pb c.A B j ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j)) = 0 := by
    simp only [← Category.assoc _ (pb c.A B _) mu, hpb, MonObj.one_comp, z3, Finset.sum_const_zero]
  rw [s1, s2, s3, s4, add_zero, add_zero] at h1

  have eS : cls c.P hP = evc hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
  have eL : cls c.P hP = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff hP (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  have ePQ : ∀ {Y : Over S} (u a : Y ⟶ c.A), evc hP u a = evc hQ a (u ≫ la) := by
    intro Y u a
    have e1 := congrArg (CechPic.pull (lift u a).left) eS
    have e2 := congrArg (CechPic.pull (lift a u).left) eL
    rw [pull_evc, lift_snd, lift_fst] at e1
    rw [pull_evc, lift_fst, lift_snd_assoc] at e2
    exact e1.trans e2

  have hadd : ∀ {Y : Over S} (a : Y ⟶ c.A) (b b' : Y ⟶ B), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro Y a b b'
    rw [← evc_swap hQ hs, ← evc_swap hQ hs, ← evc_swap hQ hs]
    exact (isAdditive_iff hs).1 hQd'.additive Y b b' a
  let φ : (T ⟶ B) →* Multiplicative (Pic (c.A ⊗ T).left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (evc hQ (fst c.A T) (snd c.A T ≫ b))) fun b b' => by
      simp only [MonObj.comp_mul, hadd, ofAdd_add]
  refine (hQd.isPerfect hQd').ker_right T _ ((triv_ev_iff hQ _ _).2 ?_)
  have key : Multiplicative.toAdd (φ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) =
      evc hQ (fst c.A T) (snd c.A T ≫ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) := rfl
  rw [← key, map_mul, map_prod, toAdd_mul, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, φ, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [← Category.assoc, ← Category.assoc, ← ePQ]
  simpa only [Category.assoc] using h1

end GlobalTheory.ZarhinKerA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  first | (exact @GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerA.zarhinBundle_kernel  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

namespace AffZphi

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  unfold mkZ pa
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  unfold mkZ pb
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

theorem zob_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (Out.powIsLimit A 4).hom_ext fun ⟨i⟩ => by simpa [pa] using ha i
  · exact (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by simpa [pb] using hb j

instance pa_isMonHom (i : Fin 4) : IsMonHom (pa A B i) := by unfold pa; infer_instance

instance pb_isMonHom (j : Fin 4) : IsMonHom (pb A B j) := by unfold pb; infer_instance

theorem sig_castAdd (i : Fin 4) : sig (Fin.castAdd 4 i) = .inl i := by fin_cases i <;> rfl

theorem sig_natAdd (j : Fin 4) : sig (Fin.natAdd 4 j) = .inr j := by fin_cases j <;> rfl

end AffZphi

open AffZphi

theorem isAffineHom_zphi : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A)
    (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) →
    IsAffineHom (GlobalTheory.ZarhinFam.zphi c.A B mu).left := by
  intro h M d S t c B _ _ Q la mu hZ _ hu
  have hB : IsAbelianScheme B := hZ.1
  have hA : IsAbelianScheme c.A := c.ab
  have hZab : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
    (AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hB 3)
  have h8 : IsAbelianScheme (Out.powObj c.A 8) := AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 7
  have := hZab.comm
  have := hZab.smooth
  have := hZab.proper
  have := h8.proper
  have hfin : IsFinite ((𝟙 (Zob c.A B)) ^ d).left := GlobalTheory.GrpTangent.isFinite_id_pow _ hu
  have hlm : mu ≫ la = 𝟙 B ^ d := hZ.2.2.2.2.2.2.1
  let ν : Out.powObj c.A 8 ⟶ Zob c.A B :=
    mkZ c.A B (fun i => Out.powPr c.A (Fin.castAdd 4 i) ^ d) (fun j => Out.powPr c.A (Fin.natAdd 4 j) ≫ la)
  have key : zphi c.A B mu ≫ ν = (𝟙 (Zob c.A B)) ^ d := by
    refine zob_ext c.A B _ _ (fun i => ?_) (fun j => ?_)
    · rw [Category.assoc, mkZ_pa, MonObj.comp_pow, zphi_powPr, MonObj.pow_comp, Category.id_comp]
      simp [zpr, sig_castAdd]
    · rw [Category.assoc, mkZ_pb, ← Category.assoc, zphi_powPr, MonObj.pow_comp, Category.id_comp]
      simp only [zpr, sig_natAdd, Sum.elim_inr, Category.assoc, hlm, MonObj.comp_pow, Category.comp_id]
  have hsep : IsSeparated ν.left := by
    have : IsSeparated (ν.left ≫ (Zob c.A B).hom) := by rw [Over.w ν]; infer_instance
    exact IsSeparated.of_comp ν.left (Zob c.A B).hom
  have : IsAffineHom ((zphi c.A B mu).left ≫ ν.left) := by
    rw [← Over.comp_left, key]; infer_instance
  exact IsAffineHom.of_comp _ ν.left

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsAffineHom (GlobalTheory.ZarhinFam.zphi c.A B mu).left := by
  first | (exact @GlobalTheory.ZarhinFam.isAffineHom_zphi) | (exact GlobalTheory.ZarhinFam.isAffineHom_zphi) | (intros; apply GlobalTheory.ZarhinFam.isAffineHom_zphi  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_comp_idPow {S : Scheme.{0}} {B Y : Over S} [GrpObj B] (b : Y ⟶ B) (n : ℕ) :
    b ≫ (𝟙 B) ^ n = b ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem zClsDiag_nsmul_evc {S : Scheme.{0}} {A B Y : Over S} [GrpObj A] [GrpObj B]
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hs : IsDual B A (swap Q)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    n • evc hQ a b = evc hQ a (b ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ← evc_swap hQ hs.isLB, hs.additive.evc_one hs.isLB]
  | succ n ih =>
    rw [succ_nsmul, ih, pow_succ, ← evc_swap hQ hs.isLB (b ^ n * b), (isAdditive_iff hs.isLB).1 hs.additive,
      evc_swap hQ hs.isLB, evc_swap hQ hs.isLB]

theorem zClsDiag_key {h M d : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
    {B : Over S} [GrpObj B] [IsCommMonObj B] {Q : LB (c.A ⊗ B).left} {la : c.A ⟶ B} {mu : B ⟶ c.A}
    (hZ : ZData c d B Q la mu) {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B) :
    d • pull (lift a b).left (cls Q hZ.2.1.isLB) = pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := by
  have hQ := hZ.2.1.isLB
  have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  show d • evc hQ a b = _
  rw [e, pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hZ.2.2.2.2.2.2.1, zClsDiag_comp_idPow,
    zClsDiag_nsmul_evc hQ hZ.2.2.1]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_sum_sig {M : Type*} [AddCommMonoid M] (F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → M) :
    ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) = ∑ s, ∑ t, F s t := by
  let e : Fin 8 ≃ Fin 4 ⊕ Fin 4 := Equiv.ofBijective sig (by decide)
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_congr rfl fun k _ => Equiv.sum_comp e (F (sig k))).trans (Equiv.sum_comp e fun s => ∑ t, F s t)

theorem nsmul_pull_diag_zCls : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  intro h M d S t c B _ _ Q la mu hZ _
  let F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Pic (Zob c.A B).left := fun s u =>
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 s u •
      pull (lift (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) s)
        (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) u)).left (cls c.P c.isLB)
  rw [show (∑ kl : Fin 8 × Fin 8, zW d kl.1 kl.2 • pull (lift (zpr c.A B mu kl.1) (zpr c.A B mu kl.2)).left
      (cls c.P c.isLB)) = ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) from rfl, zClsDiag_sum_sig]
  simp only [F, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc, Category.id_comp]
  have hk : ∀ {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B), d • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun a b => zClsDiag_key c hZ a b
  have hk' : ∀ {Y : Over S} (z : ℤ) (a : Y ⟶ c.A) (b : Y ⟶ B), d • z • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      z • pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun z a b => by rw [smul_comm, hk]
  simp only [smul_add, Finset.smul_sum, hk, hk', Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
    zero_add, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, one_smul, Finset.sum_add_distrib, mul_smul, two_smul, natCast_zsmul]
  abel

end GlobalTheory.ZarhinFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  first | (exact @GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (exact GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls) | (intros; apply GlobalTheory.ZarhinFam.nsmul_pull_diag_zCls  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDef
open Matrix

namespace GlobalTheory.ZarhinFam

theorem zW_symm_blocks (d : ℕ) (i j : Fin 4 ⊕ Fin 4) :
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 i j +
      Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 j i =
    2 * Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1 i j := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.zero_apply, smul_eq_mul]
  all_goals (try simp only [@eq_comm _ b a])
  all_goals (try split_ifs)
  all_goals ring

theorem zarhin_block_posDef {d : ℕ} (hd : 0 < d) :
    (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
      (Int.cast : ℤ → ℝ) |>.PosDef := by
  set x : Matrix (Fin 4) (Fin 4) ℝ := (quat d).map (Int.cast : ℤ → ℝ) with hx
  have hxx : xᵀ * x = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
    ext i j
    have h0 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (quat_transpose_mul d) i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, hx, Matrix.map_apply] at h0 ⊢
    rw [h0]
    split_ifs <;> simp [Nat.cast_sub (show 1 ≤ d by omega)]
  set C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 x 1 with hC
  set C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-x) 1 with hC'
  have hCC : C' * C = 1 := by
    rw [hC, hC', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
  have hinj : Function.Injective C.mulVec := by
    intro v w hvw
    have := congrArg (C'.mulVec) hvw
    simpa [Matrix.mulVec_mulVec, hCC] using this
  have key : Cᴴ * 1 * C =
      (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
        (Int.cast : ℤ → ℝ) := by
    rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]
    congr 1
    · rw [Matrix.transpose_one, Matrix.one_mul, hxx]; ext i j
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    · simp [hx, Matrix.transpose_map]
    · simp [hx]
    · simp
  rw [← key]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

theorem zW_symm_posDef : ∀ (d : ℕ), 0 < d →
    ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  intro d hd
  have hsig : Function.Injective sig := by
    intro a b h; revert a b h; decide
  have h := ((zarhin_block_posDef hd).smul (a := (2 : ℝ)) two_pos).submatrix hsig
  convert h using 1
  ext k l
  have e := zW_symm_blocks d (sig k) (sig l)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [zW, zW, e]
  push_cast
  ring

end GlobalTheory.ZarhinFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDefStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef : ∀ (d : ℕ), 0 < d → ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  first | (exact @GlobalTheory.ZarhinFam.zW_symm_posDef) | (exact GlobalTheory.ZarhinFam.zW_symm_posDef) | (intros; apply GlobalTheory.ZarhinFam.zW_symm_posDef  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivial
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.KerC

theorem ker_zarhinPolarization_of_pullback : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx hv j
  obtain ⟨hB, hD1, hD2, hla, hmu, hlm, hml, hPiso⟩ := id hZ
  haveI : IsMonHom la := hla
  have hQ : Q.IsLB := hD1.isLB
  have hPQ : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc hQ a (a' ≫ la) := by
    have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hPiso
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd_assoc]
  have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ d mu
  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull hz]
    exact (cls_eq_zero_iff (pull_isLB hz _)).2 hx
  have h1 := congrArg (CechPic.pull
    (lift (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then snd T B else 1)) (fst T B) :
      T ⊗ B ⟶ Zob c.A B ⊗ T).left) h0
  rw [← pull_comp, ← Over.comp_left, comp_lift, map_zero, lift_snd_assoc, lift_fst,
    AdjPf.pull_zCls c.isLB hQ d la mu hPQ] at h1
  simp only [AdjPf.zf, Category.assoc, AdjPf.mkZ_pa, AdjPf.mkZ_pb, hv, MonObj.comp_one, MonObj.one_comp,
    evc_one_right hQ hD1.zero, hD1.additive.evc_one hQ, smul_zero, Finset.sum_const_zero, zero_add, add_zero] at h1
  simp only [apply_ite (evc hQ _), evc_one_right hQ hD1.zero, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  refine (hD1.isPerfect hD2).ker_left T _ ((triv_ev_iff hQ _ _).2 ?_)
  let F : (T ⊗ B ⟶ c.A) →* Multiplicative (Pic (T ⊗ B).left) :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hQ a (snd T B))) fun a a' => by
      rw [(isAdditive_iff hQ).1 hD1.additive, ofAdd_add]
  have eF : ∀ a, evc hQ a (snd T B) = Multiplicative.toAdd (F a) := fun _ => rfl
  have ep : fst T B ≫ ∏ i, (x ≫ pa c.A B i) ^ quat d j i = ∏ i, (fst T B ≫ x ≫ pa c.A B i) ^ quat d j i := by
    have := map_prod (AdjPf.pre (G := c.A) (fst T B)) (fun i => (x ≫ pa c.A B i) ^ quat d j i) Finset.univ
    simp only [map_zpow] at this
    exact this
  rw [ep, eF, map_prod, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← eF]
  exact h1

end GlobalTheory.ZarhinFam.KerC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelOfSecondCoordTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback) | (exact GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback) | (intros; apply GlobalTheory.ZarhinFam.KerC.ker_zarhinPolarization_of_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipal
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic

theorem principal_zP : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hunit hK
  refine ⟨?_, fun T x hx => ?_⟩
  · have hAb : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
      (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
    have := hAb.proper
    have hA : Out.RelAmple c.A c.diag := hK.1
    have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ Out.powObj c.A 8,
        ∀ u, x ≫ Out.powPr c.A u = y u := fun T y =>
      ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
        fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
    have h8 := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef GlobalTheory.SemiRigid.globalFns h M 8 _ _ S t c
      (Out.powObj c.A 8) (Out.powPr c.A) (zW d) (fun u => inferInstance) huniv hA (GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef d hd)
    have := GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower h M d S t c B Q la mu hZ hd hunit
    have hF : (LB.LinComb c.P (K := Fin 8 × Fin 8)
        (fun uv => (lift (Out.powPr c.A uv.1) (Out.powPr c.A uv.2)).left) (fun uv => zW d uv.1 uv.2)).IsLB :=
      LB.isLB_linComb c.isLB _ _
    have hp := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom (zphi c.A B mu) hF h8
    have hzP := zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
    refine GlobalTheory.PosDefAmple.relAmple_of_nsmul (pull_isLB hzP _) (pull_isLB hF _) (N := d) hd ?_ hp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cls_pull hzP, cls_zP, cls_pull hF, cls_linComb c.isLB, GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form h M d S t c B Q la mu hZ hd, map_sum]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, zphi_powPr, zphi_powPr]
  · have hla := hZ.2.2.2.1
    have hmu := hZ.2.2.2.2.1
    let f : (T ⟶ c.A) →* (T ⟶ B) := MonoidHom.mk' (fun a => a ≫ la) (fun a b => MonObj.mul_comp a b la)
    let g : (T ⟶ B) →* (T ⟶ c.A) := MonoidHom.mk' (fun a => a ≫ mu) (fun a b => MonObj.mul_comp a b mu)
    have hfg : ∀ a, g (f a) = a ^ d := fun a => by
      change (a ≫ la) ≫ mu = a ^ d
      rw [Category.assoc, hZ.2.2.2.2.2.1, MonObj.comp_pow, Category.comp_id]
    obtain ⟨hu, hv⟩ := GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial d (T ⟶ c.A) (T ⟶ B) f g hd hfg (fun i => x ≫ pa c.A B i) (fun j => x ≫ pb c.A B j)
      (fun i => by simpa [f, Category.assoc] using GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations h M d S t c B Q la mu hZ T x hx i)
      (fun j => GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations h M d S t c B Q la mu hZ T x hx j)
      (GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial h M d S t c B Q la mu hZ T x hx)
    have e1 : x ≫ fst _ _ = 1 := (Out.powIsLimit c.A 4).hom_ext fun ⟨i⟩ => by
      change (x ≫ fst _ _) ≫ Out.powPr c.A i = 1 ≫ Out.powPr c.A i
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hu i)
    have e2 : x ≫ snd _ _ = 1 := (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by
      change (x ≫ snd _ _) ≫ Out.powPr B j = 1 ≫ Out.powPr B j
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hv j)
    ext1
    · rw [e1, MonObj.one_comp]
    · rw [e2, MonObj.one_comp]

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_principal : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.principal_zP) | (exact GlobalTheory.ZarhinFam.principal_zP) | (intros; apply GlobalTheory.ZarhinFam.principal_zP <;> assumption)
end
