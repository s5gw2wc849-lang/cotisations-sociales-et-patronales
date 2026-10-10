/-
Exemples et vérifications : chaque cas reproduit un exemple chiffré
officiel (Urssaf, Agirc-Arrco) ou une identité des barèmes 2026.

Les théorèmes concrets sont prouvés par `native_decide` : l'évaluateur
Lean exécute le code (arithmétique rationnelle exacte, racines entières
de Newton) et vérifie la proposition.
-/
import Cotisations.Bulletin
import Cotisations.Organismes
import Cotisations.Syntech

namespace CotationsExamples

open Cotisations

/-! ### Outils numériques -/

theorem racine_carree_mille : Cotisations.racineNieme 2 1000000 = 1000 := by
  native_decide

theorem racine_quatrieme : Cotisations.racineNieme 4 (10 ^ 28 : Nat) = 10 ^ 7 := by
  native_decide

theorem puissance_carree : Cotisations.dans (Cotisations.puissanceRat 4 1 2) 1.999999 2.000001 := by
  native_decide

/-! ### Barèmes : identités structurelles 2026 -/

/-- CSG totale = 9,20 % (6,80 % déductible + 2,40 % non déductible). -/
theorem csg_totale_92 : ((0.068 : Rat) + 0.024) = (0.092 : Rat) := by native_decide

/-- Vieillesse employeur 2026 : 8,55 % (T1) + 2,11 % (déplafonnée) = 10,66 %,
    cohérent avec la décomposition officielle de la cible RGDU. -/
theorem vieillesse_patronale_2026 : ((0.0855 : Rat) + 0.0211) = (0.1066 : Rat) := by native_decide

/-- Vieillesse salarié 2026 : 6,90 % (T1) + 0,40 % (déplafonnée). -/
theorem vieillesse_salariale_2026 : ((0.069 : Rat) + 0.004) = (0.073 : Rat) := by native_decide

/-- Cible RGDU < 50 salariés : maladie 13 % + vieillesse 10,66 % +
    famille 5,25 % + AT mutualisé 0,49 % + Agirc-Arrco 6,01 % + FNAL 0,10 % +
    CSA 0,30 % + chômage 4,00 % = 39,81 % (décomposition officielle Urssaf). -/
theorem cible_rgdu_petit :
    ((0.13 : Rat) + 0.1066 + 0.0525 + 0.0049 + 0.0601 + 0.001 + 0.003 + 0.04) = (0.3981 : Rat) := by
  native_decide

/-- Cible RGDU ≥ 50 salariés : idem avec FNAL 0,50 % → 40,21 %. -/
theorem cible_rgdu_grand :
    ((0.13 : Rat) + 0.1066 + 0.0525 + 0.0049 + 0.0601 + 0.005 + 0.003 + 0.04) = (0.4021 : Rat) := by
  native_decide

/-- Imputation officielle : part Urssaf + part Agirc-Arrco = cible totale. -/
theorem imputation_rgdu :
    (((0.3420 : Rat) + 0.0601) = (0.4021 : Rat) ∧ ((0.3380 : Rat) + 0.0601) = (0.3981 : Rat)) := by
  native_decide

/-- Répartition réglementaire Agirc-Arrco : 40 % salarié / 60 % employeur. -/
theorem repartition_agirc_arrco :
    (((0.0315 : Rat) / (0.0315 + 0.0472)) ≥ (0.39 : Rat)
      ∧ ((0.0315 : Rat) / (0.0315 + 0.0472)) ≤ (0.41 : Rat)) := by
  native_decide

/-! ### Tranches de plafond -/

def tranche5000 : Cotisations.Tranches := Cotisations.decoupeTranches 5000 4005

theorem tranche1_exemple : tranche5000.tranche1 = 4005 := by native_decide
theorem tranche2_exemple : tranche5000.tranche2 = 995 := by native_decide
theorem tranche3_exemple : tranche5000.tranche3 = 0 := by native_decide

/-- Sous le plafond : toute l'assiette est en tranche 1. -/
theorem tranche_sous_plafond :
    (Cotisations.decoupeTranches 3000 4005).tranche1 = 3000
    ∧ (Cotisations.decoupeTranches 3000 4005).tranche2 = 0
    ∧ (Cotisations.decoupeTranches 3000 4005).tranche3 = 0 := by
  native_decide

/-- Au-delà de 8 plafonds : le surplus passe en tranche 3
    (50 000 − 8 × 4 005 = 17 960). -/
theorem tranche_sur_8_plafonds :
    (Cotisations.decoupeTranches 50000 4005).tranche1 = 4005
    ∧ (Cotisations.decoupeTranches 50000 4005).tranche2 = 28035
    ∧ (Cotisations.decoupeTranches 50000 4005).tranche3 = 17960 := by
  native_decide

/-- Somme des tranches = assiette (cas concret). -/
theorem somme_tranches_exemple :
    tranche5000.tranche1 + tranche5000.tranche2 + tranche5000.tranche3 = 5000 := by
  native_decide

/-! ### Agirc-Arrco 2026 (exemples chiffrés) -/

def ppAA : Cotisations.ParametresAgircArrco := Cotisations.parametresAgircArrco2026

/-- T2 sur 995 € : 8,64 % salarié = 85,968 €. -/
theorem agirc_t2_salarial :
    (Cotisations.cotisationAgircArrcoT2 ppAA tranche5000).partSalariale = 85.968 := by
  native_decide

/-- T2 sur 995 € : 12,95 % employeur = 128,8525 €. -/
theorem agirc_t2_patronal :
    (Cotisations.cotisationAgircArrcoT2 ppAA tranche5000).partPatronale = 128.8525 := by
  native_decide

/-- CEG T2 : 1,08 % salarié = 10,746 €. -/
theorem ceg_t2_salarial :
    (Cotisations.cegT2 ppAA tranche5000).partSalariale = 10.746 := by native_decide

/-- CET due (rémunération > PASS) : 0,14 % × 5 000 = 7 €. -/
theorem cet_salarial :
    (Cotisations.cotisationCET ppAA tranche5000).partSalariale = 7 := by native_decide

/-- APEC cadre : 0,024 % × 5 000 = 1,20 €. -/
theorem apec_salarial :
    (Cotisations.cotisationApec ppAA tranche5000 4005).partSalariale = 1.2 := by native_decide

/-! ### CSG / CRDS -/

def ps3000 : Cotisations.ParametresSalarie := { brutMensuel := 3000 }

/-- CSG déductible : 6,80 % × 98,25 % × 3 000 = 200,43 €. -/
theorem csg_deductible_3000 :
    (Cotisations.csgDeductible Cotisations.parametres2026 ps3000).partSalariale = 200.43 := by
  native_decide

/-- CSG non déductible : 2,40 % × 98,25 % × 3 000 = 70,74 €. -/
theorem csg_non_deductible_3000 :
    (Cotisations.csgNonDeductible Cotisations.parametres2026 ps3000).partSalariale = 70.74 := by
  native_decide

/-- CRDS : 0,50 % × 98,25 % × 3 000 = 14,7375 €. -/
theorem crds_3000 :
    (Cotisations.crds Cotisations.parametres2026 ps3000).partSalariale = 14.7375 := by
  native_decide

/-- Assiette CSG avec heures supplémentaires : 98,25 % × 2 500 +
    (98,25 % − 11,31 %) × 300 = 2 717,07 €. -/
theorem assiette_csg_hs :
    Cotisations.assietteCSGSalariale Cotisations.parametres2026
      { brutMensuel := 2500, brutHeuresSupplementaires := 300 } = 2717.07 := by
  native_decide

/-! ### Plafonnements chômage / AGS (4 PASS) -/

/-- Chômage : 4 % × min(20 000 ; 4 × 4 005) = 640,80 €. -/
theorem chomage_plafonne :
    (Cotisations.chomagePatronal Cotisations.parametres2026
      { brutMensuel := 20000 } 4005).partPatronale = 640.80 := by
  native_decide

/-- AGS : 0,25 % × 16 020 = 40,05 €. -/
theorem ags_plafonnee :
    (Cotisations.agsPatronale Cotisations.parametres2026
      { brutMensuel := 20000 } 4005).partPatronale = 40.05 := by
  native_decide

/-- Intérimaire : AGS au taux réduit de 0,03 %. -/
theorem ags_interimaire :
    (Cotisations.agsPatronale Cotisations.parametres2026
      { brutMensuel := 20000, contrat := .interimaire } 4005).partPatronale = 4.806 := by
  native_decide

/-! ### Réduction générale dégressive unique — exemples officiels Urssaf -/

/-- Paramètres du 1er juin 2026 (plafond abaissé à 2,9293 SMIC). -/
def paJuin : Cotisations.ParametresAnnee :=
  { Cotisations.parametres2026 with ratioRGDU := 2.9293 }

def peGrand : Cotisations.ParametresEntreprise := { effectif := 60 }

/-- Exemple officiel Urssaf (juin 2026, ≥ 50 salariés, rémunération 2 000 €) :
    coefficient = 0,0200 + 0,3821 × [(2,9293 × 1 867,02 / 2 000 − 1)/2]^1,75 = 0,3178. -/
theorem rgdu_juin_coef :
    Cotisations.dans (Cotisations.coefficientRGDU
      (Cotisations.parametresRGDU paJuin peGrand) 2000 0) 0.3177 0.3179 := by
  native_decide

/-- Montant officiel : 0,3178 × 2 000 ≈ 635,60 €. -/
theorem rgdu_juin_montant :
    Cotisations.dans (Cotisations.montantRGDU
      (Cotisations.parametresRGDU paJuin peGrand) 2000 0) 635.3 635.9 := by
  native_decide

/-- Paramètres de la régularisation progressive (janvier 2026,
    ≥ 50 salariés, SMIC cumulé sur 7 mois). -/
def prgduRegul : Cotisations.ParametresRGDU :=
  { ratioSMIC := 3, tMin := 0.02, tDelta := 0.3821, diviseur := 2
    exposantNum := 7, exposantDen := 4
    partIRCRatio := 0.0601 / 0.4021, partUrssafRatio := 0.3420 / 0.4021
    plafondDFS := 1.30
    smicPeriode := Cotisations.salaireMensuel 12.02 * 7, smicHoraire := 12.02 }

/-- Exemple officiel de régularisation progressive (janvier 2026, ≥ 50 salariés,
    15 000 € cumulés sur 7 mois) : coefficient = 0,2652. -/
theorem rgdu_regul_coef :
    Cotisations.dans (Cotisations.coefficientRGDU prgduRegul 15000 0) 0.2651 0.2653 := by
  native_decide

/-- Réduction cumulée officielle : ≈ 3 978 €. -/
theorem rgdu_regul_montant :
    Cotisations.dans (Cotisations.montantRGDU prgduRegul 15000 0) 3977.5 3979.5 := by
  native_decide

/-- Exemple officiel Mayotte (rémunération 1 600 €, SMIC 1 449,93 €) :
    coefficient = 0,2449 × [(1,6 × 1 449,93/1 600 − 1)/0,6] = 0,1836. -/
theorem rgdu_mayotte_coef :
    Cotisations.dans (Cotisations.coefficientRGDU
      (Cotisations.parametresRGDU Cotisations.parametres2026
        { effectif := 10, region := .mayotte }) 1600 0) 0.1835 0.1838 := by
  native_decide

/-- Au-delà du plafond (2,9293 SMIC en juin 2026), réduction nulle. -/
theorem rgdu_hors_plafond :
    Cotisations.coefficientRGDU (Cotisations.parametresRGDU paJuin peGrand) 6000 0 = 0 := by
  native_decide

/-- La puissance rationnelle exacte 7/4 reproduit l'exposant 1,75 :
    0,867263^1,75 ≈ 0,7794. -/
theorem puissance_7_4 :
    Cotisations.dans (Cotisations.puissanceRat 0.867263 7 4) 0.7793 0.7795 := by
  native_decide

/-! ### Taxes -/

/-- Taxe sur les salaires 2026 (20 000 €/an) : barème 1 388,1945 €,
    décote → 181,424 €. -/
theorem taxe_salaires_20000 :
    Cotisations.dans (Cotisations.taxeSurSalairesSalarie
      Cotisations.parametres2026 false 20000) 181.4 181.5 := by
  native_decide

/-- Sous la franchise (1 200 €) : taxe nulle. -/
theorem taxe_salaires_franchise :
    Cotisations.taxeSurSalairesSalarie Cotisations.parametres2026 false 10000 = 0 := by
  native_decide

/-- Forfait social > 10 PASS : 20 % × (50 000 − 40 050) = 1 990 €. -/
theorem forfait_social_exemple :
    (Cotisations.forfaitSocial Cotisations.parametres2026 { effectif := 100 }
      { brutMensuel := 50000 } 4005).partPatronale = 1990 := by
  native_decide

/-- Versement mobilité : 2,4 % × 3 000 = 72 €. -/
theorem versement_mobilite_exemple :
    (Cotisations.versementMobilite { effectif := 30, tauxVersementMobilite := 0.024 }
      ps3000).partPatronale = 72 := by
  native_decide

/-! ### Convention collective : minimums légaux -/

theorem mutuelle_exemple_conforme :
    Cotisations.mutuelleConforme 60 100 = true := by native_decide

theorem prevoyance_cadres_minimum :
    Cotisations.prevoyanceCadresConforme 0.015 0.60 = true := by native_decide

theorem mutuelle_non_conforme :
    Cotisations.mutuelleConforme 30 100 = false := by native_decide

/-! ### Bulletin complet : invariants -/

def bulletinSMIC : Cotisations.Bulletin :=
  Cotisations.calculeBulletin Cotisations.parametres2026
    { effectif := 30 } { brutMensuel := 1823.03 } none

/-- Net avant impôt = brut − total salarial. -/
theorem net_invariant :
    bulletinSMIC.netAvantIR + bulletinSMIC.totalSalarial = bulletinSMIC.brut := by
  native_decide

/-- Coût employeur = brut + patronal net des réductions. -/
theorem cout_invariant :
    bulletinSMIC.coutEmployeur = bulletinSMIC.brut + bulletinSMIC.totalPatronalNet := by
  native_decide

/-- La somme des versements par organisme = total salarial + total patronal. -/
theorem versements_invariant :
    (bulletinSMIC.versements.foldl (fun acc p => acc + p.2) 0)
      = bulletinSMIC.totalSalarial + bulletinSMIC.totalPatronalNet := by
  native_decide

/-- Au SMIC (1 823,03 €, effectif < 50), la réduction générale est appliquée. -/
theorem rgdu_smic_positive :
    bulletinSMIC.reducGenerale > 0 := by native_decide

/-- Exemple de bulletin cadre (5 000 €, cadre, mutuelle/ prévoyance
    conventionnelles). -/
def bulletinCadre : Cotisations.Bulletin :=
  Cotisations.calculeBulletin Cotisations.parametres2026
    { effectif := 120, tauxVersementMobilite := 0.024, sujetPEEC := true }
    { brutMensuel := 5000, cadre := true }
    (some { nom := "convention d'exemple", mutuelleSalariale := 40, mutuellePatronale := 60
            prevoyanceTauxT1 := 0.015, prevoyancePartPatronale := 0.60 })

theorem net_invariant_cadre :
    bulletinCadre.netAvantIR + bulletinCadre.totalSalarial = bulletinCadre.brut := by
  native_decide

theorem cout_invariant_cadre :
    bulletinCadre.coutEmployeur = bulletinCadre.brut + bulletinCadre.totalPatronalNet := by
  native_decide

theorem versements_invariant_cadre :
    (bulletinCadre.versements.foldl (fun acc p => acc + p.2) 0)
      = bulletinCadre.totalSalarial + bulletinCadre.totalPatronalNet := by
  native_decide

/-- Le bulletin cadre verse bien à l'Agirc-Arrco, à l'APEC, à la mutuelle,
    à la prévoyance et à l'Urssaf. -/
theorem versements_cadre_contiennent :
    (bulletinCadre.versements.any (fun p => p.1 == Cotisations.Organisme.agircArrco)) = true
    ∧ (bulletinCadre.versements.any (fun p => p.1 == Cotisations.Organisme.apec)) = true
    ∧ (bulletinCadre.versements.any (fun p => p.1 == Cotisations.Organisme.mutuelle)) = true
    ∧ (bulletinCadre.versements.any (fun p => p.1 == Cotisations.Organisme.prevoyance)) = true := by
  native_decide

/-! ### Convention SYNTEC (IDCC 1486) : prévoyance -/

def rsSyntec : Cotisations.RegimeSyntech := Cotisations.regimeSyntec2026

/-- Exemple chiffré conventionnel (ingénieur cadre à 5 500 € brut/mois) :
    1,50 % × tranche 1 (4 005 €) = 60,075 €. -/
theorem syntec_prevoyance_cadre_t1 :
    (Cotisations.lignesSyntech rsSyntec
      { brutMensuel := 5500, cadre := true }
      (Cotisations.decoupeTranches 5500 4005)).head!.partPatronale = 60.075 := by
  native_decide

/-- Prévoyance d'un cadre à 5 500 € (grille avenant n° 8) : part patronale
    totale = 60,075 € (T1, employeur) + 16,445/2 € (T2) = 68,2975 €. -/
theorem syntec_prevoyance_cadre_avenant8 :
    Cotisations.sommePatronale (Cotisations.lignesSyntech rsSyntec
      { brutMensuel := 5500, cadre := true }
      (Cotisations.decoupeTranches 5500 4005)) = 68.2975 := by
  native_decide

/-- Part salariale du même cadre : la moitié de la cotisation de branche
    de tranche 2, soit 8,2225 € (la cotisation cadres T1 est employeur). -/
theorem syntec_prevoyance_cadre_salariale :
    Cotisations.sommeSalariale (Cotisations.lignesSyntech rsSyntec
      { brutMensuel := 5500, cadre := true }
      (Cotisations.decoupeTranches 5500 4005)) = 8.2225 := by
  native_decide

/-- Ancienne grille (avant le 01/07/2026) : T2 à 1,13 % → part patronale
    totale = 60,075 + 16,8935/2 = 68,52175 €. -/
theorem syntec_prevoyance_cadre_ancienne_grille :
    Cotisations.sommePatronale (Cotisations.lignesSyntech
      { rsSyntec with tauxBrancheT2 := 0.0113 }
      { brutMensuel := 5500, cadre := true }
      (Cotisations.decoupeTranches 5500 4005)) = 68.52175 := by
  native_decide

/-- Non-cadre 3 000 € : 0,85 % × 3 000 = 25,50 € en tranche 1,
    partagés par moitié (12,75 € / 12,75 €). -/
theorem syntec_prevoyance_branche_t1_etam :
    let l := (Cotisations.lignesSyntech rsSyntec { brutMensuel := 3000 }
      (Cotisations.decoupeTranches 3000 4005)).head!
    l.partSalariale = 12.75 ∧ l.partPatronale = 12.75 := by
  native_decide

/-- La répartition par défaut (moitié / moitié) respecte le plafond
    de part salariale de 50 % ; une répartition 60/40 ne le respecte pas. -/
theorem syntec_repartition_conformite :
    Cotisations.partSalarialeBrancheConforme rsSyntec = true
    ∧ Cotisations.partSalarialeBrancheConforme
        { rsSyntec with partSalarialeBranche := 0.6 } = false := by
  native_decide

/-- Paramètres SYNTEC par défaut conformes. -/
theorem syntec_regime_conforme :
    Cotisations.partSalarialeBrancheConforme rsSyntec = true
    ∧ Cotisations.prevoyanceCadresSyntechConforme rsSyntec = true := by
  native_decide

/-- Minimum capital décès : un cadre dont les ayants droit reçoivent
    144 180 € (3 × PASS 2026) est couvert ; 100 000 € ne suffisent pas ;
    un non-cadre couvert à 96 120 € (2 × PASS) l'est. -/
theorem syntec_capital_deces_minima :
    Cotisations.capitalDecesSyntechConforme true 144180 48060 = true
    ∧ Cotisations.capitalDecesSyntechConforme true 100000 48060 = false
    ∧ Cotisations.capitalDecesSyntechConforme false 96120 48060 = true := by
  native_decide

/-! ### Bulletin SYNTEC complet : invariants -/

/-- Bulletin SYNTEC d'un ingénieur cadre à 5 500 € (effectif 80). -/
def bulletinSyntecCadre : Cotisations.Bulletin :=
  Cotisations.calculeBulletinSyntech Cotisations.parametres2026
    { effectif := 80 }
    { brutMensuel := 5500, cadre := true }
    rsSyntec
    (some { nom := "Syntec — complémentaire santé (avenant n° 8 santé)"
            mutuelleSalariale := 45, mutuellePatronale := 55 })

theorem net_invariant_syntec :
    bulletinSyntecCadre.netAvantIR + bulletinSyntecCadre.totalSalarial
      = bulletinSyntecCadre.brut := by
  native_decide

theorem cout_invariant_syntec :
    bulletinSyntecCadre.coutEmployeur
      = bulletinSyntecCadre.brut + bulletinSyntecCadre.totalPatronalNet := by
  native_decide

theorem versements_invariant_syntec :
    (bulletinSyntecCadre.versements.foldl (fun acc p => acc + p.2) 0)
      = bulletinSyntecCadre.totalSalarial + bulletinSyntecCadre.totalPatronalNet := by
  native_decide

/-- La prévoyance conventionnelle est bien versée à l'organisme de
    prévoyance, en plus de la mutuelle. -/
theorem versements_syntec_prevoyance :
    (bulletinSyntecCadre.versements.any
      (fun p => p.1 == Cotisations.Organisme.prevoyance)) = true := by
  native_decide

/-! ### Affichage de démonstration -/

#eval bulletinSMIC.netAvantIR
#eval bulletinSMIC.coutEmployeur
#eval bulletinSMIC.reducGenerale
#eval bulletinCadre.netAvantIR
#eval bulletinCadre.coutEmployeur
#eval bulletinCadre.versements
#eval bulletinSyntecCadre.netAvantIR
#eval bulletinSyntecCadre.coutEmployeur
#eval bulletinSyntecCadre.totalPatronalNet

end CotationsExamples
