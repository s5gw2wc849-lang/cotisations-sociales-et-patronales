/-
Convention collective nationale SYNTEC — bureaux d'études techniques,
cabinets d'ingénieurs-conseils et sociétés de conseils (IDCC 1486).

Spécificités conventionnelles en matière de cotisations :

1. Prévoyance décès des cadres (art. 7 de la CCN des cadres du 14 mars
   1947, repris par la convention) : cotisation obligatoire d'au moins
   1,50 % de la tranche 1, à la charge de l'employeur, affectée en
   priorité à la garantie décès (au moins 0,76 point) et à l'incapacité/
   invalidité (0,74 point). À défaut, l'employeur doit verser aux
   ayants droit trois plafonds annuels de la Sécurité sociale.

2. Prévoyance de branche (accord du 27 mars 1997 relatif à la prévoyance
   lourde, modifié par l'avenant n° 8 du 16 décembre 2025, étendu par
   arrêté du 21 mai 2026, en vigueur le 1er juillet 2026) : cotisation
   de 0,85 % sur la tranche 1 et 1,10 % sur la tranche 2, partagée entre
   l'entreprise et le salarié, la part salariale restant plafonnée à la
   moitié du total. Pour les cadres, la cotisation de tranche 1 de
   1,50 % couvre le socle de branche (pas de cumul).
   Garanties : capital décès de 200 % du salaire de référence, avec des
   minima de 200 % du PASS pour les non-cadres et 300 % du PASS pour les
   cadres ; rente d'éducation de 12 % du salaire de référence par enfant
   (15 % en cas d'études jusqu'à 26 ans) ; carence incapacité de
   90 jours, indemnisation jusqu'à 80 % du salaire brut.

3. Complémentaire santé (avenant n° 8 santé du 14 février 2025, en
   vigueur le 1er janvier 2026) : répartition de la cotisation avec une
   part patronale d'au moins 50 % (ANI du 11 janvier 2013) ; les
   montants dépendent du contrat choisi (passés en paramètre).

La branche ne prévoit ni caisse de congés payés ni retraite
supplémentaire obligatoire.
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.Bulletin
import Cotisations.Convention

namespace Cotisations

/-- Paramètres du régime de prévoyance SYNTEC. Valeurs = avenant n° 8
    (prévoyance) en vigueur au 1er juillet 2026. -/
structure RegimeSyntech where
  /-- Obligation décès cadres : 1,50 % de la tranche 1. -/
  tauxCadresT1 : Rat := 0.015
  /-- Part patronale de la cotisation cadres (art. 7 : employeur seul). -/
  partPatronaleCadres : Rat := 1
  /-- Prévoyance de branche, tranche 1 (0,85 % depuis le 01/07/2026). -/
  tauxBrancheT1 : Rat := 0.0085
  /-- Prévoyance de branche, tranche 2 (1,10 % depuis le 01/07/2026 ;
      1,13 % avant). -/
  tauxBrancheT2 : Rat := 0.011
  /-- Part salariale de la cotisation de branche (plafond légal : 50 %). -/
  partSalarialeBranche : Rat := 0.5
  deriving Repr, DecidableEq

/-- Paramètres officiels SYNTEC (avenant n° 8 prévoyance, 01/07/2026). -/
def regimeSyntec2026 : RegimeSyntech := {}

/-- La part salariale de branche respecte-t-elle le plafond de 50 % ? -/
def partSalarialeBrancheConforme (rs : RegimeSyntech) : Bool :=
  rs.partSalarialeBranche ≤ 0.5

/-- La cotisation cadres atteint-elle le minimum conventionnel de 1,50 % ? -/
def prevoyanceCadresSyntechConforme (rs : RegimeSyntech) : Bool :=
  rs.tauxCadresT1 ≥ 0.015 ∧ rs.partPatronaleCadres ≥ 0.60

/-- Le capital décès servi atteint-il le minimum de branche ?
    200 % du PASS (non-cadres) ou 300 % du PASS (cadres). -/
def capitalDecesSyntechConforme (cadre : Bool) (capitalDeces passAnnuel : Eur) : Bool :=
  if cadre then passAnnuel * 3 ≤ capitalDeces
  else passAnnuel * 2 ≤ capitalDeces

/-- Lignes de prévoyance SYNTEC d'un salarié :
    - cadre : 1,50 % de la tranche 1 (employeur) + 1,10 % de la tranche 2 ;
    - non-cadre : 0,85 % de la tranche 1 + 1,10 % de la tranche 2. -/
def lignesSyntech (rs : RegimeSyntech) (ps : ParametresSalarie)
    (t : Tranches) : List LigneCotisation :=
  (if ps.cadre then
    [ ({ nom := "Prévoyance cadres — décès, incapacité, invalidité (CCN Syntec, art. 7 CCN cadres)"
         organisme := .prevoyance, nature := .cotisation, cote := .mixte
         assiette := t.tranche1
         partSalariale := (1 - rs.partPatronaleCadres) * rs.tauxCadresT1 * t.tranche1
         partPatronale := rs.partPatronaleCadres * rs.tauxCadresT1 * t.tranche1
         commentaire := "1,50 % T1 minimum, dont 0,76 pt décès en priorité" } : LigneCotisation) ]
  else
    [ ({ nom := "Prévoyance de branche — tranche 1 (CCN Syntec, avenant n° 8)"
         organisme := .prevoyance, nature := .cotisation, cote := .mixte
         assiette := t.tranche1
         partSalariale := rs.partSalarialeBranche * rs.tauxBrancheT1 * t.tranche1
         partPatronale := (1 - rs.partSalarialeBranche) * rs.tauxBrancheT1 * t.tranche1
         commentaire := "0,85 % T1 depuis le 01/07/2026 (0,74 % avant)" } : LigneCotisation) ])
  ++ (if t.tranche2 > 0 then
    [ ({ nom := "Prévoyance de branche — tranche 2 (CCN Syntec, avenant n° 8)"
         organisme := .prevoyance, nature := .cotisation, cote := .mixte
         assiette := t.tranche2
         partSalariale := rs.partSalarialeBranche * rs.tauxBrancheT2 * t.tranche2
         partPatronale := (1 - rs.partSalarialeBranche) * rs.tauxBrancheT2 * t.tranche2
         commentaire := "1,10 % T2 depuis le 01/07/2026 (1,13 % avant)" } : LigneCotisation) ]
  else [])

/-- Bulletin complet d'un salarié de la branche SYNTEC : bulletin légal
    (incluant la mutuelle passée en convention), augmenté des lignes de
    prévoyance conventionnelles. -/
def calculeBulletinSyntech (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (rs : RegimeSyntech)
    (cc : Option ConventionCollective) : Bulletin :=
  let base := calculeBulletin pa pe ps cc
  let plafond := plafondMensuelProratise pa ps
  let t := decoupeTranches ps.assietteSecu plafond
  let sy := lignesSyntech rs ps t
  let sal := sommeSalariale sy
  let pat := sommePatronale sy
  { base with
    lignesPatronales := base.lignesPatronales ++ sy.filter (fun l => !l.estNulle)
    totalSalarial := base.totalSalarial + sal
    netAvantIR := base.netAvantIR - sal
    totalPatronalNet := base.totalPatronalNet + pat
    coutEmployeur := base.coutEmployeur + pat
    versements := versementsParOrganisme
      (base.lignesSalariales ++ base.lignesRetraite ++ base.lignesPatronales
        ++ sy ++ base.lignesReductions) }

end Cotisations
