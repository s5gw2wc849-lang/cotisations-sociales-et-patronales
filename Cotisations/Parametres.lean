/-
Paramètres légaux : année (barèmes), entreprise, salarié, convention collective.

Valeurs par défaut = droit applicable au 1er janvier 2026 en métropole
(régime général du secteur privé), d'après :
- Urssaf, « Taux de cotisations – Secteur privé », mis à jour au 01/01/2026 ;
- Agirc-Arrco, « Le calcul des cotisations de retraite complémentaire »
  (paramètres 2026, circulaire 2025-20) ;
- Urssaf, « La réduction générale dégressive unique », mise à jour du 13/07/2026 ;
- barème de la taxe sur les salaires 2026 (rémunérations versées en 2026).

Chaque valeur est un champ modifiable : le modèle reste valable les années
suivantes en changeant les paramètres.
-/
import Cotisations.Basic
import Cotisations.Organismes

namespace Cotisations

/-! ### Types de base -/

/-- Régions à régime spécifique. -/
inductive Region where
  | metropole
  | alsaceMoselle          -- Haut-Rhin, Bas-Rhin, Moselle
  | autresDom              -- Guadeloupe, Martinique, Réunion, Guyane
  | mayotte
  deriving Repr, DecidableEq, Inhabited

/-- Type de contrat de travail. -/
inductive TypeContrat where
  | cdi
  | cddStandard            -- éligible contribution CPF-CDD
  | cddUsage               -- éligible contribution CPF-CDD
  | interimaire            -- intérim : AGS à taux réduit, surcotisation éventuelle
  | apprentissage          -- RGDU non applicable (sauf option)
  | professionnalisation
  deriving Repr, DecidableEq, Inhabited

/-! ### Paramètres annuels (barèmes) -/

/-- Barèmes et taux de l'année. Valeurs = 2026 métropole. -/
structure ParametresAnnee where
  annee : Nat := 2026
  /-- SMIC horaire au 1er janvier (métropole : 12,02 € au 01/01/2026). -/
  smicHoraire : Rat := 12.02
  /-- SMIC horaire après revalorisation en cours d'année (12,31 € au 01/06/2026 ;
      0 si aucune). -/
  smicHoraireJuin : Rat := 12.31
  /-- Ratio plafond de la réduction générale : 3 SMIC au 1er janvier,
      2,9293 SMIC au 1er juin 2026. -/
  ratioRGDU : Rat := 3
  /-- Plafond mensuel de la Sécurité sociale (4 005 € en 2026). -/
  passMensuel : Rat := 4005
  limiteChomagePass : Rat := 4    -- assurance chômage et AGS plafonnées à 4 PASS
  /-- SMIC mensuel de Mayotte (1 449,93 € au 1er juin 2026). -/
  smicMensuelMayotte : Rat := 1449.93

  -- Branche maladie
  tauxMaladie : Rat := 0.13                 -- MMID patronale (13 %)
  tauxCsa : Rat := 0.003                    -- contribution solidarité autonomie
  tauxMaladieAlsaceMoselleSalarie : Rat := 0.013  -- régime local Alsace-Moselle

  -- Branche vieillesse (régime général)
  tauxVieillessePatronalPlafonne : Rat := 0.0855    -- tranche 1
  tauxVieillessePatronalDeplafonne : Rat := 0.0211  -- totalité (2,11 % en 2026)
  tauxVieillesseSalarialPlafonne : Rat := 0.069     -- tranche 1
  tauxVieillesseSalarialDeplafonne : Rat := 0.004   -- totalité

  -- Branche famille
  tauxFamille : Rat := 0.0525
  tauxFamilleReduit : Rat := 0.0345
  seuilFamilleReduitSMIC : Rat := 2.5   -- masse < 250 % du SMIC

  -- Assurance chômage / AGS
  tauxChomage : Rat := 0.04                  -- 4,00 % (2026), plafonné à 4 PASS
  tauxAgs : Rat := 0.0025                    -- 0,25 %, plafonné à 4 PASS
  tauxAgsInterimaire : Rat := 0.0003         -- 0,03 % pour le travail temporaire

  -- FNAL
  tauxFnalPlafonne : Rat := 0.001    -- effectif < 50 : 0,10 % sur la tranche 1
  tauxFnalTotalite : Rat := 0.005    -- effectif ≥ 50 : 0,50 % sur la totalité

  -- CSG / CRDS
  tauxCsgDeductible : Rat := 0.068
  tauxCsgNonDeductible : Rat := 0.024
  tauxCrds : Rat := 0.005
  assietteCsg : Rat := 0.9825                 -- 98,25 % du brut
  abattementHeuresSupSalarial : Rat := 0.1131 -- abattement 11,31 % sur les HS (salarié)

  -- Contributions diverses
  tauxDialogueSocial : Rat := 0.00016  -- ≥ 11 salariés
  tauxCpfCdd : Rat := 0.01             -- contribution CPF-CDD (1 %, tranche 1)
  tauxPEEC : Rat := 0.0045             -- effort construction (≥ 50 salariés)

  -- Formation professionnelle et apprentissage
  tauxFormationProPetit : Rat := 0.0055  -- < 11 salariés
  tauxFormationProGrand : Rat := 0.01    -- ≥ 11 salariés (2026)
  tauxTaxeApprentissagePrincipale : Rat := 0.0059
  tauxTaxeApprentissageSolde : Rat := 0.0009
  tauxTaxeApprentissageAlsaceMoselle : Rat := 0.0044

  -- Réduction générale dégressive unique (RGDU)
  rgduTMin : Rat := 0.0200
  rgduTDeltaPetit : Rat := 0.3781   -- < 50 salariés : Tmax = 0,3981
  rgduTDeltaGrand : Rat := 0.3821   -- ≥ 50 salariés : Tmax = 0,4021
  rgduTDeltaMayotte : Rat := 0.2449 -- Tmax à Mayotte (P = 1, Tmin = 0)
  rgduExposantNum : Nat := 7        -- exposant 7/4 = 1,75
  rgduExposantDen : Nat := 4
  rgduPartIRCT1 : Rat := 0.0601     -- Agirc-Arrco T1 dans la cible
  rgduPartUrssafPetit : Rat := 0.3380
  rgduPartUrssafGrand : Rat := 0.3420
  rgduPlafondDFS : Rat := 1.30      -- plafond de la réduction avec DFS

  -- Heures supplémentaires (déduction forfaitaire patronale)
  deductionHSGrand : Rat := 1.50    -- ≥ 20 salariés : 1,50 €/h
  deductionHSPetit : Rat := 0.25    -- < 20 salariés : 0,25 €/h

  -- Taxe sur les salaires (barème annuel par salarié, 2026)
  tsSeuil1 : Rat := 9229
  tsSeuil2 : Rat := 18423
  tsTaux1 : Rat := 0.0425
  tsTaux2 : Rat := 0.0850
  tsTaux3 : Rat := 0.1360
  tsFranchise : Rat := 1200
  tsSeuilDecote : Rat := 2640
  tsAbattementAssociation : Rat := 24256

  -- Forfait social sur les rémunérations > 10 PASS
  fsSeuilPass : Rat := 10
  fsTauxPetit : Rat := 0.20
  fsTauxGrand : Rat := 0.30
  fsSeuilEffectifGrand : Nat := 250

  deriving Repr, DecidableEq

/-- SMIC horaire applicable à la réduction générale selon la période. -/
def ParametresAnnee.smicHoraireRGDU (pa : ParametresAnnee) : Rat :=
  if pa.ratioRGDU == 3 then pa.smicHoraire else pa.smicHoraireJuin

/-- Nombre d'heures annuelles temps plein (35 h × 52 = 1 820 h), base
    des conversions entre taux horaire et salaire mensuel ou annuel. -/
def heuresAnnuelles : Rat := 1820

/-- Salaire mensuel correspondant à un taux horaire (base 1 820 h/an).
    Utilisé pour le SMIC de la période de la réduction générale. -/
def salaireMensuel (tauxHoraire : Rat) : Eur :=
  tauxHoraire * heuresAnnuelles / (12 : Rat)

/-- SMIC mensuel temps plein. -/
def ParametresAnnee.smicMensuel (pa : ParametresAnnee) : Eur :=
  salaireMensuel pa.smicHoraire

/-- SMIC annuel temps plein. -/
def ParametresAnnee.smicAnnuel (pa : ParametresAnnee) : Eur :=
  pa.smicHoraire * heuresAnnuelles

/-- PASS annuel. -/
def ParametresAnnee.passAnnuel (pa : ParametresAnnee) : Eur :=
  pa.passMensuel * 12

/-- Barèmes officiels 2026, métropole. -/
def parametres2026 : ParametresAnnee := {}

/-! ### Paramètres entreprise -/

structure ParametresEntreprise where
  /-- Effectif au sens Urssaf (seuils 11, 20, 50, 250 salariés). -/
  effectif : Nat := 1
  region : Region := .metropole
  /-- Taux notifié par la Carsat pour les AT/MP (0 = pas de taux communiqué). -/
  tauxATMP : Rat := 0
  /-- Taux de versement mobilité de l'AOM (0 = hors périmètre). -/
  tauxVersementMobilite : Rat := 0
  /-- Entreprise soumise à l'obligation PEEC (≥ 50 salariés : 0,45 %). -/
  sujetPEEC : Bool := false
  /-- Employeur assujetti à la taxe sur les salaires (TVA < 90 %). -/
  assujettiTaxeSalaires : Bool := false
  estAssociation : Bool := false
  /-- Régime réel : la CSG salariale 6,8 % est déductible du revenu imposable. -/
  regimeReel : Bool := true
  /-- Taux de la contribution supplémentaire à l'apprentissage (selon
      ratio d'alternants ; 0 si ratio ≥ 5 % ou effectif < 250). -/
  tauxCSAApprentissage : Rat := 0
  /-- Contribution annuelle OETH (DOETH), montant calculé par ailleurs. -/
  contributionOETHAnnuelle : Eur := 0
  /-- Caisses de congés payés / intempéries (BTP, transport…) : taux appliqué
      à la totalité de la masse (recouvré par la caisse, pas par l'Urssaf). -/
  tauxCaisseCongesPayes : Rat := 0
  /-- La masse salariale annuelle reste sous 250 % du SMIC (taux famille réduit). -/
  familleTauxReduit : Bool := true

  deriving Repr, DecidableEq

/-- Taux famille applicable. -/
def ParametresEntreprise.tauxFamille (pe : ParametresEntreprise) (pa : ParametresAnnee) : Rat :=
  if pe.familleTauxReduit then pa.tauxFamilleReduit else pa.tauxFamille

/-! ### Paramètres salarié -/

structure ParametresSalarie where
  /-- Rémunération brute du mois, hors heures supplémentaires,
      hors remboursements de frais (exonérés). -/
  brutMensuel : Eur
  /-- Montant brut des heures supplémentaires / complémentaires. -/
  brutHeuresSupplementaires : Eur := 0
  /-- Nombre d'heures supplémentaires / complémentaires du mois. -/
  nombreHeuresSupplementaires : Rat := 0
  cadre : Bool := false
  /-- Plafond proratisé (temps partiel, entrée/sortie en cours de mois) :
      1 = mois complet. -/
  prorataPlafond : Rat := 1
  contrat : TypeContrat := .cdi
  /-- Affilié à l'assurance chômage (l'est par défaut dans le secteur privé). -/
  assujettiChomage : Bool := true
  /-- Prime de partage de la valeur du mois (incluse dans la base RGDU
      depuis 2025, qu'elle soit placée ou non). -/
  primePartageValeur : Eur := 0

  deriving Repr, DecidableEq

/-- Assiette brute de sécurité sociale du salarié (frais exclus). -/
def ParametresSalarie.assietteSecu (ps : ParametresSalarie) : Eur :=
  ps.brutMensuel + ps.brutHeuresSupplementaires

/-- Assiette retenue pour la réduction générale (brut + PPV). -/
def ParametresSalarie.assietteRGDU (ps : ParametresSalarie) : Eur :=
  ps.brutMensuel + ps.brutHeuresSupplementaires + ps.primePartageValeur

/-! ### Convention collective

Le droit légal (régime général + Agirc-Arrco) est codé en dur dans les
modules suivants ; la convention collective s'intègre ici comme source
de cotisations complémentaires (mutuelle, prévoyance, retraite
supplémentaire, caisses spéciales). Seule la convention applicable à
l'entreprise doit être instanciée. -/

/-- Régime de protection sociale complémentaire. -/
structure RegimeComplementaire where
  tauxSalarial : Rat := 0
  tauxPatronal : Rat := 0
  /-- Commentaire (ex. « taux conventionnel, art. X »). -/
  commentaire : String := ""
  deriving Repr, DecidableEq, Inhabited

/-- Cotisations complémentaires issues de la convention collective. -/
structure ConventionCollective where
  /-- Nom de la convention (ex. « Hôtellerie-restauration »). -/
  nom : String := ""
  /-- Complémentaire santé obligatoire : part patronale ≥ 50 % du coût
      (ANI 2013, codifié art. L911-7 du code de la sécurité sociale). -/
  mutuelleSalariale : Eur := 0
  mutuellePatronale : Eur := 0
  /-- Prévoyance décès. Pour les cadres, obligation légale d'une couverture
      au moins égale à 1,5 % de la tranche 1, prise en charge à au moins
      60 % par l'employeur (art. L911-2 CSS / AGIRC-ARRCO). -/
  prevoyanceTauxT1 : Rat := 0
  prevoyancePartPatronale : Rat := 0
  /-- Retraite supplémentaire (tranches 1/2, taux conventionnels). -/
  retraiteSupplementaireT1 : RegimeComplementaire := {}
  retraiteSupplementaireT2 : RegimeComplementaire := {}
  /-- Taux versé à une caisse de congés payés conventionnelle
      (recouvrement par la caisse, en plus des cotisations légales). -/
  tauxCaisseCongesPayes : Rat := 0

  deriving Repr, DecidableEq, Inhabited

end Cotisations