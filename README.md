# Cotisations sociales et patronales — règles légales françaises en Lean 4

Modèle Lean 4 du bloc « cotisations et contributions sociales » du bulletin
de paie français, pour le régime général du secteur privé (métropole, Dom,
Alsace-Moselle, Mayotte) complété par la convention collective SYNTEC
(IDCC 1486).

Le projet code toutes les lignes situées après le brut : cotisations
salariales, cotisations patronales, mutuelle, prévoyance, retraite
complémentaire, CSG/CRDS, taxes, réductions — avec, pour chaque ligne,
l'organisme collecteur, la nature juridique et les agrégats de versement.

Tous les montants sont des rationnels exacts (`Rat`) : aucune perte de
précision. Les identités et les cas chiffrés officiels sont vérifiés par
des théorèmes (`native_decide`) : le compilateur prouve que le code
calcule les valeurs attendues.

## Couverture

**Cotisations légales (recouvrées par l'Urssaf via la DSN)** — maladie,
maternité, invalidité, décès (13 %), contribution solidarité autonomie
(0,30 %), régime local Alsace-Moselle (1,30 % salarié), assurance
vieillesse plafonnée (8,55 % / 6,90 %) et déplafonnée (2,11 % / 0,40 %),
allocations familiales (5,25 % / 3,45 %), FNAL (0,10 % / 0,50 %),
assurance chômage (4,00 %, plafonnée à 4 PASS), AGS (0,25 %, 0,03 %
intérim), contribution au dialogue social (0,016 %), accidents du travail
(taux Carsat paramétré), CSG déductible (6,80 %) et non déductible
(2,40 %), CRDS (0,50 %) sur 98,25 % du brut avec abattement de 11,31 %
sur les heures supplémentaires.

**Retraite complémentaire (Agirc-Arrco, paramètres 2026)** — tranche 1 :
3,15 % salarié / 4,72 % employeur (taux appelé 7,87 %) ; tranche 2 :
8,64 % / 12,95 % (21,59 %) ; CEG (2,15 % T1, 2,70 % T2) ; CET (0,35 %
sur T1+T2 au-delà du PASS) ; APEC (0,06 %, cadres, jusqu'à 4 PASS).

**Réduction générale dégressive unique (RGDU 2026)** — la réduction qui
remplace la réduction « Fillon » : coefficient `T_min + T_delta ×
((ratioSMIC × SMIC de référence / rémunération − 1) / 2)^1,75`, avec
T_min = 0,0200, T_delta = 0,3781 (< 50 salariés) ou 0,3821 (≥ 50),
plafond à 3 SMIC (2,9293 SMIC au 1er juin 2026), imputation Urssaf /
institutions de retraite complémentaire (0,3420 + 0,0601 = 0,4021),
variante Mayotte (1,6 SMIC, T_delta = 0,2449), DFS plafonnée à 130 %,
déduction forfaitaire heures supplémentaires (1,50 €/h ou 0,25 €/h).
Les trois exemples chiffrés officiels de l'Urssaf sont prouvés
(coefficient 0,3178 ; régularisation 0,2652 → 3 978 € ; Mayotte 0,1836).

**Taxes et contributions annexes** — formation professionnelle (0,55 % /
1,00 %), taxe d'apprentissage (0,59 % + 0,09 % ; 0,44 % Alsace-Moselle),
contribution supplémentaire à l'apprentissage (paramètre), effort
construction PEEC (0,45 %, ≥ 50 salariés), versement mobilité (taux de
l'AOM), contribution CPF-CDD (1 %), forfait social sur les rémunérations
> 10 PASS (20 % / 30 %), taxe sur les salaires (barème annuel 2026 :
4,25 % / 8,50 % / 13,60 %, seuils 9 229 € et 18 423 €, franchise
1 200 €, décote, abattement associations 24 256 €), contribution OETH
(montant paramétré).

**Convention collective SYNTEC (IDCC 1486)** — prévoyance décès des
cadres (art. 7 CCN cadres 1947 : 1,50 % de la tranche 1 à la charge de
l'employeur, dont 0,76 point décès en priorité) ; prévoyance de branche
(accord du 27 mars 1997 modifié par l'avenant n° 8 du 16 décembre 2025,
en vigueur au 1er juillet 2026 : 0,85 % tranche 1 / 1,10 % tranche 2,
part salariale plafonnée à 50 %) ; minima de capital décès vérifiés
(200 % du PASS non-cadres, 300 % du PASS cadres) ; complémentaire santé
avec part patronale ≥ 50 %. L'exemple chiffré conventionnel du cadre à
5 500 € brut est prouvé (60,075 € en tranche 1, 16,445 € en tranche 2
avec la grille 2026, 16,8935 € avec l'ancienne grille).

**Organismes et bulletin** — chaque ligne est rattachée à son organisme
(Urssaf, Agirc-Arrco, APEC, DGFiP, Carsat, mutuelle, prévoyance, caisse
de congés payés) ; le bulletin calcule le net avant impôt, le coût
employeur global, la réduction générale et la ventilation des versements
par organisme. Les invariants (net = brut − salarial, coût = brut +
patronal, somme des versements = salarial + patronal) sont prouvés sur
les bulletins d'exemple.

## Structure

```
Cotisations.lean                    — racine (importe tous les modules)
Cotisations/
  Basic.lean                        — Eur, Taux, racines n-ièmes exactes (Newton),
                                      puissance rationnelle 10⁻¹⁰
  Organismes.lean                   — organismes, natures, lignes de bulletin,
                                      agrégats par organisme
  Parametres.lean                   — barèmes 2026 (année, entreprise, salarié),
                                      convention collective générique
  Assiette.lean                     — tranches 1/2/3, plafonds proratisés, assiette CSG
  CotisationsLegales.lean           — cotisations Urssaf, parts salariale et patronale
  RetraiteComplementaire.lean       — Agirc-Arrco, CEG, CET, APEC
  ReducGenerale.lean                — réduction générale dégressive unique
  Taxes.lean                        — taxes et contributions annexes
  Convention.lean                   — mutuelle, prévoyance, retraite supplémentaire
  Syntech.lean                      — convention SYNTEC (IDCC 1486)
  Bulletin.lean                     — assemblage du bulletin complet
  Exemples.lean                     — théorèmes de vérification (exemples officiels)
```

## Utilisation

```lean
import Cotisations

open Cotisations

-- Bulletin d'un non-cadre au SMIC, entreprise de 30 salariés, 2026
def b : Bulletin :=
  calculeBulletin parametres2026 { effectif := 30 } { brutMensuel := 1823.03 } none

#eval b.netAvantIR        -- net avant impôt
#eval b.coutEmployeur     -- coût global employeur
#eval b.versements        -- versements par organisme

-- Bulletin SYNTEC d'un ingénieur cadre à 5 500 €
def bs : Bulletin :=
  calculeBulletinSyntech parametres2026 { effectif := 80 }
    { brutMensuel := 5500, cadre := true } regimeSyntec2026 none
```

Chaque paramètre (taux, seuils, effectif, région, type de contrat,
heures supplémentaires, répartitions conventionnelles…) est un champ de
structure : le modèle reste valable les années suivantes en changeant
les valeurs (les valeurs par défaut sont celles du 1er janvier 2026).

## Compilation

Lean 4 (toolchain `v4.34.1`), sans dépendance externe :

```
lake build
```

## Sources

- Urssaf, « Taux de cotisations – Secteur privé » (mis à jour au 01/01/2026) ;
- Urssaf, « La réduction générale dégressive unique » (mise à jour du 13/07/2026),
  code de la sécurité sociale, art. L241-13 et D241-7 et suivants, BOSS ;
- Agirc-Arrco, « Le calcul des cotisations de retraite complémentaire »,
  paramètres 2026 (circulaire 2025-20) ;
- Avenant n° 8 du 16 décembre 2025 à l'accord du 27 mars 1997 relatif à la
  prévoyance (CCN Syntec, IDCC 1486), étendu par arrêté du 21 mai 2026 ;
- Barème de la taxe sur les salaires 2026 (rémunérations versées en 2026).

## Limites connues

Le projet est un modèle des règles de calcul, pas un logiciel de paie
certifié : pas de gestion de la DSN réelle, des régularisations annuelles
complètes, des exonérations zonées (Lodéom, ZRR…), de l'activité
partielle, ni des cumuls d'exonérations ; le barème de la contribution
supplémentaire à l'apprentissage et le calcul du DOETH en points sont
passés en paramètres ; les montants de mutuelle dépendent du contrat de
l'entreprise. Sans Mathlib, les propriétés génériques du découpage en
tranches sont vérifiées sur des cas concrets plutôt que prouvées en
toute généralité.
