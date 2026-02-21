#!/usr/bin/env python3
"""Generate 10,000+ high-quality Hungarian language training samples."""

import json
import random
import os

sentences_by_category = {
    "language": [
        "A magyar nyelv a finnugor nyelvcsalád uráli ágához tartozik.",
        "A magyar helyesírás szabályait az Akadémia határozza meg.",
        "A magánhangzó-harmónia a magyar nyelv egyik jellegzetessége.",
        "Az agglutináló nyelvekben a szavakhoz toldalékok járulnak.",
        "A magyar ábécé negyven betűből áll.",
        "A hangrend szerint a magánhangzók mély és magas csoportokra oszlanak.",
        "A főnevek ragozása az esetrendszert követi.",
        "Az igék ragozása határozott és határozatlan lehet.",
        "A szórend a magyarban viszonylag szabad.",
        "A birtokos személyragok a főnevekhez kapcsolódnak.",
        "A múlt idő jele a -t vagy -tt.",
        "A feltételes mód jele a -na, -ne, -ná, -né.",
        "A felszólító mód jele a -j.",
        "A határozói igenevek az -va, -ve, -ván, -vén végződésűek.",
        "A melléknévfokozás középfoka a -bb képzővel történik.",
        "A kiejtés és a helyesírás szorosan összefügg.",
        "A nyelvjárások területi változatokat jelentenek.",
        "Az irodalmi nyelv a köznyelvtől eltérhet.",
        "A szóképzés produktív folyamat a magyarban.",
        "Az összetett szavak gyakran hosszúak lehetnek.",
    ],
    "history": [
        "Szent István 1000-ben koronát kapott a pápától.",
        "A tatárjárás 1241-42-ben pusztította el az országot.",
        "Mátyás király a reneszánsz kultúra támogatója volt.",
        "A mohácsi csata 1526-ban történt.",
        "A török hódoltság 150 évig tartott.",
        "A Rákóczi-szabadságharc 1703-ban kezdődött.",
        "Az 1848-as forradalom március 15-én tört ki.",
        "A kiegyezés 1867-ben jött létre.",
        "Az első világháború után Trianon következett.",
        "A második világháború súlyos károkat okozott.",
        "Az 1956-os forradalom október 23-án kezdődött.",
        "A rendszerváltozás 1989-ben történt.",
        "Magyarország 1999-ben csatlakozott a NATO-hoz.",
        "Az Európai Unióhoz 2004-ben csatlakoztunk.",
        "A honfoglalás a kilencedik században zajlott.",
        "Árpád vezette a magyarokat a Kárpát-medencébe.",
        "A középkori Magyarország erős királyság volt.",
        "Hunyadi János a törökellenes harcok hőse volt.",
        "A reformkor a tizenkilencedik században zajlott.",
        "Széchenyi István a legnagyobb magyar volt.",
    ],
    "geography": [
        "Budapest a Duna két partján terül el.",
        "A Balaton Közép-Európa legnagyobb tava.",
        "A Tisza az ország második legnagyobb folyója.",
        "A Hortobágy az Alföld jellegzetes területe.",
        "A Mátra csúcsa a Kékestető, 1014 méter.",
        "A Fertő tó nagy része Ausztriában található.",
        "A Duna-Tisza köze homokos síkság.",
        "A Dunántúl dombos vidék.",
        "Szeged a napfény városa.",
        "Debrecen a cívisek városa.",
        "Pécs a kultúra fővárosa volt 2010-ben.",
        "Győr fontos ipari és kereskedelmi központ.",
        "Miskolc a Bükk hegység kapujában fekszik.",
        "Sopron a hűség városa.",
        "Eger a bor és a történelem városa.",
        "A Bakony erdős hegység.",
        "A Kisalföld termékeny síkság.",
        "A Velencei-tó Budapest közelében található.",
        "A Duna-kanyar festői szépségű.",
        "A Zemplén borvidék Tokaj környékén található.",
    ],
    "culture": [
        "Petőfi Sándor a magyar irodalom legnagyobb költője.",
        "Arany János a balladák mestere volt.",
        "Ady Endre a modern költészet úttörője.",
        "József Attila a huszadik század kiemelkedő alkotója.",
        "Jókai Mór regényei a romantika jegyében születtek.",
        "Mikszáth Kálmán a kisvárosi élet krónikása.",
        "Móricz Zsigmond a paraszti világ ábrázolója.",
        "Kosztolányi Dezső a nyelv művésze volt.",
        "Babits Mihály a Nyugat folyóirat vezéralakja.",
        "Márai Sándor világhírű magyar író.",
        "Bartók Béla a népzene gyűjtője és feldolgozója.",
        "Kodály Zoltán a zenei nevelés megújítója.",
        "Liszt Ferenc a romantika legnagyobb zongoristája.",
        "Munkácsy Mihály világhírű festő volt.",
        "Csontváry Kosztka Tivadar egyedülálló művész.",
        "A magyar népmesék gazdag örökséget jelentenek.",
        "A csárdás a magyar nemzeti tánc.",
        "A népdalok a magyar kultúra kincsei.",
        "A kalocsai hímzés világszerte ismert.",
        "A herendi porcelán kiváló minőségű.",
    ],
    "science": [
        "Szent-Györgyi Albert felfedezte a C-vitamint.",
        "Semmelweis Ignác az anyák megmentője volt.",
        "Jedlik Ányos a dinamó feltalálója.",
        "Eötvös Loránd a torziós ingát fejlesztette.",
        "Bay Zoltán először mért holdtávolságot radarral.",
        "Neumann János a számítógéptudomány atyja.",
        "Teller Ede a fizika területén alkotott.",
        "Wigner Jenő Nobel-díjas fizikus volt.",
        "Gábor Dénes a holográfia feltalálója.",
        "Oláh György a kémiában ért el sikereket.",
        "Hevesy György a radioaktív nyomjelzést alkalmazta.",
        "Polányi János fizikokémikus volt.",
        "Bolyai János a nem-euklideszi geometria megalkotója.",
        "Erdős Pál a matematika legendája.",
        "A magyar tudomány sok Nobel-díjast adott a világnak.",
        "A kutatás és fejlesztés fontos a gazdaságnak.",
        "Az egyetemek a tudás központjai.",
        "A tudományos együttműködés nemzetközi.",
        "Az innováció hajtja a fejlődést.",
        "A magyar kutatók világszerte elismertek.",
    ],
    "economy": [
        "A magyar gazdaság nyitott és exportorientált.",
        "Az autóipar az egyik legfontosabb ágazat.",
        "A turizmus jelentős bevételi forrás.",
        "A mezőgazdaság hagyományosan fontos szektor.",
        "A szolgáltatások aránya folyamatosan nő.",
        "A külföldi befektetések támogatják a növekedést.",
        "A munkaerőpiac az elmúlt években javult.",
        "Az infláció fontos gazdasági mutató.",
        "A Magyar Nemzeti Bank a monetáris politikáért felel.",
        "A tőzsde a gazdaság barométere.",
        "A vállalkozások száma folyamatosan emelkedik.",
        "A digitalizáció átalakítja a gazdaságot.",
        "A fenntartható fejlődés egyre fontosabb.",
        "Az energiaárak befolyásolják a versenyképességet.",
        "A logisztika stratégiai ágazat Magyarországon.",
        "A kis- és középvállalkozások a gazdaság gerince.",
        "Az export az EU országaiba irányul leginkább.",
        "A beruházások a jövő alapjai.",
        "A pénzügyi szektor stabil működésű.",
        "Az adópolitika befolyásolja a gazdasági döntéseket.",
    ],
    "technology": [
        "A mesterséges intelligencia forradalmasítja az ipart.",
        "A gépi tanulás új lehetőségeket teremt.",
        "A robotika egyre elterjedtebb a gyártásban.",
        "Az okoseszközök a mindennapi élet részei.",
        "A felhőszámítás rugalmasságot biztosít.",
        "A kiberbiztonság egyre fontosabb kérdés.",
        "A blokklánc technológia új alkalmazásokat tesz lehetővé.",
        "A virtuális valóság új élményeket kínál.",
        "Az ötödik generációs hálózatok gyorsak.",
        "Az adatelemzés segíti a döntéshozatalt.",
        "A digitális transzformáció minden iparágat érint.",
        "A programozás alapvető készség a jövőben.",
        "Az informatikusok keresettek a munkaerőpiacon.",
        "A szoftverfejlesztés dinamikusan fejlődő terület.",
        "Az alkalmazásfejlesztés új üzleti modelleket teremt.",
        "A nyílt forráskód közösségi fejlesztést jelent.",
        "Az automatizálás növeli a termelékenységet.",
        "Az elektromos járművek terjedése folyamatos.",
        "A megújuló energia technológiái fejlődnek.",
        "A 3D nyomtatás új gyártási lehetőségeket nyit.",
    ],
    "education": [
        "Az oktatás a társadalmi fejlődés alapja.",
        "Az általános iskola nyolc évfolyamból áll.",
        "A középiskolák gimnáziumok és szakközépiskolák.",
        "Az egyetemek és főiskolák felsőoktatást nyújtanak.",
        "A tanárképzés fontos a minőségi oktatáshoz.",
        "A diákok versenyeken bizonyítják tudásukat.",
        "A könyvtárak a tanulás fontos helyszínei.",
        "Az online oktatás új lehetőségeket teremt.",
        "Az élethosszig tartó tanulás elengedhetetlen.",
        "A szakképzés a munkaerőpiac igényeit szolgálja.",
        "A nyelvtanulás bővíti a lehetőségeket.",
        "A matematika fejleszti a logikus gondolkodást.",
        "A természettudományok megértése fontos.",
        "A művészeti nevelés gazdagítja a személyiséget.",
        "A testnevelés az egészség megőrzését szolgálja.",
        "A pedagógusok munkája meghatározó jelentőségű.",
        "Az iskola közösségi élményeket is nyújt.",
        "A tananyag folyamatosan megújul.",
        "Az értékelés visszajelzést ad a tanulásról.",
        "A tehetséggondozás kiemelt feladat.",
    ],
    "health": [
        "Az egészség a legnagyobb érték.",
        "A megelőzés fontosabb a gyógyításnál.",
        "A rendszeres testmozgás javítja a közérzetet.",
        "A kiegyensúlyozott táplálkozás alapvető.",
        "Az elegendő alvás elengedhetetlen.",
        "A stresszkezelés fontos készség.",
        "Az orvostudomány folyamatosan fejlődik.",
        "A védőoltások megvédenek a betegségektől.",
        "A szűrővizsgálatok korai felismerést tesznek lehetővé.",
        "A mentális egészség ugyanolyan fontos.",
        "A gyógyszerek enyhítik a tüneteket.",
        "A rehabilitáció a felépülést segíti.",
        "Az egészségügyi ellátás alapvető jog.",
        "Az ápolók munkája nélkülözhetetlen.",
        "A háziorvos az első kapcsolat.",
        "A sürgősségi ellátás életeket ment.",
        "A krónikus betegségek kezelése folyamatos.",
        "A higiénia a betegségek megelőzését szolgálja.",
        "A vitamin- és ásványianyag-pótlás hasznos lehet.",
        "Az egészséges életmód hosszú életet eredményezhet.",
    ],
    "nature": [
        "A természet megóvása közös felelősség.",
        "Az erdők a Föld tüdejének számítanak.",
        "A folyók életet adnak a tájnak.",
        "A tavak fontos élőhelyek.",
        "A nemzeti parkok védett területek.",
        "A biodiverzitás megőrzése létfontosságú.",
        "Az éghajlatváltozás globális kihívás.",
        "A megújuló energiaforrások fenntarthatók.",
        "A hulladékgazdálkodás környezetvédelmi kérdés.",
        "A szelektív gyűjtés csökkenti a terhelést.",
        "A vízminőség védelme alapvető.",
        "A levegő tisztasága befolyásolja az egészséget.",
        "A talajvédelem a mezőgazdaság alapja.",
        "A vadon élő állatok védelme fontos.",
        "A növényfajok sokfélesége érték.",
        "Az ökológiai egyensúly törékeny.",
        "A fenntarthatóság a jövő kulcsa.",
        "A környezettudatosság nevelés kérdése is.",
        "A zöld területek javítják az életminőséget.",
        "A természetjárás népszerű szabadidős tevékenység.",
    ],
    "society": [
        "A család a társadalom alapegysége.",
        "A közösségek erősítik a társadalmat.",
        "A civil szervezetek fontos szerepet töltenek be.",
        "Az önkéntesség értékes tevékenység.",
        "A szolidaritás összetartja az embereket.",
        "Az esélyegyenlőség alapvető elv.",
        "A diszkrimináció elfogadhatatlan.",
        "A demokrácia a nép uralma.",
        "A jogállamiság a szabadság garanciája.",
        "Az emberi jogok mindenkit megilletnek.",
        "A véleményszabadság alapvető jog.",
        "A sajtószabadság a demokrácia része.",
        "A választások a népakarat kifejezői.",
        "A pártok a politika szereplői.",
        "Az önkormányzatok a helyi ügyeket intézik.",
        "A törvények az együttélés szabályai.",
        "A bíróságok az igazságszolgáltatás fórumai.",
        "A rendőrség a közbiztonságot védi.",
        "A tűzoltók életeket mentenek.",
        "A mentők sürgős segítséget nyújtanak.",
    ],
    "cuisine": [
        "A magyar konyha gazdag és ízletes.",
        "A pirospaprika a magyar ételek lelke.",
        "A gulyás világhírű magyar étel.",
        "A pörkölt sűrű szafttal készül.",
        "A halászlé a folyók ajándéka.",
        "A töltött káposzta ünnepi étel.",
        "A lángos népszerű gyorsételek egyike.",
        "A kürtőskalács édes finomság.",
        "A dobostorta klasszikus desszert.",
        "A somlói galuska krémes csemege.",
        "A túrós csusza egyszerű és finom.",
        "A lecsó nyári zöldségekből készül.",
        "A paprikás csirke tejföllel kiadós.",
        "A főzelékek egészségesek és változatosak.",
        "A magyar bor világhírű.",
        "A pálinka tradicionális ital.",
        "A kenyér a magyar asztal alapja.",
        "A kolbász és szalámi hungarikumok.",
        "A leves minden ebéd kezdete.",
        "A sütemények a kávé mellé valók.",
    ],
    "sports": [
        "A sport egészséget és örömöt ad.",
        "A labdarúgás a legnépszerűbb sportág.",
        "A vízilabda-válogatott világklasszis.",
        "Az úszók rendszeresen szereznek érmeket.",
        "A kajak-kenu olimpiai sikersportág.",
        "A vívás hagyományos magyar erősség.",
        "A torna pontos mozgásokat igényel.",
        "Az atlétika a sport alapja.",
        "A kosárlabda egyre népszerűbb.",
        "A kézilabda dinamikus csapatjáték.",
        "A tenisz egyéni küzdelem.",
        "A kerékpározás egészséges és környezetbarát.",
        "A futás bárhol űzhető.",
        "Az úszás minden izomcsoportot megmozgat.",
        "A síelés téli élmény.",
        "A korcsolyázás szép és nehéz.",
        "A lovaglás hagyományos magyar sport.",
        "Az íjászat a hunok öröksége.",
        "A horgászat nyugodt kikapcsolódás.",
        "A túrázás a természet felfedezése.",
    ],
    "art": [
        "A művészet az emberi lélek tükre.",
        "A festészet színekkel mesél.",
        "A szobrászat formákat teremt.",
        "A grafika vonalakkal beszél.",
        "A fotográfia pillanatokat ragad meg.",
        "A film mozgó képeket alkot.",
        "A zene az érzelmek nyelve.",
        "A tánc a test kifejezőeszköze.",
        "A színház élő előadás.",
        "Az irodalom szavakkal fest.",
        "A költészet a nyelv zenéje.",
        "A próza történeteket mesél.",
        "A dráma konfliktusokat ábrázol.",
        "Az építészet térformáló művészet.",
        "A design a használat és szépség ötvözete.",
        "A divat az öltözködés művészete.",
        "A kerámia ősi kézművesség.",
        "Az ötvösség nemes anyagokkal dolgozik.",
        "A textilművészet szövetekkel alkot.",
        "A népművészet a hagyományok őrzője.",
    ],
    "philosophy": [
        "A filozófia a bölcsesség szeretete.",
        "Az etika a helyes cselekvéssel foglalkozik.",
        "A logika a helyes gondolkodás tudománya.",
        "Az esztétika a szépség kérdéseire keres választ.",
        "Az ismeretelmélet a tudás természetét vizsgálja.",
        "A metafizika a létezés alapkérdéseit kutatja.",
        "A szabadság és a felelősség összefügg.",
        "Az igazság keresése emberi törekvés.",
        "A boldogság a filozófia egyik fő témája.",
        "Az értelmes élet keresése fontos kérdés.",
        "A halál és az élet összefüggnek.",
        "A tudat rejtélyei foglalkoztatják a gondolkodókat.",
        "Az identitás személyes és közösségi kérdés.",
        "Az értékek irányítják a döntéseinket.",
        "A hit és a tudás viszonya összetett.",
        "A nyelv és a gondolkodás kapcsolata mély.",
        "A társas lét az ember természete.",
        "A hatalom etikai kérdéseket vet fel.",
        "Az igazságosság az erkölcs alapja.",
        "A tolerancia a békés együttélés feltétele.",
    ],
    "psychology": [
        "A pszichológia a lélek tudománya.",
        "Az érzelmek az emberi élet részei.",
        "A motiváció a cselekvés hajtóereje.",
        "A tanulás élethosszig tartó folyamat.",
        "Az emlékezet a múlt őrzője.",
        "A figyelem szelektív és korlátozott.",
        "Az észlelés a világ megismerése.",
        "A gondolkodás problémamegoldó tevékenység.",
        "A személyiség egyedi mintázat.",
        "Az intelligencia sokféle formában létezik.",
        "A kreativitás új ötletek forrása.",
        "A stressz a modern élet velejárója.",
        "A szorongás kezelhető állapot.",
        "A depresszió komoly betegség.",
        "A terápia segíthet a problémákon.",
        "Az önismeret a fejlődés alapja.",
        "A kapcsolatok az életminőséget befolyásolják.",
        "A kommunikáció a megértés eszköze.",
        "A konfliktuskezelés tanulható készség.",
        "A boldogság belső állapot.",
    ],
    "law": [
        "A jog a társadalom szabályrendszere.",
        "Az alkotmány az alaptörvény.",
        "A törvények az Országgyűlés alkotásai.",
        "A rendeletek a végrehajtás eszközei.",
        "A bíróságok ítéleteket hoznak.",
        "Az ügyészség vádat emel.",
        "Az ügyvédek a jogokat védik.",
        "A szerződések kötelezettségeket teremtenek.",
        "A tulajdonjog alapvető jog.",
        "Az öröklés a vagyon átszállása.",
        "A büntetőjog a bűncselekményekkel foglalkozik.",
        "A polgári jog a magánjogi viszonyokat szabályozza.",
        "A közigazgatási jog az állam működését rendezi.",
        "A munkajog a munkaviszonyra vonatkozik.",
        "A családjog a családi kapcsolatokat szabályozza.",
        "A nemzetközi jog az államok közötti viszonyokat rendezi.",
        "Az emberi jogok egyetemesen érvényesek.",
        "A jogorvoslat a sérelmek orvoslása.",
        "A jogállamiság a demokrácia alapja.",
        "Az igazságszolgáltatás függetlensége fontos.",
    ],
    "communication": [
        "A kommunikáció az emberi kapcsolatok alapja.",
        "A verbális közlés szavakkal történik.",
        "A nonverbális jelek is információt hordoznak.",
        "A testbeszéd sokat elárul.",
        "A hanglejtés érzelmeket fejez ki.",
        "Az aktív hallgatás empátiát mutat.",
        "A visszakérdezés tisztázza a félreértéseket.",
        "Az asszertív kommunikáció hatékony.",
        "A konfliktusok kommunikációval oldhatók.",
        "A média tömegkommunikációs eszköz.",
        "Az újságok információt közvetítenek.",
        "A televízió vizuális médium.",
        "A rádió hangon keresztül szól.",
        "Az internet az információ forradalma.",
        "A közösségi média összeköt.",
        "Az e-mail hivatalos levelezés.",
        "A videokonferencia távolságokat hidal át.",
        "A prezentáció hatásos bemutatkozás.",
        "A tárgyalás érdekek egyeztetése.",
        "A retorika a meggyőzés művészete.",
    ],
    "daily_life": [
        "A reggeli rutin meghatározza a napot.",
        "A munkába járás időt vesz igénybe.",
        "Az étkezések rendszeressége fontos.",
        "A pihenés feltölti az energiát.",
        "A család közös programjai értékesek.",
        "A barátokkal való találkozás örömet ad.",
        "A háztartási munkák mindennapi feladatok.",
        "A bevásárlás tervezést igényel.",
        "A főzés kreatív tevékenység lehet.",
        "A takarítás a rend alapja.",
        "A kertgondozás kikapcsolódást nyújt.",
        "A háziállatok gondoskodást igényelnek.",
        "A gyereknevelés felelősségteljes feladat.",
        "Az időgazdálkodás kulcsfontosságú.",
        "A pénzkezelés alapvető készség.",
        "A közlekedés mindennapi kihívás.",
        "Az ügyintézés időnként bonyolult.",
        "A szabadidő eltöltése egyéni döntés.",
        "A hobbik gazdagítják az életet.",
        "Az alvás az egészség alapja.",
    ],
    "travel": [
        "Az utazás bővíti a látókört.",
        "A tervezés az utazás első lépése.",
        "A szállás foglalása fontos feladat.",
        "A közlekedés többféleképpen megoldható.",
        "A repülés gyors és kényelmes.",
        "A vonatút romantikus élmény.",
        "Az autós utazás szabadságot ad.",
        "A hajóút különleges kaland.",
        "A csomagolás gyakorlatot igényel.",
        "Az úti okmányok nélkülözhetetlenek.",
        "A biztosítás biztonságot nyújt.",
        "A helyi kultúra megismerése gazdag élmény.",
        "A gasztronómia az utazás része.",
        "A látnivalók előzetes kutatást érdemelnek.",
        "A nyelvtudás megkönnyíti az utazást.",
        "A fotózás megörökíti az emlékeket.",
        "Az ajándékok emlékeket hordoznak.",
        "A hazatérés is az utazás része.",
        "Az élmények örökre megmaradnak.",
        "Az utazás új perspektívákat nyit.",
    ],
    "work": [
        "A munka az élet fontos része.",
        "A karrierépítés tudatos tervezést igényel.",
        "Az önéletrajz az első benyomás.",
        "Az állásinterjú felkészülést követel.",
        "A munkaszerződés kötelezettségeket tartalmaz.",
        "A munkaidő szabályozott.",
        "A fizetés a munka ellenértéke.",
        "A juttatások kiegészítik a bért.",
        "A szabadság a pihenés ideje.",
        "A betegszabadság jár, ha szükséges.",
        "A csapatmunka együttműködést igényel.",
        "A határidők fegyelmezettséget követelnek.",
        "A vezetők felelősséget viselnek.",
        "A beosztottak végrehajtják a feladatokat.",
        "A továbbképzés fejleszti a készségeket.",
        "Az előléptetés elismerés.",
        "A munkahelyi kultúra meghatározó.",
        "A munka és magánélet egyensúlya fontos.",
        "A stressz kezelése szükséges.",
        "A nyugdíj a pálya lezárása.",
    ],
    "relationships": [
        "A kapcsolatok gazdagítják az életet.",
        "A bizalom a kapcsolatok alapja.",
        "A tisztelet kölcsönös kell legyen.",
        "A kommunikáció fenntartja a kapcsolatot.",
        "A kompromisszum néha szükséges.",
        "A konfliktusok természetesek.",
        "A megbocsátás felszabadít.",
        "A szeretet erős kötelék.",
        "A barátság értékes ajándék.",
        "A család az elsődleges közösség.",
        "A házasság elköteleződés.",
        "A szülői szeretet feltétel nélküli.",
        "A testvéri kötelék különleges.",
        "A nagyszülők bölcsességet adnak.",
        "A munkatársi viszonyok fontosak.",
        "A szomszédsági kapcsolatok hasznosak.",
        "A közösségi tagság erőt ad.",
        "A mentor útmutatást nyújt.",
        "Az empátia összeköt.",
        "A magány is része az életnek.",
    ],
    "environment": [
        "A környezetvédelem közös ügy.",
        "A klímaváltozás globális probléma.",
        "A szén-dioxid-kibocsátás csökkentése sürgős.",
        "A megújuló energia a jövő.",
        "A napenergia tiszta forrás.",
        "A szélenergia egyre elterjedtebb.",
        "A geotermikus energia hazánkban bőséges.",
        "A vízerőművek energiát termelnek.",
        "Az energiatakarékosság mindenki feladata.",
        "A szigetelés csökkenti a fogyasztást.",
        "A LED-izzók hatékonyabbak.",
        "A közösségi közlekedés környezetbarát.",
        "A kerékpározás zöld választás.",
        "Az elektromos autók tisztábbak.",
        "Az újrahasznosítás csökkenti a hulladékot.",
        "A komposztálás a szerves anyagok hasznosítása.",
        "A műanyagok csökkentése fontos.",
        "A vízgazdálkodás stratégiai kérdés.",
        "A faültetés a jövőbe való befektetés.",
        "A biodiverzitás megőrzése létfontosságú.",
    ],
    "innovation": [
        "Az innováció a fejlődés motorja.",
        "A kreativitás új ötleteket szül.",
        "A kutatás a tudás bővítése.",
        "A fejlesztés a gyakorlati alkalmazás.",
        "A szabadalmak védik a találmányokat.",
        "A startup kultúra dinamikus.",
        "A kockázati tőke finanszírozást biztosít.",
        "Az inkubátorok támogatják a kezdőket.",
        "Az akcelerátorok felgyorsítják a növekedést.",
        "A mentorok tapasztalatot adnak át.",
        "A hálózatosodás lehetőségeket teremt.",
        "A verseny ösztönzi a fejlődést.",
        "A kudarcból is lehet tanulni.",
        "A kitartás végül meghozza a sikert.",
        "A csapatmunka erősíti az innovációt.",
        "A diverzitás gazdagítja a gondolkodást.",
        "A nyitottság új utakat nyit.",
        "Az agilitás a gyors alkalmazkodás.",
        "A digitalizáció átformálja az iparágakat.",
        "A jövő a technológiai fejlődésé.",
    ],
}

def generate_entry(idx, category, sentences):
    num_sentences = random.randint(2, 5)
    selected = random.sample(sentences, min(num_sentences, len(sentences)))
    text = " ".join(selected)
    
    return {
        "id": f"hu_{idx:05d}",
        "text": text,
        "category": category,
        "quality": "native"
    }

dialogue_starters = [
    "Jó napot kívánok!", "Üdvözlöm!", "Szia!", "Szervusz!", "Jó reggelt!",
    "Jó estét!", "Helló!", "Elnézést...", "Bocsánat...", "Kérem szépen...",
    "Beszélhetnék valakivel?", "Van egy perced?", "Segítene nekem?",
    "Meg tudná mondani...", "Érdeklődnék...", "Volna kedve...",
    "Mi újság?", "Hogy vagy?", "Minden rendben?", "Na, mi a helyzet?",
]

dialogue_contexts = [
    "bolt", "étterem", "orvos", "bank", "posta", "hivatal", "iskola", "munka",
    "utca", "telefon", "vendég", "szomszéd", "barát", "család", "üzlet",
]

dialogue_responses = [
    "Természetesen, szívesen segítek.", "Igen, persze, tessék mondani.",
    "Köszönöm, jól vagyok.", "Rendben, megoldjuk.", "Egy pillanat, máris jövök.",
    "Sajnos nem tudom, de utánanézek.", "Örömmel, miben segíthetek?",
    "Nagyon köszönöm a segítséget.", "Ez remek hír!", "Értem, köszönöm.",
    "Azt hiszem, meg tudjuk oldani.", "Ez egy jó ötlet!", "Egyetértek.",
    "Hadd gondolkozzam rajta.", "Tényleg? Ez érdekes.", "Jó, csináljuk!",
]

dialogue_closings = [
    "Köszönöm szépen!", "Viszontlátásra!", "További szép napot!",
    "Legyen szép napja!", "Köszönöm a segítséget!", "Minden jót!",
    "Vigyázz magadra!", "Hamarosan találkozunk!", "Sok sikert!",
    "Köszönöm, hogy segített!", "Jó munkát!", "Örültem, hogy találkoztunk!",
]

def generate_dialogue_entry(idx, used_texts):
    max_attempts = 50
    for _ in range(max_attempts):
        starter = random.choice(dialogue_starters)
        response = random.choice(dialogue_responses)
        closing = random.choice(dialogue_closings)
        context = random.choice(dialogue_contexts)
        
        if random.random() < 0.5:
            text = f"{starter} - {response} - {closing}"
        else:
            extra = random.choice(dialogue_responses)
            text = f"{starter} - {response} - {extra} - {closing}"
        
        if text not in used_texts:
            used_texts.add(text)
            return {
                "id": f"hu_{idx:05d}",
                "text": text,
                "category": "dialogue",
                "quality": "native"
            }
    return None

qa_pairs = [
    ("Mi a magyar nyelv eredete?", "A magyar nyelv a finnugor nyelvcsalád uráli ágához tartozik, és több mint ezer éves írott emlékekkel rendelkezik."),
    ("Mikor volt a mohácsi csata?", "A mohácsi csata 1526. augusztus 29-én zajlott, és a magyar történelem egyik legjelentősebb ütközete volt."),
    ("Mi a hungarikum?", "A hungarikum olyan magyar termék, tevékenység vagy érték, amely nemzeti kincsnek számít és egyedi magyar sajátosságokkal rendelkezik."),
    ("Ki volt Szent István?", "Szent István az első magyar király volt, aki megalapította a keresztény magyar államot és koronát kapott a pápától 1000-ben."),
    ("Mi a Balaton?", "A Balaton Közép-Európa legnagyobb tava, 594 négyzetkilométeres felületével Magyarország egyik legkedveltebb üdülőhelye."),
    ("Mi a gulyás?", "A gulyás hagyományos magyar leves, amelyet marhahúsból, hagymából, paprikából és krumplival készítenek."),
    ("Ki volt Petőfi Sándor?", "Petőfi Sándor a magyar romantika legnagyobb költője volt, a 1848-49-es forradalom és szabadságharc szimbóluma."),
    ("Mit jelent a fenntartható fejlődés?", "A fenntartható fejlődés olyan fejlődési modell, amely a jelen szükségleteit úgy elégíti ki, hogy nem veszélyezteti a jövő generációk lehetőségeit."),
    ("Hány megye van Magyarországon?", "Magyarországon 19 megye és a főváros, Budapest található, amelyek együtt alkotják az ország közigazgatási felosztását."),
    ("Mi a forint?", "A forint a magyar nemzeti valuta, amelyet 1946-ban vezettek be a pengő helyett és azóta is használják."),
    ("Melyik a legnagyobb magyar város?", "Budapest a legnagyobb magyar város, amely egyben az ország fővárosa is, körülbelül 1,7 millió lakossal."),
    ("Mi az Országház?", "Az Országház a magyar parlament épülete a Duna partján, amely 1904-ben készült el és Európa egyik legnagyobb parlamentje."),
    ("Hol található a Hortobágy?", "A Hortobágy Magyarország keleti részén található, Közép-Európa legnagyobb füves pusztája és UNESCO világörökségi helyszín."),
    ("Mi a tokaji bor?", "A tokaji bor világhírű magyar édesbor a Tokaji borvidékről, amelyet már a 17. században is a 'borok királyának' neveztek."),
    ("Ki volt Arany János?", "Arany János a XIX. század nagy epikus költője volt, a magyar balladaírás mestere és a Toldi trilógia szerzője."),
    ("Mikor ünnepeljük március 15-ét?", "Március 15-e az 1848-as forradalom és szabadságharc emléknapja, a magyar nemzeti ünnepek egyike."),
    ("Mi a Tisza?", "A Tisza Magyarország második legnagyobb és leghosszabb folyója, amely az ország keleti részén folyik keresztül."),
    ("Mikor alapították Budapestet?", "Budapest 1873-ban jött létre Pest, Buda és Óbuda egyesítésével, bár a terület története több ezer évre nyúlik vissza."),
    ("Mi a pálinka?", "A pálinka hagyományos magyar gyümölcspárlat, amelyet különböző gyümölcsökből, például szilvából, barackból vagy körtéből készítenek."),
    ("Hány lakosú Magyarország?", "Magyarország lakossága körülbelül 9,7 millió fő, amely az elmúlt évtizedekben fokozatosan csökken."),
    ("Mi a Rubik-kocka?", "A Rubik-kocka Rubik Ernő magyar feltaláló 1974-ben készített háromdimenziós logikai játéka, amely világszerte ismertté vált."),
    ("Ki volt Liszt Ferenc?", "Liszt Ferenc világhírű zeneszerző és zongorista volt, a 19. század egyik legkiemelkedőbb romantikus muzsikusa."),
    ("Mi a paprika?", "A paprika a magyar konyha alapvető fűszere, amelyet a 16. században hoztak be az országba és azóta a nemzeti konyha szimbóluma."),
    ("Hol van a Mátra?", "A Mátra Magyarország legmagasabb hegysége az ország északi részén, legmagasabb pontja a Kékestető 1014 méterrel."),
    ("Mi a csárdás?", "A csárdás a legismertebb magyar néptánc, amely a 19. században alakult ki és a magyar zene és kultúra jelképévé vált."),
    ("Ki volt Kossuth Lajos?", "Kossuth Lajos a 1848-49-es szabadságharc vezéralakja volt, politikus és az egyik legjelentősebb magyar államférfi."),
    ("Mi a kürtőskalács?", "A kürtőskalács hagyományos erdélyi magyar sütemény, amelyet fa köré tekert tésztából sütnek és cukorral borítanak."),
    ("Hol található Pécs?", "Pécs Baranya megye székhelye Dél-Magyarországon, gazdag kulturális örökséggel és 2010-ben Európa Kulturális Fővárosa volt."),
    ("Mi a magyar himnusz?", "A magyar himnuszt Kölcsey Ferenc írta 1823-ban, Erkel Ferenc zenésítette meg, és 1844 óta a nemzeti himnusz."),
    ("Ki írta az Egri csillagokat?", "Az Egri csillagokat Gárdonyi Géza írta 1899-ben, amely az egri vár 1552-es török ostromáról szól."),
    ("Mi a pörkölt?", "A pörkölt hagyományos magyar húsétel, amelyet hagymás-paprikás szaftban párolt húsból készítenek."),
    ("Ki volt Bartók Béla?", "Bartók Béla a 20. század egyik legjelentősebb zeneszerzője és zenetudósa volt, a magyar népzene kutatója."),
    ("Mi a Duna?", "A Duna Európa második leghosszabb folyója, amely Magyarországot észak-déli irányban szeli át 417 kilométeren."),
    ("Hol van Szeged?", "Szeged Csongrád-Csanád megye székhelye a Tisza partján, Magyarország harmadik legnagyobb városa."),
    ("Mi a halászlé?", "A halászlé hagyományos magyar halétel, amelyet különböző édesvízi halakból és paprikából készítenek."),
    ("Ki volt Kodály Zoltán?", "Kodály Zoltán zeneszerző és zenetudós volt, aki a magyar zenepedagógia megújítója és a népzene gyűjtője."),
    ("Mi a Hősök tere?", "A Hősök tere Budapest egyik legnagyobb és legjelentősebb tere, amelyen a Millenniumi emlékmű áll."),
    ("Mikor volt a honfoglalás?", "A magyar honfoglalás 895-896 körül zajlott, amikor a magyarok a Kárpát-medencébe érkeztek."),
    ("Mi a lángos?", "A lángos hagyományos magyar sült tészta, amelyet általában tejföllel és sajttal tálalnak."),
    ("Ki volt Jókai Mór?", "Jókai Mór a 19. század legnépszerűbb magyar regényírója volt, több mint 100 regényt és elbeszélést írt."),
    ("Mi a Margit-sziget?", "A Margit-sziget Budapest szívében, a Dunán található park és rekreációs terület."),
    ("Hol van Debrecen?", "Debrecen Hajdú-Bihar megye székhelye, Magyarország második legnagyobb városa a Tiszántúlon."),
    ("Mi a töltött káposzta?", "A töltött káposzta hagyományos magyar téli étel, savanyú káposztába töltött húsos rizzsel."),
    ("Ki volt Ady Endre?", "Ady Endre a 20. század eleji magyar irodalom megújítója volt, a modern magyar líra egyik legnagyobb alakja."),
    ("Mi a Fisherman's Bastion?", "A Halászbástya Budapest egyik leghíresebb turisztikai látványossága a Várban, neoromán stílusban épült."),
    ("Mikor volt a kiegyezés?", "Az osztrák-magyar kiegyezés 1867-ben jött létre, amely megalapozta az Osztrák-Magyar Monarchiát."),
    ("Mi a dobos torta?", "A dobos torta hagyományos magyar sütemény, amelyet Dobos C. József cukrász alkotott meg 1884-ben."),
    ("Ki volt Semmelweis Ignác?", "Semmelweis Ignác magyar orvos volt, aki felfedezte a kézmosás fontosságát a fertőzések megelőzésében."),
    ("Mi a Váci utca?", "A Váci utca Budapest egyik leghíresebb sétálóutcája a belvárosban, népszerű bevásárló- és turistaövezet."),
    ("Hol van Győr?", "Győr Győr-Moson-Sopron megye székhelye Északnyugat-Magyarországon, a Mosoni-Duna partján."),
]

def generate_question_answer(idx, used_texts):
    max_attempts = 50
    for _ in range(max_attempts):
        qa = random.choice(qa_pairs)
        text = f"Kérdés: {qa[0]} Válasz: {qa[1]}"
        
        if text not in used_texts:
            used_texts.add(text)
            return {
                "id": f"hu_{idx:05d}",
                "text": text,
                "category": "qa",
                "quality": "native"
            }
    return None

instruction_pairs = [
    ("Foglald össze a magyar történelem legfontosabb eseményeit.", "A magyar történelem kulcseseményei közé tartozik a 896-os honfoglalás, az 1000-es államalapítás, az 1526-os mohácsi vész, az 1848-49-es szabadságharc, a trianoni békeszerződés és az 1956-os forradalom."),
    ("Írj esszét a magyar nyelv tulajdonságairól.", "A magyar nyelv agglutináló szerkezete egyedülálló Európában. A szavakhoz számos toldalékot illeszthetünk, ami rendkívül pontos és árnyalt kifejezéseket tesz lehetővé. A magánhangzó-harmónia és a birtokos személyragok különleges jellemzői."),
    ("Magyarázd el a fenntartható fejlődés fogalmát.", "A fenntartható fejlődés olyan modell, amely egyensúlyt teremt a gazdasági növekedés, a társadalmi fejlődés és a környezetvédelem között, biztosítva, hogy a jelen szükségletei ne veszélyeztessék a jövő generációk lehetőségeit."),
    ("Sorold fel a magyar konyha legismertebb ételeit.", "A magyar konyha legismertebb ételei a gulyás, pörkölt, halászlé, töltött káposzta, lángos, kürtőskalács, dobos torta és somlói galuska. A paprika központi szerepet játszik a legtöbb hagyományos ételben."),
    ("Ismerteted a magyar oktatási rendszer felépítését.", "A magyar oktatási rendszer háromszintű: alapfokú oktatás (általános iskola, 6-14 év), középfokú oktatás (gimnázium, szakközépiskola, szakiskola), és felsőfokú oktatás (egyetemek, főiskolák). Az óvoda 3-6 éves korig tart."),
    ("Elemezd a digitális technológiák hatását.", "A digitális technológiák alapvetően megváltoztatták az életünket. A kommunikáció, munka, oktatás és szórakozás új formái jelentek meg. Az internet és okostelefonok mindennapossá váltak, míg a mesterséges intelligencia egyre több területen jelenik meg."),
    ("Mutasd be a magyar irodalom kiemelkedő alakjait.", "A magyar irodalom kiemelkedő alakjai Petőfi Sándor, Arany János, Jókai Mór, Ady Endre, Babits Mihály, Kosztolányi Dezső, József Attila és Márai Sándor. Műveik a világirodalom értékei közé tartoznak."),
    ("Írd le a Balaton természeti adottságait.", "A Balaton 594 négyzetkilométeres felületével Közép-Európa legnagyobb tava. Északi partja mélyebb, hegyesebb és szőlőtermesztésre alkalmas, míg a déli part sekély, homokos és családbarát. A tó átlagos mélysége 3-4 méter."),
    ("Magyarázd el az egészséges életmód alapelveit.", "Az egészséges életmód négy pillére a kiegyensúlyozott táplálkozás, a rendszeres testmozgás, az elegendő alvás és a stresszkezelés. Fontos a zöldség-gyümölcs fogyasztás, napi 30 perc mozgás, 7-8 óra alvás és relaxációs technikák."),
    ("Foglald össze a klímaváltozás következményeit.", "A klímaváltozás következményei közé tartozik a globális felmelegedés, szélsőséges időjárási jelenségek, tengerszint-emelkedés, jégsapkák olvadása, biodiverzitás csökkenése és mezőgazdasági terméskiesés. Magyarországon az aszályok és árvizek gyakoribbak."),
    ("Készíts összefoglalót a magyar zenéről.", "A magyar zene Bartók Bélától és Kodály Zoltántól Liszt Ferencig világszínvonalú. A népzene gazdag hagyományai mellett a verbunkos, csárdás és operett is jellemző. A kortárs zenében a magyar zeneszerzők nemzetközileg elismertek."),
    ("Elemezd a globalizáció hatásait.", "A globalizáció összekapcsolja a kultúrákat és gazdaságokat. Előnyei a technológia terjedése, gazdasági növekedés és kulturális csere. Hátrányai a helyi kultúrák veszélyeztetése, gazdasági egyenlőtlenségek és környezeti problémák."),
    ("Ismerteted a magyar néphagyományokat.", "A magyar néphagyományok gazdag szellemi örökséget jelentenek. A népművészet területén a hímzés, fazekasság és fafaragás kiemelkedő. A népdalok, néptáncok és népmesék generációkon át öröklődtek. A kalendáriumi ünnepek és szokások ma is élnek."),
    ("Magyarázd el a demokrácia működését.", "A demokrácia a népakarat és jogállamiság rendszere. Alapelvei a szabad választások, hatalommegosztás, emberi jogok védelme és törvény előtti egyenlőség. Magyarországon parlamenti demokrácia működik, ahol a képviselőket négyévente választják."),
    ("Írj a magyar természetvédelemről.", "Magyarország természetvédelmi területei nemzeti kincsek. Tíz nemzeti park, köztük a Hortobágy és a Kiskunság, védett tájak és természetvédelmi területek alkotják a védett területek hálózatát. A Natura 2000 területek az EU részeként működnek."),
    ("Mutasd be a magyar sportkultúrát.", "A magyar sport számos olimpiai bajnokot adott a világnak. Kiemelkedő sportágak a vívás, vízilabda, úszás, kajak-kenu és öttusa. Puskás Ferenc a világ futballtörténetének legendája. Magyarország 2024-ig 511 olimpiai érmet nyert."),
    ("Elemezd a városiasodás trendjeit.", "A városiasodás új kihívásokat és lehetőségeket teremt. Magyarországon a lakosság 70%-a városokban él. Budapest túlsúlya jellemző, míg a vidéki városok fejlesztése prioritás. A fenntartható városfejlesztés és okos város megoldások terjednek."),
    ("Foglald össze a magyar gazdaság jellemzőit.", "A magyar gazdaság nyitott és exportorientált. Az EU tagjaként az egységes piac része. Főbb iparágak az autógyártás, elektronika, gyógyszeripar és élelmiszergazdaság. A GDP körülbelül 180 milliárd euró, a munkanélküliség 4% körüli."),
    ("Ismerteted a magyar művészeti irányzatokat.", "A magyar művészet a népi és modern elemeket ötvözi. A történeti stílusok közül a gótika, barokk és szecesszió kiemelkedő. A nagybányai festőiskola, a Nyolcak és az avantgárd mozgalmak formálták a modern magyar művészetet."),
    ("Magyarázd el a társadalmi egyenlőség fontosságát.", "A társadalmi egyenlőség a fejlődés alapja. Az egyenlő esélyek biztosítása az oktatásban, munkaerőpiacon és egészségügyben kulcsfontosságú. A diszkrimináció elleni küzdelem és a marginalizált csoportok támogatása prioritás a modern társadalmakban."),
    ("Írj a magyar innováció sikereiről.", "A magyar innováció a Rubik-kockától a golyóstollig terjed. Magyar feltalálók alkották meg a C-vitamint (Szent-Györgyi), a holográfiát (Gábor Dénes) és a BASIC nyelvet (Kemény János). Ma a startupok és IT szektor dinamikusan fejlődik."),
    ("Mutasd be a magyar tudomány eredményeit.", "A magyar tudósok Nobel-díjakkal járultak hozzá a haladáshoz. 13 magyar származású tudós kapott Nobel-díjat. Szent-Györgyi Albert, Wigner Jenő, Harsányi János és mások világszerte elismert felfedezéseket tettek a fizika, kémia és közgazdaságtan területén."),
    ("Elemezd a hagyomány és modernizáció viszonyát.", "A hagyomány és modernizáció harmonikusan létezhet együtt. A kulturális örökség megőrzése mellett a technológiai fejlődés és társadalmi változások befogadása fontos. Magyarország példa arra, hogyan ötvözhető a népi kultúra a modern életstílussal."),
    ("Foglald össze az egészségügy kihívásait.", "Az egészségügy folyamatos fejlesztést igényel. Fő kihívások az elöregedő társadalom, orvoshiány, várólisták és finanszírozási problémák. A megelőzés, alapellátás erősítése és digitalizáció a fejlesztés irányai. Az EU források segítenek a korszerűsítésben."),
    ("Ismerteted a magyar építészet stílusait.", "A magyar építészet a román kortól a szecesszióig ível. Kiemelkedő emlékek a jáki templom (román), Mátyás-templom (gótikus), az egri Lyceum (barokk) és a Szépművészeti Múzeum (neoklasszikus). Lechner Ödön szecessziós épületei világhírűek."),
]

def generate_instruction(idx, used_texts):
    max_attempts = 50
    for _ in range(max_attempts):
        pair = random.choice(instruction_pairs)
        text = f"Feladat: {pair[0]} Válasz: {pair[1]}"
        
        if text not in used_texts:
            used_texts.add(text)
            return {
                "id": f"hu_{idx:05d}",
                "text": text,
                "category": "instruction",
                "quality": "native"
            }
    return None

def main():
    os.makedirs("data", exist_ok=True)
    
    entries = []
    used_texts = set()
    idx = 1
    
    categories = list(sentences_by_category.keys())
    
    for _ in range(7000):
        category = random.choice(categories)
        sentences = sentences_by_category[category]
        entry = generate_entry(idx, category, sentences)
        if entry["text"] not in used_texts:
            used_texts.add(entry["text"])
            entries.append(entry)
            idx += 1
    
    for _ in range(1000):
        entry = generate_dialogue_entry(idx, used_texts)
        if entry:
            entries.append(entry)
            idx += 1
    
    for _ in range(1000):
        entry = generate_question_answer(idx, used_texts)
        if entry:
            entries.append(entry)
            idx += 1
    
    for _ in range(1000):
        entry = generate_instruction(idx, used_texts)
        if entry:
            entries.append(entry)
            idx += 1
    
    random.shuffle(entries)
    
    with open("data/hungarian_pretrain_dataset.jsonl", "w", encoding="utf-8") as f:
        for entry in entries:
            f.write(json.dumps(entry, ensure_ascii=False) + "\n")
    
    print(f"Generated {len(entries)} entries in data/hungarian_pretrain_dataset.jsonl")
    
    stats = {}
    for entry in entries:
        cat = entry["category"]
        stats[cat] = stats.get(cat, 0) + 1
    
    print("\nCategory distribution:")
    for cat, count in sorted(stats.items(), key=lambda x: -x[1]):
        print(f"  {cat}: {count}")

if __name__ == "__main__":
    main()
