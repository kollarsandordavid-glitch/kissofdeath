Áttekintés

A nsir_core tárház biztosítja az alapvető adatszerkezeteket és formális specifikációkat az NSIR (Nem-lineáris Önismétlő Információ Ábrázolás) számára. Az NSIR az elsődleges adatarchitektúraként szolgál a Kognitív Relációs Motor (CRE) számára a Jaide LLM projekten belül.

A projekt összeköti a klasszikus gráfelméletet a kvantummechanikai tulajdonságokkal, hogy az információt nem-lineáris, önismétlő formátumban ábrázolja. Ez a megvalósítás egyedülálló a kettős nyelvi stratégiájában: nagy teljesítményű futásidejű implementációt biztosít Zig nyelven és matematikailag rigorózus formális specifikációt Lean 4 nyelven.

Az NSIR Koncepció

Az NSIR adatot ábrázol mint Önismétlő Relációs Gráf. A hagyományos gráfokkal ellentétben az NSIR csomópontok és élek kvantumállapotokkal és tulajdonságokkal rendelkeznek.

Csomópontok: Qubit állapotot tartalmaznak (komplex amplitúdók a és b), egy fázist és metaadatokat.

Élek: EdgeQuality által definiáltak (például szuperpozíció, összefonódott, fraktál) és egy kvantum_korreláció értékkel rendelkeznek.

Összefonódás: A gráf nyomon követi a több csomópontos korrelációkat TwoQubit Bell állapotok használatával.

Megvalósítási Stratégia

A tárház két különböző nyelvet használ különböző mérnöki követelmények kielégítésére.

1. Zig (nsir_core.zig): A teljesítményre, manuális memóriakezelésre az Allocator segítségével, és a gépi tanulási tenzorokkal (core_tensor) való integrációra fókuszál. Megvalósítja az updateTopologyHash függvényt SHA-256 használatával az állapot integritás érdekében.

2. Lean 4 (nsir.lean, nsir_modulation.lean): Formális specifikációt biztosít. Egyedi implementációkat tartalmaz komplex aritmetikára, SHA-256-ra és fixpontos matematikára, hogy bizonyítsa az NSIR modulációs pipeline helyességét.

Rendszer Architektúra

Az NSIR gráf több mint egy egyszerű szomszédsági lista. Fenntart egy kvantum regisztert és egy kriptográfiai kivonatot a teljes topológiájáról.

Gráf Konténer: SelfSimilarRelationalGraph - Kezeli a csomópontokat, éleket és kvantumállapotokat.

Kvantum Állapot: Qubit - Tárolja a komplex amplitúdókat és kiszámítja a mérési valószínűségeket.

Integritás: topology_hash - Egy 64 karakteres hexadecimális karakterlánc, amely az összes gráf komponens XOR-összegét képviseli.

Moduláció: nsirForward - Fixpontos skálázást alkalmaz az információra a gráf állapota alapján.

Projekt Célja és Kontextusa

Az NSIR (Nem-lineáris Önismétlő Információ Ábrázolás) core az alapvető adatszerkezet és építészeti keretrendszer a Kognitív Relációs Motor (CRE) számára a Jaide LLM projekten belül. Ez eltérést jelent a hagyományos lineáris vektor beágyazásoktól egy önismétlő, gráf alapú ábrázolás felhasználásával, amely kvantummechanikai tulajdonságokat integrál az információ kapcsolatok modellezésére.

Cél és Hatókör

A nsir_core elsődleges célja egy nagy teljesítményű, formálisan ellenőrzött implementációt biztosítani az NSIR gráf számára. A szabványos tudásgráfokkal ellentétben az NSIR integrálja a kvantumállapotokat (Qubiteket) a csomópontokba és modellezi a kapcsolatokat komplex korrelációkon és összefonódáson keresztül. Ez lehetővé teszi a CRE számára a bizonytalanság, a jelentések szuperpozíciójának és a nem-lineáris asszociációknak a képviselését, amelyek gyakran elvesznek a lapos építészeti mintákban.

A projekt kettős nyelvi stratégiát követ.

1. Zig (nsir_core.zig): Biztosítja a nagy teljesítményű futásidejű implementációt, memóriakezelést és integrációt külső tenzor könyvtárakkal.

2. Lean 4 (nsir.lean, nsir_modulation.lean): Biztosítja a formális specifikációt és matematikai bizonyításokat a helyességről a gráf műveletekre és a modulációs pipeline-ra.

Az NSIR Koncepció: Gráfelmélet Találkozik a Kvantummechanikával

Az NSIR keretrendszer összeköti a klasszikus gráfelméletet a kvantummechanikai tulajdonságokkal, hogy létrehozzon egy Önismétlő Relációs Gráfot. Ebben a modellben az információ nem csupán egy statikus pont a térben, hanem egy dinamikus állapot, amely kvázi-szerű műveleteknek van kitéve.

Kulcs Tervezési Filozófiák

Nem-linearitás: A kapcsolatok (Élek) súlyok, fraktál dimenziók és kvantum korrelációk által vezéreltek, lehetővé téve a komplex, többdimenziós bejárást.

Önismétlés: A gráf szerkezet úgy van tervezve, hogy megőrizze a strukturális integritást az információ sűrűség különböző skáláin.

Kvantum Állapot Integráció: Minden csomópont rendelkezik egy Qubit állapottal, amely képviseli az információ összeomlásának valószínűségét következtetés vagy mérés során.

Alapvető Szerep a Kognitív Relációs Motorban (CRE)

Az NSIR gráf szolgál mint a memória és a következtetés aljzat a CRE számára. Kezeli az átmenetet a nyers szövegtől a strukturált, kvázi-korrelált ábrázolásokig.

Információ Életciklus

1. Kódolás: Az encodeInformation függvény átalakítja a nyers adatokat Node entitásokká, automatikusan létrehozva koherens éleket a meglévő csomópontokhoz topológiai közelség alapján.

2. Moduláció: Az nsir_modulation pipeline fixpontos aritmetikát alkalmaz a skálázáshoz és az aktivációk beállításához a gráf állapota alapján.

3. Mérés: A measure függvény összeomlasztja a kvantum szuperpozíciókat diszkrét állapotokká, szimulálva egy döntést vagy felismerési eseményt az LLM-en belül.

Tervezési Filozófia: Determinizmus és Ellenőrzés

Az NSIR projekt kritikus aspektusa a determinisztikus állapot követelmény és a formális ellenőrzés.

Topológia Integritás

A gráf minden módosítása (csomópontok hozzáadása, élek eltávolítása vagy kvantumállapotok megváltoztatása) kiváltja az updateTopologyHash függvényt. Ez a függvény XOR-alapú akkumulációt használ SHA-256 kivonatokból, hogy biztosítsa, hogy a gráf állapota mindig képviselhető legyen egy egyedi 64 karakteres hexadecimális karakterláncként, függetlenül attól, hogy milyen sorrendben adták hozzá a csomópontokat.

Matematikai Szigorúság

A Lean 4 implementáció biztosítja, hogy a komplex aritmetika és a kvantum kapu műveletek követik a lineáris algebra törvényeit. Például a Complex struktúra Lean-ben bizonyítékokat szolgáltat a nagyság számításokra és normalizálásra, amelyekre a Zig futásidejű környezet támaszkodik.

Tárház Szerkezet és Nyelvi Stratégia

Ez az oldal leírja a nsir_core tárház strukturális szervezetét és a stratégiai indoklást a Zig és Lean 4 együttes használatára. A tárház implementálja a Nem-lineáris Önismétlő Információ Ábrázolást (NSIR), amely az alapvető adatszerkezetként szolgál a Kognitív Relációs Motor (CRE) számára a Jaide LLM projekten belül.

Tárház Fájlok

A tárház négy elsődleges fájlból áll, amelyek mindegyike különálló szerepet tölt be az NSIR gráf rendszer fejlesztésében, ellenőrzésében és telepítésében.

README.md - Markdown - Kanonikus specifikáció és dokumentáció

nsir_core.zig - Zig - Nagy teljesítményű futásidejű implementáció és rendszer integráció

nsir.lean - Lean 4 - A gráf és kvantumállapot logika formális specifikációja

nsir_modulation.lean - Lean 4 - Az ML képzési modulációs pipeline formális specifikációja

Kettős Nyelvi Stratégia

A projekt kettős nyelvi stratégiát alkalmaz, hogy egyensúlyba hozza a versengő követelményeket a nagy teljesítményű végrehajtás és a formális helyesség között.

1. Zig: A Teljesítmény Futásidejű Környezet

A Zig-et használják a SelfSimilarRelationalGraph produkciós implementációjára. Manuális memóriakezelést biztosít a std.mem.Allocator segítségével, amely kritikus fontosságú a nagy méretű gráf szerkezetek hatékony kezeléséhez. A Zig implementáció közvetlenül integrálódik külső modulokkal, mint a core_tensor és core_memory. Kezeli a nehéz feladatokat.

Memória Tulajdonjog: A StringHashMap kezelése a csomópontokhoz és a komplex EdgeMap struktúrákhoz.

Kriptográfiai Kivonatolás: Az XOR-alapú updateTopologyHash implementálása SHA-256 használatával.

Kvantum Műveletek: Kapuk végrehajtása, mint a hadamardGate és a measure() műveletek végrehajtása.

2. Lean 4: A Formális Specifikáció

A Lean 4 matematikai alapot biztosít, amely biztosítja, hogy az NSIR logika helyes. Míg a Zig kód sebességre van optimalizálva, addig a Lean kód bizonyíthatóságra van optimalizálva.

Algebrai Ellenőrzés: A Lean-t használják a Complex aritmetika tulajdonságainak és az EdgeQuality átmenetek bizonyítására.

Funkcionális Integritás: Funkcionális struktúrák, mint az asszociációs listák (StringMap-ként modellezve) használatával a Lean biztosítja, hogy a gráf műveletek, mint az addNode vagy addEdge, fenntartsák a belső invariánsokat, amelyeket nehezebb bizonyítani egy imperatív környezetben.

Numerikus Biztonság: Az nsir_modulation.lean fájl egy fixpontos aritmetikai rendszert (FP) definiál, hogy bizonyítsa, hogy a modulációs tényezők nem okoznak túlcsordulást a képzési pipeline során.

Nyelv Interoperabilitás és Invariánsok

A két nyelv közötti kapcsolatot a következő elvek szabályozzák.

1. Bit-Szintű Megfelelés: Az EdgeQuality enum Zig-ben pontosan megfelel az EdgeQuality induktív típusnak Lean-ben. Mindkettő ugyanazt az egész szám leképezést használja (0: szuperpozíció, 1: összefonódott, stb.).

2. Kvantum Állapot Normalizálás: Mindkét implementáció kikényszeríti, hogy egy Qubit-nek normalizáltnak kell lennie. A Zig a normalizeInPlace-t használja, míg a Lean tételeket definiál a magnitudeSquared-ra vonatkozóan, hogy biztosítsa, hogy az állapot az egység gömbön maradjon.

3. Kivonat Integritás: Az updateTopologyHash függvény mindkét implementációban biztosítja az állapot konzisztenciáját.

Alapvető Adatszerkezetek

Ez az oldal áttekintést nyújt azokról az alapvető adattípusokról, amelyek a Nem-lineáris Önismétlő Információ Ábrázolás (NSIR) gerincét képezik. Ezek a struktúrák közösek mind a Zig futásidejű implementációban, mind a Lean 4 formális specifikációban, biztosítva, hogy a bizonyításokban definiált matematikai tulajdonságok megmaradjanak a végrehajtható kódban.

A rendszer információt ábrázol gráfként, ahol a csomópontok kvantumállapotokkal rendelkeznek, és az élek a kapcsolati összeköttetések különböző minőségeit képviselik, a klasszikus súlyoktól a kvantum összefonódásig.

Kvantum Állapot Típusok: Qubit és TwoQubit

A Qubit az információ atomi egysége az NSIR-ben. Egy klasszikus bittel ellentétben két komplex amplitúdóval van definiálva, a és b, amelyek képviselik annak valószínűségét, hogy az állapot 0 vagy 1 legyen.

Qubit: Két komplex számot tartalmaz. Logikát tartalmaz a normalizálásra, hogy biztosítsa, hogy |a|^2 + |b|^2 = 1.0. A Zig implementációban kezeli a szélsőséges eseteket, mint a NaN vagy Inf, azzal, hogy egy bázisállapotra áll vissza.

TwoQubit: Két csomópont közötti összefonódott állapotok (Bell állapotok) képviselésére használják, négy komplex amplitúdóból áll (amp00, amp01, amp10, amp11).

Csomópont és Él Struktúrák

A gráf Node és Edge objektumokból áll. Ezek a struktúrák kombinálják a klasszikus adattárolást a fent említett kvantum tulajdonságokkal.

Node: Egy entitást képvisel. Egyedi id-t, data hasznos terhet, qubit állapotot, phase értéket és egy metadata térképet tartalmaz kiterjeszthető attribútumokhoz.

Edge: Két csomópont, a source és target közötti kapcsolatot képvisel. Nyomon követi az EdgeQuality-t, egy weight-et, quantum_correlation-t és fractal_dimension-t.

EdgeQuality Enum

Az EdgeQuality típus definiálja a két csomópont közötti kapcsolat természetét. Ez egy kritikus komponens a Kognitív Relációs Motor (CRE) számára, hogy megértse, hogyan van összekapcsolva az információ.

Variánsok és Szemantikai Jelentés:

superposition - A kapcsolat több potenciális állapotban létezik egyszerre.

entangled - A csomópontok nem-lokális kvantum korrelációt osztanak meg.

coherent - Stabil, fázis-igazított kapcsolat.

collapsed - Egy mérés utáni klasszikus állapot.

fractal - Önismétlő rekurzív kapcsolat.

A Lean 4 implementáció formális bizonyítékokat szolgáltat ezeknek a konstruktoroknak a különbözőségére.

SelfSimilarRelationalGraph Konténer

A SelfSimilarRelationalGraph az elsődleges konténerként szolgál az egész rendszer számára. Kezeli a csomópontok és élek életciklusát, fenntartja a kvantum regisztert, és biztosítja a felületet a gráf-szintű műveletekhez, mint a topológia kivonatolás.

Zig Implementáció: Teljesítményre és memóriabiztonságra optimalizálva explicit Allocator kezeléssel.

Lean 4 Specifikáció: Funkcionális struktúraként definiálva a gráf invariánsok formális ellenőrzésére.

Kvantum Állapot Típusok: Qubit és TwoQubit

Ez az oldal részletes technikai hivatkozást nyújt az NSIR core-on belül használt kvantumállapot ábrázolásokhoz. Kiterjed az egyedi qubit állapotra, amelyet az egyes csomópontokhoz használnak, és a két-qubit Bell állapotokra, amelyeket a csomópontok közötti összefonódás képviselésére használnak. Az implementáció szét van választva egy nagy teljesítményű futásidejű környezet között Zig-ben és egy formális specifikáció között Lean 4-ben.

Qubit Struktúra

A Qubit a kvázi információ alapvető egysége, amely egy Node-hoz van társítva az NSIR gráfban. Egy kétdimenziós Hilbert-térben lévő állapotot képvisel két komplex amplitúdó használatával, amelyeket gyakran így jelölnek: |ψ⟩ = a|0⟩ + b|1⟩.

Implementációs Részletek

A Zig implementációban a Qubit egy csomagolt struktúra, amely dupla pontosságú komplex számokat használ. A Lean 4 implementáció ezt tükrözi egy egyedi Complex struktúra használatával, hogy elősegítse a normalizálás és kapu alkalmazás formális bizonyításait.

Tulajdonságok:

a - Complex(f64) / Complex - Valószínűségi amplitúdó a |0⟩ állapothoz

b - Complex(f64) / Complex - Valószínűségi amplitúdó a |1⟩ állapothoz

Normalizálás és Biztonság

Egy érvényes kvantumállapotnak meg kell felelnie a normalizálási feltételnek: |a|^2 + |b|^2 = 1. A rendszer ezt kikényszeríti a normalizeInPlace segítségével.

Normalizálási Logika: A négyzetes normát mindkét komplex amplitúdó nagyságának összegeként számítják ki.

Szélsőséges Eset Kezelés: Ha a négyzetes norma nulla, NaN vagy Végtelen, a rendszer visszaállítja a qubitet a stabil initBasis0 (|0⟩) állapotra, hogy megakadályozza a numerikus instabilitást.

Valószínűség Számítás: A prob0() és prob1() függvények valós értékű valószínűségeket adnak vissza, |a|^2 és |b|^2, 0.0 és 1.0 közé szorítva.

Inicializálási Módszerek

init(a, b) - Normalizált állapot az amplitúdókból

initBasis0() - |0⟩ (amplitúdók: a=1, b=0)

initBasis1() - |1⟩ (amplitúdók: a=0, b=1)

TwoQubit és Bell Állapotok

A TwoQubit struktúra két összefonódott csomópont közös állapotát képviseli. Az NSIR-ben az összefonódást négy komplex amplitúdóval modellezik, amelyek a |00⟩, |01⟩, |10⟩, |11⟩ bázis állapotoknak felelnek meg.

Bell Állapot Inicializálás

A rendszer kifejezetten biztosít egy konstruktort a Φ+ Bell állapothoz, amely egy maximálisan összefonódott állapot: Φ+ = (1/√2)(|00⟩ + |11⟩)

Lean 4-ben ezt a TwoQubit névtérben definiálják. Ezt az állapotot általában a csomópontokhoz rendelik, amikor egy összefonódási műveletet hajtanak végre, összekapcsolva azok valószínűségi kimeneteleit.

Komplex Aritmetika Támogatás

Mindkét implementáció komplex szám aritmetikára támaszkodik az állapot manipulációhoz. A Lean 4 implementáció nem kiszámítható specifikációt biztosít ezekre a műveletekre, hogy támogassa a kvantum kapu unitaritás formális ellenőrzését.

Összeadás/Kivonás: Komponensenként a valós (re) és imaginárius (im) részeken.

Szorzás: Implementálja (ac - bd) + i(ad + bc)

Nagyság Négyzete: re^2 + im^2, valószínűséghez és normalizáláshoz használva.

Csomópont és Él Struktúrák

Ez az oldal részletes technikai hivatkozást nyújt az NSIR (Nem-lineáris Önismétlő Információ Ábrázolás) gráf alapvető entitásaihoz: a Node-hoz és az Edge-hez. Ezek a struktúrák elősegítik a klasszikus gráf adatok integrációját a kvantummechanikai tulajdonságokkal és az önismétlő (fraktál) metrikákkal.

Node Struktúra

Egy Node egy diszkrét információs egységet képvisel a relációs gráfon belül. Kapszulázza a klasszikus adatokat, egy kvantumállapotot (qubit) és relációs metaadatokat.

Zig Implementáció (Futásidejű)

A nsir_core.zig-ben a Node egy heap-en allokált struktúra, amely kezeli a saját memóriáját a változó hosszúságú mezőkhöz.

Mezők:

id - []u8 - Egyedi azonosító. A memóriát a node birtokolja a dupeBytes segítségével.

data - []u8 - A node elsődleges tartalma vagy hasznos terhe.

qubit - Qubit - A helyi kvantumállapot (amplitúdók α és β).

phase - f64 - Egy fázis tényező, amelyet az interferencia számításokhoz használnak.

metadata - StringHashMap([]u8) - Egy asszociációs térkép tetszőleges kulcs-érték párokhoz.

allocator - Allocator - Hivatkozás az allokátorra, amelyet a memória életciklus kezeléshez használnak.

Memória Tulajdonjog: A Node a dupeBytes-t használja inicializálás során, hogy privát másolatokat készítsen az id és data karakterláncokról. Ez biztosítja, hogy a node integritása megmaradjon, még akkor is, ha a forrás puffereket módosítják vagy felszabadítják a hívó által.

Lean 4 Implementáció (Formális Specifikáció)

A nsir.lean-ben a Node funkcionális struktúraként van definiálva. A Zig implementációval ellentétben nem kezel allokátort, hanem Lean változatlan adatkezelésére támaszkodik.

Mezők:

id - String - Egyedi azonosító.

data - String - Node hasznos teher.

qubit - Qubit - Formális kvantumállapot.

phase - Float - Fázis tényező.

metadata - StringMap String - Egy funkcionális asszociációs lista (párok listája).

Él Struktúra

Egy Edge definiálja a két csomópont közötti kapcsolatot. Kiterjeszti a klasszikus súlyozott éleket kvantum korrelációval és fraktál dimenzionalitással.

Technikai Attribútumok

Az Edge struktúra konzisztens mindkét implementációban.

Source/Target: Hivatkozások a csatlakoztatott csomópontok id-jére. Zig-ben ezek gyakran canonicalIdPtr hivatkozások a memória megtakarítása érdekében.

EdgeQuality: Egy enum, amely definiálja a link természetét (például szuperpozíció, összefonódott).

Kvantum Korreláció: Egy komplex szám (Complex(f64)), amely képviseli a kvantummechanikai erőt vagy összefonódási fázist a csomópontok között.

Fraktál Dimenzió: Egy f64 (Zig) vagy Float (Lean) érték, amely képviseli a kapcsolat önismétlő skáláját.

Memória és Tulajdonjog Szemantika

A két implementáció eltérően kezeli az adatok perzisztenciáját és identitását a nyelvi paradigma alapján.

Zig: Manuális Életciklus és Karakterlánc Internálás

A Zig implementáció kanonikus mutató stratégiát használ az allokációk minimalizálására. Amikor egy él létrejön, a source és target karakterláncok ideálisan mutatók a meglévő Node objektumok id mezőjére a SelfSimilarRelationalGraph-on belül.

dupeBytes: A Node.init és Node.clone használatos, hogy biztosítsa, hogy a node birtokolja az adatait.

putOwnedStringBytes: Egy segédfüggvény, amely kezeli a StringHashMap frissítéseket a régi kulcsok/értékek felszabadításával, mielőtt új duplikáltakat illesztene be.

freeMapStringBytes: A deinit során használják a metaadat térképek rekurzív tisztításához.

Lean 4: Funkcionális Asszociációs Listák

Lean 4-ben a metadata egy StringMap-ként van tárolva, amely asszociációs listaként van implementálva (List (String × α)).

Egyediség Invariáns: A StringMap.insert függvény biztosítja, hogy ha egy kulcs már létezik, a régi bejegyzés eltávolításra kerül, mielőtt az újat előkészítenék.

Változtathatatlanság: Minden módosítás a Node vagy Edge egy új verzióját adja vissza, ami elengedhetetlen a gráf tulajdonságok formális ellenőrzéséhez.

Mező Referencia Táblázat

Entitás és Mezők:

Node - qubit - Qubit - Automatikusan normalizálva az init-en

Node - phase - f64 / Float - Interferenciához használva a measure műveletekben

Edge - quality - EdgeQuality - Enum: szuperpozíció, összefonódott, koherens, összeomlott, fraktál

Edge - weight - f64 / Float - A kapcsolat klasszikus súlya

Edge - quantum_correlation - Complex - Képviseli az összefonódási fázist vagy korreláció nagyságot

Edge - fractal_dimension - f64 / Float - Méri a strukturális komplexitást/önismétlést

EdgeQuality Enum

Az EdgeQuality enumeráció definiálja a kapcsolatok szemantikai állapotát a csomópontok között a Nem-lineáris Önismétlő Információ Ábrázoláson (NSIR) belül. Elsődleges leíróként szolgál egy Él kvantum és strukturális természetéhez, diktálva, hogyan terjed az információ a gráfon és hogyan reagál a gráf a mérési műveletekre.

Enumeráció Variánsok

Az enum öt különálló variánsból áll, amelyek mindegyike egy specifikus szakaszt képvisel a gráf él információ életciklusában.

superposition (0) - Egy valószínűségi kapcsolatot képvisel, ahol a kapcsolat egyszerre létezik több potenciális állapotban.

entangled (1) - Nem-lokális korrelációt jelez két csomópont között, ahol az egyik csomópont állapota nem írható le függetlenül a másiktól.

coherent (2) - Egy stabil, fázis-igazított kapcsolat, amelyet általában szabványos információ kódoláshoz és összekapcsoláshoz használnak.

collapsed (3) - Egy él állapota egy kvantum mérés végrehajtása után, csökkentve a valószínűségi állapotokat egy határozott klasszikus értékre.

fractal (4) - Egy önismétlő rekurzív kapcsolatot képvisel, gyakran magas fractal_dimension értékekkel társítva.

Implementációs Részletek

Zig: enum(u8)-ként definiálva a memória hatékonyság és kiszámítható ABI elrendezés biztosítására.

Lean 4: induktív típusként definiálva a formális bizonyítások és minta illesztés elősegítésére.

Életciklus és Adat Folyam

Az Edge minősége egy Élnek nem statikus; átmeneteken megy keresztül a gráf műveletek alapján. Például, amikor a measure-t hívják meg egy gráfon, a mért csomópontokhoz társított élek átmennek a .collapsed állapotba.

Konverziós Segédeszközök

Mindkét implementáció segédfüggvényeket biztosít az enum, numerikus típusok (szerializáláshoz) és ember által olvasható karakterláncok közötti konverzióhoz.

Karakterlánc Konverzió

A toString és fromString módszereket szerializáláshoz és metaadat ábrázoláshoz használják.

Zig: switch utasítást használ a toString-hoz és std.mem.eql-t a fromString-hoz.

Lean 4: Funkcionális leképezésekként implementálva.

Numerikus Konverzió

Lean 4: Biztosítja a toNat és fromNat függvényeket. Zig-ben ezt az enum mögöttes u8 támogató típusa kezeli.

Formális Különbözőség és Tételek (Lean 4)

A Lean 4 implementáció tartalmaz egy tételkészletet, hogy bizonyítsa az EdgeQuality típus matematikai integritását. Ezek a bizonyítások biztosítják, hogy a futásidejű viselkedés Zig-ben megegyezik a formális specifikációval.

Különbözőség Tételek

Lean 4 kifejezetten bizonyítja, hogy minden variáns különbözik minden más variánstól a noConfusion használatával.

Példa: EdgeQuality.superposition_ne_entangled bizonyítja, hogy .szuperpozíció ≠ .összefonódott

Tíz ilyen tétel létezik, hogy lefedje az összes egyedi párosítást.

Leképezés Integritás

Injektív Leképezés: EdgeQuality.toNat_injective bizonyítja, hogy ha két minőség természetes szám ábrázolásai egyenlők, maguknak a minőségeknek is azonosnak kell lenniük.

Körbejárás Biztonság: EdgeQuality.fromNat_toNat bizonyítja, hogy egy minőség természetes számra és vissza konvertálása mindig az eredeti minőséget adja eredményül.

Határ Bizonyítás: EdgeQuality.toNat_lt_five bizonyítja, hogy minden variáns egy [0, 4] tartományba eső értékre képeződik le.

SelfSimilarRelationalGraph: Futásidejű Implementáció (Zig)

Ez az oldal magas szintű technikai áttekintést nyújt a SelfSimilarRelationalGraph implementációról Zig-ben. A Zig futásidejű környezetet nagy teljesítményű végrehajtásra tervezték a Jaide LLM projekten belül, biztosítva a Nem-lineáris Önismétlő Információ Ábrázolás (NSIR) specifikáció konkrét implementációját. Szorosan integrálódik az alacsony szintű memóriakezeléssel és tenzor műveletekkel, hogy támogassa a kognitív relációs feldolgozást.

Rendszer Architektúra

A Zig implementáció a SelfSimilarRelationalGraph struktúrán központosul, amely konténerként szolgál a csomópontokhoz, élekhez és kvantumállapot regisztrációkhoz. Kihasználja a Zig std.StringHashMap-jét a hatékony keresésekhez, és kezeli a memóriát explicit Allocator mintákon keresztül.

Komponens Áttekintések

Gráf Életciklus és Memória Kezelés

A gráf manuális memóriakezelési stratégiát használ, ahol a SelfSimilarRelationalGraph birtokolja a memóriát a csomópontjaihoz és éleihez. Több inicializálási stratégiát biztosít: initWithArena, initWithPool és initWithBuddy, hogy optimalizálja a különböző allokációs mintákhoz. Minden csomópont vagy él hozzáadása magában foglalja a karakterlánc adatok duplikálását, hogy biztosítsa, hogy a gráf fenntartsa a saját érvényes másolatát az azonosítókról és adatokról.

Kvantum Kapu Műveletek és Mérés

A futásidejű környezet támogatja a kvantummechanikai tulajdonságokat egy szimulált quantum_register-en keresztül. A csomópontok szuperpozícióba helyezhetők kapuk használatával, mint a hadamardGate, vagy módosíthatók Pauli kapukon keresztül. A measure művelet állapot összeomlást indít el, átmenve az éleket a szuperpozíció vagy összefonódott minőségekből az összeomlottba, és frissítve a node qubit amplitúdóit bázis állapotokra.

Topológia Kivonat és Állapot Integritás

A relációs szerkezet integritásának biztosítására a rendszer fenntart egy topology_hash-t. Ez egy SHA-256 kivonat, amelyet az összes csomópont, él és összefonódás egyedi kivonatainak XOR-olásával számítanak ki. Ez az XOR-alapú akkumuláció biztosítja, hogy a kivonat sorrend-független legyen, ami azt jelenti, hogy ugyanaz a gráf állapot ugyanazt a kivonatot eredményezi, függetlenül attól, hogy milyen sorrendben adták hozzá az elemeket.

Információ Kódolás és Tenzor Export

Az implementáció segédeszközöket biztosít a gráf és a gépi tanulási munkafolyamatok közötti hídhoz. Az encodeInformation lehetővé teszi a magas szintű adat bevitelt az adatok kivonatolásával csomópontok létrehozásához és automatikus összekapcsolásukkal a meglévő topológiához. Továbbá a gráf exportálhatja az állapotát core_tensor.Tensor formátumokba, lehetővé téve a kvantum amplitúdók és szomszédsági mátrixok numerikus formátumokká alakítását, amelyek alkalmasak neurális hálózat feldolgozásra.

Integrációs Összefoglaló

Standard Könyvtár: Kriptográfia (SHA256), HashMap-ek és Allokátorok

core_tensor: Biztosítja a Tensor struktúrát a beágyazás exporthoz

core_memory: Felület a specializált memória allokációs stratégiákhoz

Kvantum Logika: Qubit matematika és Kapu függvény mutatók implementációja

Gráf Életciklus és Memória Kezelés

Ez az oldal dokumentálja a SelfSimilarRelationalGraph életciklus műveleteit és memóriakezelési stratégiáit a Zig implementáción belül. Részletezi, hogyan kezeli a gráf a belső állapotát a csomópontok, élek és kvantum regiszterek között, biztosítva a memóriabiztonságot és a hatékony allokációt.

Memória Tulajdonjog Modell

A SelfSimilarRelationalGraph Zig implementációja egy explicit Allokátor-alapú tulajdonjog modellt követ. Minden gráf példány egy std.mem.Allocator-rel van inicializálva, amelyet a gráf a részei életciklusának kezelésére használ.

Kulcs Tulajdonjog Elvek

1. Node Tulajdonjog: A gráf birtokolja a Node struktúrákat. Amikor az addNode-t hívják meg, a gráf duplikálja a biztosított id és data karakterláncokat, hogy biztosítsa, hogy saját stabil memória hivatkozással rendelkezik.

2. Karakterlánc Kezelés: A dupeBytes és putOwnedStringBytes segédfüggvényeket használják a heap-en allokált karakterláncok kezelésére az ID-khez, adat hasznos terhekhez és metaadatokhoz.

3. Él Tulajdonjog: Az élek egy EdgeMap-ben vannak tárolva (egy StringHashMap ArrayList-ekből). A gráf kezeli ezeknek a listáknak és az egyes éleken belüli metaadat térképeknek az életciklusát.

Allokátor Stratégiák

A gráf három inicializálási stratégiát támogat specializált konstruktorokon keresztül, hogy különböző teljesítmény követelményekhez igazodjon.

Arena: initWithArena - Kötegelt műveletekhez optimalizálva, ahol az egész gráf egyszerre van felszabadítva.

Pool: initWithPool - Fix méretű elemekkel vagy gyakori egyenletes allokációkkal rendelkező gráfokhoz optimalizálva.

Buddy: initWithBuddy - Általános célú allokáció csökkentett fragmentációval változó objektum méretekhez.

Belső Adatszerkezetek

A SelfSimilarRelationalGraph több specializált térképet használ a hálózati topológia és kvantumállapot megszervezésére.

StringHashMap Belsők

Nodes Map (nodes): Egy string id-t képez le egy Node struktúrára. Ez az elsődleges nyilvántartás a gráf összes entitásához.

Kvantum Regiszter (quantum_register): Egy node id-t képez le a jelenlegi Qubit állapotára. Ez lehetővé teszi a gyors hozzáférést a kvantum amplitúdókhoz a kapu műveletek során.

EdgeMap és Párhuzamos Élek

A gráf egy egyedi EdgeMap struktúrát használ a párhuzamos élek támogatására (több él ugyanazon két csomópont között).

EdgeKey: Egy egyedi azonosító egy irányított csomópont párhoz.

Tárolás: Egy StringHashMap(ArrayList(Edge)), ahol a kulcs a source/target pár és az érték az összes él listája, amely összeköti őket.

EntMap (Összefonódás Térkép)

Az ent_map nyomon követi a kvantum összefonódásokat a csomópontok között. Amikor két csomópont összefonódik, egy bejegyzés jön létre ebben a térképben, hogy biztosítsa, hogy az egyik csomópont mérése helyesen indítsa el a partnere összeomlását.

Életciklus Műveletek

Inicializálás és Deinizializálás

init(allocator): Beállítja a belső HashMap-eket és előkészíti a gráfot a használatra.

deinit(): Végigiterál az összes csomóponton és élen, hogy felszabadítsa a birtokolt karakterláncokat és metaadatokat, majd törli a térképeket.

clear(): Visszaállítja a gráfot egy üres állapotba az összes térkép törlésével anélkül, hogy megsemmisítené magát a gráf példányt.

Mutációs Műveletek

addNode: Egy új entitást ad a gráfhoz. Ellenőrzi, hogy a node ID már létezik-e. Inicializál egy Node struktúrát, amely duplikálja az ID és Data karakterláncokat. Beszúrja a node-ot a nodes térképbe. Inicializálja a node állapotát a quantum_register-ben.

addEdge: Kapcsolatot hoz létre két meglévő csomópont között. Ellenőrzi, hogy mind a source, mind a target ID-k léteznek a nodes térképben. Lekéri vagy létrehoz egy ArrayList(Edge)-et a specifikus source-target párhoz. Hozzáad egy új Edge struktúrát a listához.

removeNode: Egy komplex művelet, amely fenntartja a gráf integritását. Eltávolítja a node-ot a nodes térképből és felszabadítja a memóriáját. Beolvassa az edges térképet és eltávolít minden élt, ahol a node vagy a source vagy a target. Eltávolítja a node-ot a quantum_register-ből és ent_map-ből.

Topológia Integritás és Kivonatolás

A gráf állapota egy topology_hash-ben van összefoglalva. Ez kritikus fontosságú az önismétlő szerkezet konzisztenciájának biztosításához.

Kivonat Akkumuláció

Az updateTopologyHash függvény SHA-256-ot használ, de aggregálja az egyes komponens kivonatokat XOR használatával (xorDigest). Ez biztosítja, hogy az eredményül kapott kivonat sorrend-független legyen; a gráf kivonat ugyanaz marad, függetlenül a beszúrási sorrendtől.

Kvantum Kapu Műveletek és Mérés

Ez az oldal dokumentálja a kvantumállapot manipulációs és megfigyelési mechanizmusokat az NSIR core Zig implementációján belül. Kiterjed az egyedi-qubit kapuk alkalmazására, az összefonódott állapotok létrehozására a csomópontok között, és a valószínűségi mérési folyamatra, amely összeomlasztja a kvantumállapotokat klasszikus információvá.

Kvantum Kapu Keretrendszer

A rendszer funkcionális megközelítést használ a kvantum kapukhoz, ahol a kapukat transzformációs függvényekként definiálják, amelyek egy Qubit struktúrán működnek.

Kapu Definíció és Szabvány Kapuk

A nsir_core.zig-ben egy Gate egy függvény mutató típus, amely elfogad egy Qubit-t és egy transzformált Qubit-t ad vissza. A könyvtár szabványos implementációkat biztosít a gyakori kvantum kapukhoz.

hadamardGate: Szuperpozíciót hoz létre

pauliXGate: Bit-flip (NOT) - Felcseréli az a és b amplitúdókat

pauliYGate: Bit és fázis flip - Komplex forgatás és csere

pauliZGate: Fázis flip - Megfordítja a b amplitúdó előjelét

Kapu Alkalmazás Folyam

Az applyQuantumGate függvény szolgál elsődleges felületként egy node kvantumállapotának módosítására. Lekéri a node-ot a nodes térképből, alkalmazza a kapu függvényt, majd frissíti a topology_hash-t, hogy tükrözze az állapot változást.

Összefonódás és Bell Állapotok

Az összefonódást az NSIR-ben a TwoQubit struktúra képviseli, amely tárolja egy közös állapot négy komplex amplitúdóját (amp00, amp01, amp10, amp11).

Az entangleNodes Művelet

Az entangleNodes függvény kvantum korrelációt hoz létre két csomópont között.

1. Érvényesítés: Biztosítja, hogy mindkét csomópont létezik a gráfban.

2. Állapot Inicializálás: Létrehoz egy TwoQubit állapotot, amelyet általában a Bell Φ+ állapotra inicializálnak ((|00⟩ + |11⟩)/√2).

3. Regiszter Frissítés: Tárolja a TwoQubit állapotot a quantum_register-ben.

4. Kapcsolat Követés: Rögzíti a párosítást az entanglements térképben (EntMap), hogy biztosítsa, hogy az egyik csomópont mérése kiváltsa a másik összeomlását.

Mérési Életciklus

A measure függvény implementálja az átmenetet a kvantum szuperpozícióból a klasszikus bizonyosságba. Egy 64 bites Xorshift véletlenszám generátort (std.rand.Xorshift64) használ, hogy meghatározza az eredményt a valószínűségi amplitúdók alapján.

Két-Út Mérési Logika

Az implementáció ágazik attól függően, hogy a cél csomópont összefonódott vagy független.

1. Független Node Út: Kiszámítja a prob0-t (|a|^2). Ha egy véletlenszerű float kisebb, mint a prob0, a qubit az initBasis0()-ra omlik össze, különben az initBasis1()-re.

2. Összefonódott Node Út: Lekéri a TwoQubit állapotot a quantum_register-ből. Kiszámítja a közös valószínűségeket (például P(0) = |amp00|^2 + |amp01|^2). Összeomlasztja mindkét csomópontot egyszerre a közös állapot alapján, és eltávolítja a bejegyzést a quantum_register-ből és az entanglements térképből.

Él Minőség Frissítések

A mérés kritikus mellékhatása a gráf topológia szinkronizálása. A mért csomópont(ok)hoz kapcsolódó élek EdgeQuality-je frissül .collapsed-ra.

Topológia Kivonat és Állapot Integritás

A SelfSimilarRelationalGraph implementáció a nsir_core.zig-ben egy robusztus mechanizmust biztosít a gráf strukturális és kvantum integritásának ellenőrzésére az updateTopologyHash függvényen keresztül. Ez a folyamat egy egyedi SHA-256 aláírást generál, amely képviseli a gráf teljes állapotát, beleértve a node tulajdonságokat, él kapcsolatokat és kvantum összefonódásokat.

A Kivonatolás Pipeline

A topológia kivonat nem egy egyszerű lineáris kivonat az adatokból. Ehelyett egy XOR-alapú akkumulációs stratégiát használ, hogy biztosítsa, hogy az eredményül kapott kivonat sorrend-független legyen. Ez azt jelenti, hogy ugyanaz a gráf azonos kivonatot fog előállítani, függetlenül attól, hogy milyen sorrendben adták hozzá a csomópontokat vagy éleket a belső térképekhez.

Implementációs Részletek

XOR-Alapú Aggregáció (xorDigest)

Egy stabil kivonat fenntartásához a különböző memória elrendezések vagy beszúrási sorrendek között a StringHashMap-ben, a rendszer egy xorDigest segédfüggvényt használ.

Függvény: xorDigest(current: *[32]u8, new: [32]u8)

Logika: Bitwise XOR-t hajt végre a current akkumulált kivonat és egy new kivonat töredék között. Mivel a XOR kommutatív (A ⊕ B = B ⊕ A), a végeredmény invariáns a frissítések sorozatára.

Per-Node Kivonatolás

Minden node-ra a nodes térképben egy SHA-256 kivonatot számítanak ki a következő mezők alapján:

1. ID: Az egyedi string azonosító.

2. Data: A node nyers bájt tartalma.

3. Phase: A lebegőpontos fázis érték.

4. Qubit Amplitúdók: Az a és b amplitúdók valós és imaginárius részei.

5. Metadata: Minden kulcs-érték pár, amely a node metaadat térképében van tárolva.

Per-Edge Kivonatolás

Az élek az edges térképből (egy ArrayList élekből) vannak lekérve. Minden él hozzájárul a topológia kivonathoz a következők alapján:

1. Source/Target: A csatlakoztatott csomópontok ID-i.

2. Quality: Az EdgeQuality enum érték (például szuperpozíció, összefonódott).

3. Weight: A lebegőpontos súly.

4. Kvantum Korreláció: Valós és imaginárius komponensek.

5. Fraktál Dimenzió: A strukturális skálázási tényező.

Összefonódás Kivonatolás

A kvantum összefonódások nem-lokális korrelációkat képviselnek a csomópontok között, tárolva a quantum_register-ben. A kivonat tartalmazza:

1. Node Pár: A két összefonódott csomópont ID-i.

2. Bell Állapot: A TwoQubit állapot négy komplex amplitúdója (amp00, amp01, amp10, amp11).

Összefoglaló a Kivonatolt Komponensekről

Node: id, data, qubit (a/b re/im), phase, metadata

Edge: source, target, quality, weight, correlation, fractal_dimension

Összefonódás: Node pár ID-k, TwoQubit amplitúdók (amp00-amp11)

A végső kimenet egy 64 karakteres hexadecimális karakterlánc, amely a topology_hash mezőben van tárolva a SelfSimilarRelationalGraph struktúrában. Ez a kivonat állapot ujjlenyomatként szolgál a szinkronizáláshoz, gyorsítótárazáshoz és a kognitív relációs állapot kriptográfiai ellenőrzéséhez.

Információ Kódolás és Tenzor Export

Ez a szakasz részletezi a mechanizmusokat a nsir_core-on belül a nyers adatok Nem-lineáris Önismétlő Információ Ábrázolás (NSIR) gráf szerkezetté alakítására és ezt követően az állapot tenzor formátumokba exportálására, amelyek kompatibilisek a gépi tanulási keretrendszerekkel. Ezek a folyamatok hidat képeznek a diszkrét információ csomópontok és a folytonos vektor terek között.

Információ Kódolás

A kódolási folyamat egy determinisztikus, ellenőrizhető gráf szerkezet létrehozására fókuszál a bemeneti adatokból. Kivonat-alapú azonosítást használ, hogy biztosítsa, hogy az azonos információ azonos node elhelyezést eredményezzen, miközben automatikusan létrehozza a relációs linkeket a gráf koherencia fenntartásához.

Node Létrehozás és Automatikus Linkelés

Az encodeInformation függvény szolgál elsődleges belépési pontként az adatok SelfSimilarRelationalGraph-ba történő beviteléhez.

1. Kivonat-alapú ID: A rendszer egy egyedi azonosítót generál az új csomópontokhoz az adatok SHA-256 használatával történő kivonatolásával.

2. Node Inicializálás: Ha a csomópont még nem létezik, egy új Node-t hoznak létre egy alapértelmezett Qubit-tel a |0⟩ bázis állapotban.

3. Koherens Linkelés: A strukturális integritás fenntartása érdekében a rendszer automatikusan létrehoz legfeljebb 3 élt az új csomópont és a gráf meglévő csomópontjai között. Ezek az élek EdgeQuality.coherent-tel vannak inicializálva.

Tenxor Export és Beágyazások

A Kognitív Relációs Motorral (CRE) és külső ML modellekkel való integrációhoz a gráf állapotot numerikus tenzorokként kell exportálni. Ezt két elsődleges függvény kezeli: exportNodeEmbeddings és exportAdjacencyMatrix.

Node Beágyazások (Qubit Amplitúdók)

Az exportNodeEmbeddings függvény átalakítja a gráf minden csomópontjának kvantumállapotát egy nagy dimenziós tenzorrá.

Formátum: Minden node Qubit-je (két komplex számból áll, a és b) 4 valós értékre van lapítva: [a.re, a.im, b.re, b.im]

Struktúra: Az eredményül kapott core_tensor.Tensor alakja [N, 4], ahol N a csomópontok száma.

Integráció: Ez a függvény közvetlenül interfészel a core_tensor modullal a tenzor adatok allokálásához és kitöltéséhez.

Szomszédsági Mátrix

Az exportAdjacencyMatrix függvény képviseli a gráf topológiáját és él súlyait egy négyzetes mátrixként.

Leképezés: Egy ideiglenes StringHashMap(usize)-t használ, hogy leképezze a node ID-ket mátrix indexekre.

Értékek: A mátrix cellákat az élek weight tulajdonságával töltik fel.

Alak: A kimenet egy core_tensor.Tensor [N, N] alakban.

Külső Modul Integrációs Szerződés

Az export függvények ragasztóként működnek a nsir_core és a szélesebb rendszer numerikus moduljai között.

exportNodeEmbeddings - core_tensor.Tensor - [N, 4] - Node.qubit (amplitúdók)

exportAdjacencyMatrix - core_tensor.Tensor - [N, N] - Edge.weight

Információ Dekódolás

A decodeInformation függvény biztosítja a kódolás inverz műveletét, lekérve az eredeti adatokat, amelyek egy specifikus node ID-hoz vannak társítva.

Keresés: Lekérdezi a nodes térképet a biztosított ID használatával.

Adat Lekérés: Ha a csomópont létezik, visszaadja a data mező egy szeletét. Megjegyzés: a hívó nem birtokolja ezt a memóriát; azt a Node birtokolja és a gráf allokátora kezeli.

SelfSimilarRelationalGraph: Formális Specifikáció (Lean 4)

A Self-Similar Relational Graph Lean 4 implementációja szolgál az NSIR rendszer formális specifikációjaként. Míg a Zig implementáció a nagy teljesítményű futásidejű végrehajtásra és memória hatékonyságra fókuszál, addig a Lean 4 kód a nsir.lean-ben matematikailag rigorózus modellt biztosít. Definiálja a gráf műveletek és kvantumállapot átmenetek szemantikáját, formális helyességi bizonyításokkal kísérve.

A formális specifikáció biztosítja, hogy a futásidejű környezetben implementált logika megfeleljen a kiszámítható algebrai és kvantummechanikai tulajdonságoknak.

Rendszer Áttekintés és Összehasonlítás

A Lean 4 implementáció tükrözi a Zig futásidejű környezet szerkezetét, de funkcionális paradigmákat használ. A kulcs különbségek közé tartozik a perzisztens adatszerkezetek (mint az asszociációs listák a leképezéshez) használata a változtatható hash térképek helyett, és a nem kiszámítható definíciók felvétele a lebegőpontos komplex számokat érintő műveletekhez, ahol a pontos eldönthetőség nem szükséges a logika bizonyításokhoz.

Jellemzők Összehasonlítása:

Térkép Implementáció: StringHashMap (Változtatható) Zig-ben vs StringMap (Funkcionális Assoc-Lista) Lean 4-ben

Komplex Számok: std.math.Complex(f64) Zig-ben vs structure Complex Lean 4-ben

Kivonatolás: Iteratív SHA-256 Zig-ben vs Funkcionális sha256DigestHex Lean 4-ben

Ellenőrzés: Egységtesztek Zig-ben vs Formális Tételek Lean 4-ben

Véletlenszerűség: std.rand.Xoroshiro128 Zig-ben vs Egyedi 64-bit Xorshift Lean 4-ben

Lean 4 Segéd Rendszerek

A specifikáció több alacsony szintű segéd modulra támaszkodik, amelyeket nulláról implementáltak Lean-ben, hogy elkerüljék a külső függőségeket és elősegítsék a bizonyításokat.

Komplex Aritmetika: Definiálja a Complex számokat add, sub, mul és magnitudeSquared műveletekkel. Strukturális extenzionalitás tételeket tartalmaz (Complex.ext), hogy bizonyítsa, hogy két komplex szám akkor egyenlő, ha komponenseik egyenlők.

StringMap: Egy funkcionális asszociációs lista, amelyet a node és él nyilvántartások képviselésére használnak. Fenntart invariánsokat, mint a beszúrás-eltávolítás-először, hogy szimulálja a térkép viselkedést egy tiszta funkcionális kontextusban.

SHA-256: A Secure Hash Algorithm 256 teljes implementációja, beleértve a paddinget (sha256Pad), üzenet bővítést és tömörítést. Ezt használják a topology_hash formális definiálására.

Rng: Egy 64-bit Xorshift PRNG, amelyet determinisztikus, mégis valószínűségi modell biztosítására használnak a measure művelethez.

Gráf Műveletek és Helyességi Tételek

A specifikáció magja a SelfSimilarRelationalGraph struktúra és a hozzá kapcsolódó API. A Zig implementációval ellentétben, amely mutatókat kezel, a Lean verzió a canonicalIdPtr-t használja szimbolikus hivatkozásként az identitás konzisztencia biztosításához a funkcionális frissítések során.

Gráf API: Tartalmazza az empty, addNode, addEdge, applyQuantumGate és entangleNodes függvényeket.

Helyességi Tételek: Az implementáció bizonyításokat tartalmaz az enum tulajdonságokra, mint az EdgeQuality.fromNat_toNat, amely garantálja, hogy az él minőségek szerializálása megfordítható és injektív.

Állapot Invariánsok: Lean típusrendszerét használják annak kikényszerítésére, hogy bizonyos műveletek (mint a mérés) érvényes összeomlott állapotba vigyék a gráfot, egy tulajdonság, amelyet csupán feltételeznek a futásidejű környezetben.

Lean 4 Segéd Rendszerek: Complex, StringMap, SHA-256 és Rng

Ez az oldal dokumentálja az alapvető segéd rendszereket, amelyeket Lean 4-ben implementáltak a nsir_core tárházon belül. Ezek a komponensek biztosítják a matematikai és kriptográfiai primitíveket, amelyek szükségesek a Self-Similar Relational Graph formális specifikációjához, beleértve a kvantumállapot ábrázolást, funkcionális adattárolást, integritás kivonatolást és valószínűségi mérést.

Komplex Aritmetika

A Complex struktúra biztosítja a matematikai alapot a kvantum amplitúdókhoz, amelyeket a Qubit és TwoQubit típusok használnak. Két Float értéket tartalmazó struktúraként van implementálva, amelyek képviselik a valós (re) és imaginárius (im) komponenseket.

Implementáció és Kulcs Függvények

A rendszer szabványos aritmetikai műveleteket definiál, és nem kiszámítható definíciókat biztosít komplex konstansokhoz és műveletekhez, hogy elősegítse a formális érvelést Lean környezetén belül.

add: Komplex összeadást végez: (a.re + b.re) + i(a.im + b.im)

sub: Komplex kivonást végez: (a.re - b.re) + i(a.im - b.im)

mul: Komplex szorzást végez a disztributív törvény használatával.

magnitudeSquared: Kiszámítja |c|^2 = c.re^2 + c.im^2

Formális Tételek

A komplex aritmetikai alrendszer integritásának biztosítására több tételt biztosítanak, hogy bizonyítsák a mező műveletek viselkedését.

Extenzionalitás: A Complex.ext bizonyítja, hogy két komplex szám akkor egyenlő, ha valós és imaginárius részeik egyenlők.

Komponens Projekciók: Az add_re, sub_im és mul_re tételek megerősítik, hogy a komplex műveletek eredményei megfelelnek a várt komponens-szintű definícióknak.

StringMap: Funkcionális Asszociációs Lista

A StringMap egy egyedi funkcionális asszociációs lista, amelyet node metaadatok és gráf elemek tárolására használnak. A szabványos térképekkel ellentétben egy specifikus invariánst tart fenn: a beszúrás művelet eltávolít minden meglévő bejegyzést egy kulcshoz, mielőtt hozzáadná az új értéket, biztosítva, hogy a kulcsok egyediek maradjanak és a térkép lapos maradjon.

Adat Folyam és Invariánsok

A StringMap (String × α) párok listájaként van definiálva.

Kulcs Műveletek:

find: Rekurzívan keresi a listát egy kulcs első előfordulására.

remove: Szűri a listát, hogy kizárjon minden párt, amely megegyezik a cél kulccsal.

insert: Kombinálja a remove-ot és a lista konstrukciót, hogy kikényszerítse az egyediség invariánst.

SHA-256 Implementáció

A SHA-256 alrendszer biztosítja a mechanizmust a gráf topology_hash kiszámításához. Ez egy teljes, tiszta Lean 4 implementációja a SHA-256 algoritmusnak, beleértve a paddinget, üzenet bővítést és tömörítési ciklust.

Kriptográfiai Pipeline

Az implementáció követi a szabványos NIST specifikációt, az adatokat 512-bites blokkokban dolgozza fel.

Padding: sha256Pad - Biteket fűz a bemeneti karakterlánchoz, hogy elérje az 512 bites többszöröst, beleértve a hossz utótagot.

Bővítés: sha256ExpandMessage - Kibővít egy 16-szavas blokkot egy 64-szavas ütemtervre σ0 és σ1 függvények használatával.

Tömörítés: sha256Compress - A fő ciklus, amely alkalmazza a 64 kör transzformációt a kivonat állapotra.

Hex Kimenet: sha256DigestHex - Átalakítja a végső 256-bites állapotot egy 64 karakteres hexadecimális karakterlánccá.

64-bit Xorshift Rng

A Rng struktúra implementál egy 64-bit Xorshift pszeudo-véletlenszám generátort. Elsősorban a measure műveletben használják, hogy meghatározzák egy qubit összeomlott állapotát a valószínűségi amplitúdói alapján.

Állapot és Transzformáció

A generátor egyetlen UInt64 állapotot tart fenn. A next függvény három bitwise eltolást és XOR műveletet alkalmaz, hogy előállítsa a következő állapotot.

A Xorshift Algoritmus:

1. x ← x ⊕ (x << 13)

2. x ← x ⊕ (x >> 7)

3. x ← x ⊕ (x << 17)

Kulcs Függvények:

next: Frissíti a belső állapotot és visszaad egy új Rng példányt.

nextFloat: Átalakítja a 64-bites egész számot egy Float-tá a [0.0, 1.0] tartományban az állapot elosztásával 2^64-1-gyel. Ez kritikus fontosságú a measure függvény számára, hogy összehasonlítsa a magnitudeSquared értékekkel.

Gráf Műveletek és Helyességi Tételek

Ez az oldal részletezi a Self-Similar Relational Graph formális specifikációját Lean 4-ben. Kiterjed a kulcs gráf manipulációs API-ra, az alapvető funkcionális adatszerkezetekre és a matematikai tételekre, amelyek garantálják a strukturális és viselkedési helyességet. Míg a Zig implementáció nagy teljesítményű végrehajtást biztosít, addig a Lean 4 implementáció szolgál alapigazság specifikációként, használva a típusrendszert invariánsok kikényszerítésére, mint az azonosító egyediség és állapot integritás.

Formális Gráf API és Implementáció

A Lean 4 implementáció funkcionális struktúraként definiálja a SelfSimilarRelationalGraph-ot. A Zig implementációval ellentétben, amely változtatható StringHashMap-ot használ, a Lean 4 egy egyedi StringMap-ot (egy asszociációs lista egyediség invariánssal) használ a csomópontok, élek és kvantumállapotok kezelésére.

Kulcs API Függvények

A következő függvények definiálják a gráf életciklusát a formális modellben:

empty: Új gráfot hoz létre. Üres StringMap példányokat inicializál minden mezőhöz.

addNode: Beszúr egy új Node-ot. A StringMap.insert-t használja, amely fenntartja az utolsó-ben-nyer és egyediség tulajdonságokat.

addEdge: Összekapcsol két csomópontot. Hozzáad egy Edge-t a source csomópont szomszédsági listájához.

setQuantumState: Frissíti egy node Qubit-jét. Közvetlenül frissíti a quantum_register térképet.

applyQuantumGate: Transzformál egy Qubit-t. Komplex mátrix transzformációt alkalmaz a cél csomópont amplitúdóira.

entangleNodes: Összekapcsol két qubitet. Feltölti az entanglement_map-et egy TwoQubit állapottal.

measure: Összeomlaszt egy állapotot. 64-bit Xorshift RNG-t használ, hogy meghatározza az eredményt a valószínűségi amplitúdók alapján.

StringMap Egyediség és canonicalIdPtr

Egy kritikus invariáns az NSIR gráfban, hogy minden csomópontnak egyedi azonosítóval kell rendelkeznie. A Zig implementációban ezt a canonicalIdPtr kezeli a memória hatékonyság biztosítására. Lean 4-ben ezt a StringMap adatszerkezet és a hozzá kapcsolódó tételek kényszerítik ki.

A StringMap Invariáns

A StringMap párok listájaként (String × α) van definiálva. A hash map viselkedésének tükrözésére az implementáció biztosítja, hogy amikor egy kulcsot beszúrnak, minden meglévő bejegyzés ahhoz a kulcshoz logikailag felülíródik.

Tétel StringMap.insert_contains: Bizonyítja, hogy egy kulcs beszúrása után a térkép garantáltan tartalmazza azt a kulcsot.

Tétel StringMap.get_insert_same: Bizonyítja, hogy egy kulcs lekérése közvetlenül a beszúrása után a újonnan beszúrt értéket adja vissza.

Helyességi Tételek EdgeQualities-hez

Az EdgeQuality enum definiálja egy kapcsolat fizikai/kvantum állapotát (például .szuperpozíció, .összefonódott). A Lean 4 kimerítő bizonyításokat biztosít, hogy biztosítsa, hogy ezek az állapotok különbözőek és helyesen vannak szerializálva, megelőzve a logikai hibákat, amelyek előfordulhatnak a Zig futásidejű környezet C-stílusú enumjaiban.

Kulcs Tételek:

1. Különbözőség: Az olyan tételek, mint az EdgeQuality.superposition_ne_entangled, bizonyítják, hogy nincs két enum variáns, amely egyenlő lenne. Ezt a noConfusion használatával ellenőrzik.

2. Bijektív Leképezés: Az EdgeQuality.fromNat_toNat tétel bizonyítja, hogy egy EdgeQuality természetes számra és vissza konvertálása identitás függvény.

3. Injektivitás: Az EdgeQuality.toNat_injective biztosítja, hogy minden minőség egy egyedi egész számra képeződik le.

Tulajdonságok és Jelentőségük:

Kimerítősség: all_constructors - Garantálja, hogy az összes lehetséges él állapotot kezelik.

Határok: toNat_lt_five - Biztosítja, hogy az egész szám ábrázolás a [0, 4] tartományon belül marad.

Karakterlánc Integritás: toString_inj - Biztosítja, hogy a karakterláncokra való szerializálás egyedi és megfordítható.

Kvantum Művelet Helyesség

Az applyQuantumGate függvény Lean 4-ben szolgál formális specifikációként a Zig applyQuantumGate-hoz.

Komplex Aritmetika Tételek

Mivel a kvantum kapuk komplex szám szorzásra támaszkodnak, a Lean 4 definiál egy Complex struktúrát, és bizonyítja az alapvető tulajdonságokat.

Összeadás/Kivonás: Definíciók az add és sub műveletekhez a megfelelő projekciós tételekkel (add_re, add_im).

Szorzás: A mul definíció kezeli a szabványos (ac-bd) + i(ad+bc) logikát, amelyet a qubit amplitúdók transzformálására használnak a kapu alkalmazás során.

Mérés és RNG

A measure művelet használja a Rng.next függvényt (egy 64-bit Xorshift) a valószínűségi eredmény meghatározásához.

NSIR Moduláció: Formális Pipeline Specifikáció (Lean 4)

Ez az oldal magas szintű áttekintést nyújt az NSIR (Nem-lineáris Önismétlő Információ Ábrázolás) modulációs szakasz formális specifikációjáról, amelyet Lean 4-ben implementáltak. Ez a specifikáció szolgál matematikai alapigazságként az NSIR képzési pipeline-hoz, definiálva a numerikus ábrázolást, a transzformációs logikát és a több szakaszos folyamatot irányító állapot gépet.

A formális specifikáció az nsir_modulation.lean-en belül található, amely hidat képez az absztrakt matematikai koncepciók és az ellenőrizhető kód entitások között.

Numerikus Alap: Fixpontos Aritmetika

A determinisztikus viselkedés biztosításához a különböző hardver architektúrákon és a numerikus biztonság formális bizonyításainak elősegítésére a pipeline egy egyedi Fixpontos (FP) aritmetikai rendszert használ a szabványos lebegőpontos típusok helyett.

Struktúra: Az FP egy struktúra, amely egy Int értéket csomagol.

Skálázás: Fix 10^8 (100000000) skálát használ.

Aritmetika: Műveletek az add, sub, neg és mul műveletekhez definiálva vannak a kapcsolódó algebrai tételekkel (például kommutativitás, asszociativitás) a formális ellenőrzés támogatására.

Biztonság: A BoundedArithmetic szakasz határokat definiál az Usize és U32 típusokhoz, hogy bizonyítsa a túlcsordulások hiányát a memória indexelés és akkumuláció során.

Modulációs Logika és Memória Modell

Az NSIR szakasz magja az aktivációk és gradiensek modulációja az adatfolyam statisztikai tulajdonságai alapján.

Memória Ábrázolás

A rendszer hardver memóriát modellez egy MemoryMap használatával, amely funkcionális leképezésként van definiálva a Nat címektől az Option FP-ig. Ez lehetővé teszi a formális érvelést a memóriabiztonságról, olvasásokról és írásokról a pipeline-on belül.

Előre és Hátra Passz

A modulációs logika egy modulationFactor-t (konstans 1.05) alkalmaz azokra az értékekre, amelyek meghaladják a jelenlegi köteg átlagát.

Előre (nsirForward): Kiszámítja a bemeneti lista átlagát, és skálázza az értékeket a modulateValue használatával, ha nagyobbak az átlagnál.

Hátra (nsirBackward): Az előre passzt tükrözve beállítja a gradienseket ugyanazon feltételes logika alapján, hogy fenntartsa a matematikai konzisztenciát a visszafejtés során.

Pipeline Orkesztráció

Az NSIR moduláció nem egy elszigetelt függvény, hanem egy specifikus szakasz egy strukturált képzési pipeline-on belül. A specifikáció definiál egy formális állapot gépet a szakaszok közötti átmenetek kezelésére.

Pipeline Komponensek

A pipeline-t diszkrét szakaszok és fázisok halmaza definiálja, amelyek szabályozzák az információ transzformációját. A PipelineStage induktív típus definiálja a műveletek sorozatát, míg a TrainingPhase definiálja a rendszer operatív módját.

Pipeline Szakaszok:

Embedding: A bemeneti tokenek kezdeti vektorizálása a nagy dimenziós térbe.

OFTB: Ortogonális Funkcionális Transzformációs Blokk.

RSF: Relációs Szemantikai Szűrő.

NSIR: Nem-lineáris Önismétlő Információ Ábrázolás moduláció.

Projection: Végső leképezés a kimeneti dimenzióra (például szótár méret).

Képzési Fázisok:

Forward: Kiszámítja az aktivációkat és tárolja őket az activationMap-ben.

Backward: Kiszámítja a gradienseket a láncszabály használatával, tárolva a gradientMap-ben.

ZeroGrad: Visszaállít minden gradienset nullára egy új optimalizálási lépés előtt.

UpdateParams: Alkalmazza a kiszámított gradienseket a belső súlyok frissítésére.

Pipeline Állapot és Nyomon Követhetőség

A rendszer állapota a PipelineState struktúrában van kapszulázva, amely kezeli a memória térképeket az aktivációkhoz és gradiensekhez, egy stepCounter mellett és egy PipelineTrace-t a nyomon követhetőséghez.

Állapot Struktúra

A PipelineState tartalmazza:

activationMap: Egy MemoryMap (Nat → Option FP), amely közbenső értékeket tárol.

gradientMap: Egy MemoryMap, amely részleges deriváltakat tárol.

stepCounter: Egy Nat, amely nyomon követi a végrehajtási lépések számát.

trace: Egy PipelineTrace (PipelineEntry-k listája), amely rögzít minden állapot átmenetet.

Nyomon Követhetőség: PipelineEntry

Minden művelet a pipeline-on belül generál egy PipelineEntry-t, amely rögzíti:

A végrehajtott szakaszt.

A fázist (Előre/Hátra).

Egy időbélyeget (Nat lépésként képviselve).

Egy ellenőrző összeget az állapotról az adat integritás biztosításához.

Végrehajtási Logika és Szakasz Sorrend

A pipeline szigorú műveleti sorrendet kényszerít ki. Az Előre fázisban a szakaszoknak az Embedding-től a Projection-ig kell haladniuk. A Hátra fázisban a sorrend fordított.

Előre és Hátra Orkesztráció

A kulcs végrehajtási függvények, executeForward és executeBackward, szekvenciálisan hívják meg a stepPipeline-t minden szakaszhoz a definiált sorrendben.

Pipeline Állapot Gép Átmenetek

A pipeline szigorú sorrendet kényszerít ki a műveletekre. Az Előre fázisban a szakaszoknak az Embedding-től a Projection-ig kell haladniuk. A Hátra fázisban a sorrend fordított.

Modulációs Lépések Implementációja

Amikor a stepPipeline függvény eléri a .NSIR szakaszt, a specifikus modulációs logikára diszpécserel.

Előre Moduláció: Az nsirForward függvény kiolvassa az értékeket az activationMap-ből, kiszámítja az átlagot, és alkalmazza a modulationFactor-t (1.05) az átlagot meghaladó értékekre.

Hátra Moduláció: Az nsirBackward függvény beállítja a gradienseket az eredeti előre aktivációk alapján, biztosítva, hogy a gradiens folyam tiszteletben tartsa az előre passz során alkalmazott nem-lineáris skálázást.

N Kör Végrehajtása

Az executeNRounds függvény biztosítja a magas szintű belépési pontot a képzéshez, iteratívan végrehajtva:

1. ZeroGrad fázis.

2. executeForward.

3. executeBackward.

4. UpdateParams fázis.

Fixpontos Aritmetika (FP) és Numerikus Biztonság

Ez az oldal részletes technikai hivatkozást nyújt a fixpontos aritmetikai rendszerhez és a numerikus biztonsági keretrendszerhez, amelyet Lean 4-ben implementáltak. Ezek a rendszerek determinisztikus, túlcsordulás-biztos alternatívát biztosítanak a szabványos lebegőpontos műveletekhez, biztosítva, hogy az NSIR modulációs pipeline fenntartsa a matematikai integritást a különböző végrehajtási környezeteken.

Fixpontos (FP) Struktúra és Ábrázolás

Az FP struktúra a modulációs pipeline alapvető numerikus típusa. Egy egész szám alapú ábrázolást használ, hogy elkerülje az IEEE 754 lebegőpontos számokkal kapcsolatos nem-determinizmust és kerekítési problémákat.

Belső Ábrázolás

Alap Típus: Int

Skála Faktor: 10^8 (definíció szerint 100000000)

Pontosság: 8 tizedesjegy.

Konstans Értékek

zero: 0 (Nyers) / 0.0 (Ember által olvasható) - Additív identitás

one: 100000000 (Nyers) / 1.0 (Ember által olvasható) - Multiplikatív identitás

modulationFactor: 105000000 (Nyers) / 1.05 (Ember által olvasható) - Az NSIR frissítések skálázási konstansa

Aritmetikai Műveletek

A rendszer szabványos aritmetikát implementál az alapvető Int érték manipulálásával és a skála korrekciójával szorzás során.

Összeadás/Kivonás: Közvetlenül az alapvető Int értékeken végrehajtva.

Negáció: Megfordítja az alapvető Int előjelét.

Szorzás: Kiszámítja (a · b) / scale-t a fixpontos eltolás fenntartásához.

Konverzió: A fromInt balra tol egy egész számot a skála faktorral.

Algebrai Tételek és Formális Bizonyítások

Az FP implementáció tartalmaz egy átfogó bizonyításkészletet, amely ellenőrzi, hogy kielégíti a kommutatív gyűrű axiómáit (kivéve a multiplikatív inverzt). Ezek a tételek biztosítják, hogy a műveletek újrarendezése (például a pipeline párhuzamosított verziójában) nem változtatja meg a numerikus eredményt.

Kommutativitás és Asszociativitás:

add_comm: a + b = b + a

add_assoc: (a + b) + c = a + (b + c)

mul_comm: a · b = b · a

Identitások és Inverzek:

add_zero / zero_add: a + 0 = a

add_neg_cancel: a + (-a) = 0

mul_zero / zero_mul: a · 0 = 0

Disztributivitás és Kivonás:

neg_add_distrib: -(a + b) = (-a) + (-b)

sub_eq_add_neg: a - b = a + (-b)

neg_sub: -(a - b) = b - a

Numerikus Biztonság és Határok

A formális fixpontos logika és a hardver-szintű korlátok közötti szakadék áthidalására a rendszer definiálja a NsirNumericalSafety és BoundedArithmetic modulokat.

Korlátozott Aritmetika

A rendszer explicit határokat definiál a 64-bites és 32-bites előjel nélküli egész számokhoz, hogy bizonyítsa, hogy az index számítások és memória eltolások nem tudnak túlcsordulni.

USIZE_BOUND: 2^64

U32_BOUND: 2^32

index_no_usize_overflow: Egy tétel, amely bizonyítja, hogy ha egy index kisebb, mint egy méret, és az méret az USIZE_BOUND-on belül van, az index is biztonságos.

IEEE754Model és Pontosság Biztonság

A NsirNumericalSafety struktúra definiálja a Pontos Tartomány aritmetika határait.

withinExactRange: Érvényesíti, hogy egy érték belefér-e a 2^24 korláton belül (az egyszeres pontosságú lebegőpontosok pontossági korlátja, biztonsági pufferként használva).

safeAddition: Biztosítja, hogy a + b ne lépje túl a modell pontossági korlátait.

Memória Modell és Adat Folyam

A numerikus műveleteket egy MemoryMap-on belül hajtják végre, amely egy lineáris halom szimulációjaként szolgál. Ez lehetővé teszi a formális rendszer számára, hogy érveljen a mutatókról (indexek) és allokációkról, miközben fenntartja a tiszta funkcionális szemantikát.

Memória Műveletek:

memAlloc: Inicializál egy címtartományt egy alapértelmezett FP értékkel.

memRead / memWrite: Hozzáfér vagy frissíti a MemoryMap-et egy specifikus Nat címen.

memUpdate: Alkalmaz egy f: FP -> FP függvényt egy specifikus memória helyre.

Memória Helyességi Tételek

A rendszer bizonyítja a szabványos memória konzisztencia tulajdonságokat:

memRead_write_same: Olvasás egy címről közvetlenül írás után ugyanazt az értéket adja vissza.

memWrite_read_same: Írás egy címre és olvasás ugyanarról a címről visszaadja az írt értéket.

Előre és Hátra Modulációs Logika

Ez az oldal részletezi az NSIR (Nem-lineáris Önismétlő Információ Ábrázolás) modulációs logika implementációját, ahogy a Lean 4 formális modellben specifikálva van. Ez a szakasz felelős az információ feltételes skálázásáért a helyi statisztikai tulajdonságok (átlag) alapján, és kezeli az átmenetet a funkcionális lista ábrázolások és a pipeline-ban használt memória-leképezett ábrázolások között.

Memória Modell és Ábrázolás

A modulációs logika egy formális memória modellen működik, amely absztrakt hardver memóriát képez le egy funkcionális leképezésbe. Ez lehetővé teszi a rendszer számára, hogy hidat képezzen a tiszta funkcionális listák és a címezhető memória pufferek között.

Memória Struktúrák

MemoryMap: Nat → Option FP függvényként definiálva, képviselve a természetes szám címek opcionális fixpontos értékekhez való leképezését.

memAlloc: Inicializál egy memóriaterületet egy specifikus mérettel egy alapértelmezett FP értékkel.

memRead / memWrite: Szabványos hozzáférők a MemoryMap-hez. A memRead egy Option FP-t ad vissza, míg a memWrite egy új frissített MemoryMap-et ad vissza.

listToMem / memToList: Segédfüggvények, amelyek konvertálnak Lean natív List FP és a MemoryMap ábrázolás között, biztosítva a konzisztenciát a funkcionális logika és a pipeline memória állapota között.

Cím Tér Integritás

A rendszer érvényes memória tartományokat kényszerít ki a memValidRange segítségével, amely biztosítja, hogy a műveletek csak allokált szegmensek határain belül történjenek.

Előre Modulációs Logika (nsirForward)

Az előre passz kiszámítja a bemeneti lista átlagát, és nem-lineáris modulációs faktort alkalmaz azokra az elemekre, amelyek meghaladják ezt az átlagot. Ez egyfajta önismétlő megerősítést implementál az ábrázoláson belül.

Statisztikai Számítás

sumFP: Rekurzívan kiszámítja az összes FP érték összegét egy listában.

meanFP: Kiszámítja az átlagot az összeg elosztásával a lista hosszával (FP-re konvertálva a fromInt segítségével).

Modulációs Mechanizmus

gtFP: Egy összehasonlító függvény fixpontos értékekhez, amelyet annak meghatározására használnak, hogy egy érték meghaladja-e a küszöböt.

modulateValue: Ha egy v érték nagyobb, mint az m átlag, megszorozzák FP.modulationFactor-ral (konstans 1.05); különben változatlan marad.

modulateList: Leképezi a modulateValue-t a teljes bemeneti listán az előre kiszámított átlag használatával.

Hátra Modulációs Logika (nsirBackward)

A hátra passz tükrözi az előre passzt a gradiensek beállításához. Biztosítja, hogy a gradiens folyam arányosan legyen skálázva az előre modulációhoz, fenntartva a nem-lineáris transzformáció integritását az optimalizálás során.

Gradiens Beállítás

Az nsirBackward függvény elfogadja mind az eredeti aktivációkat (a feltétel újraértékeléséhez), mind a bejövő gradienseket.

1. Küszöb Újraértékelés: Újra kiszámítja az aktivációk átlagát.

2. Feltételes Gradiens Skálázás:

Ha az eredeti v aktiváció nagyobb volt az átlagnál, a megfelelő g gradiens megszorozzák FP.modulationFactor-ral.

Különben a g gradiens változatlanul halad át.

Ez a szimmetria biztosítja, hogy azokat az elemeket, amelyeket felerősítettek az előre passzban, arányosan nagyobb frissítésben részesülnek a hátra passz során.

Implementációs Összefoglaló

Kulcs függvények a modulációs pipeline-ban:

nsirForward - Előre Passz - ha v > átlag akkor v * 1.05 különben v

nsirBackward - Hátra Passz - ha v > átlag akkor grad * 1.05 különben grad

meanFP - Statisztika - összeg(lista) / hossz(lista)

modulateValue - Kulcs Skaláris Művelet - Feltételes skálázás modulationFactor használatával

listToMem - Interop - Feltölti a MemoryMap-et a List FP-ből

Pipeline Állapot Gép és Orkesztráció

Az NSIR modulációs pipeline-t formális állapot gépként implementálják a Lean 4 specifikáción belül. Orkesztrálja az adatok folyását több neurális hálózat szakaszon keresztül, miközben fenntartja a szigorú numerikus biztonságot és nyomon követhetőséget egy nyomkövetés-alapú naplózási rendszeren keresztül. Ez az orkesztráció biztosítja, hogy az előre és hátra passzok matematikai konzisztenciát tartsanak fenn a Természetes Nyelv Tér (szimbolikus ábrázolás) és a Kód Entitás Tér (fixpontos aritmetika és memória térképek) között.

Pipeline Komponensek és Szakaszok

A pipeline-t diszkrét szakaszok és fázisok halmaza definiálja, amelyek szabályozzák az információ transzformációját. A PipelineStage induktív típus definiálja a műveletek sorozatát, míg a TrainingPhase definiálja a rendszer operatív módját.

Pipeline Szakaszok:

Embedding (.Embedding): A bemeneti tokenek kezdeti vektorizálása a nagy dimenziós térbe.

OFTB (.OFTB): Ortogonális Funkcionális Transzformációs Blokk.

RSF (.RSF): Relációs Szemantikai Szűrő.

NSIR (.NSIR): Nem-lineáris Önismétlő Információ Ábrázolás moduláció.

Projection (.Projection): Végső leképezés a kimeneti dimenzióra (például szótár méret).

Képzési Fázisok:

Forward: Kiszámítja az aktivációkat és tárolja őket az activationMap-ben.

Backward: Kiszámítja a gradienseket a láncszabály használatával, tárolva a gradientMap-ben.

ZeroGrad: Visszaállít minden gradienset nullára egy új optimalizálási lépés előtt.

UpdateParams: Alkalmazza a kiszámított gradienseket a belső súlyok frissítésére.

Pipeline Állapot és Nyomon Követhetőség

A rendszer állapota a PipelineState struktúrában van kapszulázva, amely kezeli a memória térképeket az aktivációkhoz és gradiensekhez, egy stepCounter mellett és egy PipelineTrace-t a nyomon követhetőséghez.

Állapot Struktúra

A PipelineState tartalmazza:

activationMap: Egy MemoryMap (Nat → Option FP), amely közbenső értékeket tárol.

gradientMap: Egy MemoryMap, amely részleges deriváltakat tárol.

stepCounter: Egy Nat, amely nyomon követi a végrehajtási lépések számát.

trace: Egy PipelineTrace (PipelineEntry-k listája), amely rögzít minden állapot átmenetet.

Nyomon Követhetőség: PipelineEntry

Minden művelet a pipeline-on belül generál egy PipelineEntry-t, amely rögzíti:

A végrehajtott szakaszt.

A fázist (Előre/Hátra).

Egy időbélyeget (Nat lépésként képviselve).

Egy ellenőrző összeget az állapotról az adat integritás biztosításához.

Végrehajtási Logika és Szakasz Sorrend

A pipeline szigorú műveleti sorrendet kényszerít ki. Az Előre fázisban a szakaszoknak az Embedding-től a Projection-ig kell haladniuk. A Hátra fázisban a sorrend fordított.

Előre és Hátra Orkesztráció

A kulcs végrehajtási függvények, executeForward és executeBackward, szekvenciálisan hívják meg a stepPipeline-t minden szakaszhoz a definiált sorrendben.

Modulációs Lépések Implementációja

Amikor a stepPipeline függvény eléri a .NSIR szakaszt, a specifikus modulációs logikára diszpécserel.

Előre Moduláció: Az nsirForward függvény kiolvassa az értékeket az activationMap-ből, kiszámítja az átlagot, és alkalmazza a modulationFactor-t (1.05) az átlagot meghaladó értékekre.

Hátra Moduláció: Az nsirBackward függvény beállítja a gradienseket az eredeti előre aktivációk alapján, biztosítva, hogy a gradiens folyam tiszteletben tartsa az előre passz során alkalmazott nem-lineáris skálázást.

N Kör Végrehajtása

Az executeNRounds függvény biztosítja a magas szintű belépési pontot a képzéshez, iteratívan végrehajtva:

1. ZeroGrad fázis.

2. executeForward.

3. executeBackward.

4. UpdateParams fázis.

Szójegyzék

Ez az oldal átfogó hivatkozást nyújt a nsir_core tárházban használt terminológiához, matematikai koncepciókhoz és implementáció-specifikus zsargonhoz. Kiterjed mind a nagy teljesítményű Zig futásidejű környezetre, mind a formális Lean 4 specifikációra.

Alapvető Koncepciók

NSIR (Nem-lineáris Önismétlő Információ Ábrázolás): A Kognitív Relációs Motor (CRE) alapvető adatszerkezete. Információt ábrázol gráfként, ahol a csomópontok kvantumállapotokkal rendelkeznek, és az élek a kapcsolati összeköttetések különböző minőségeit képviselik.

Önismétlő Relációs Gráf: Az NSIR rendszer elsődleges konténere. Kezeli a csomópontok és élek gyűjteményét, fenntartva egy globális kvantum regisztert és egy topológia kivonatot az állapot integritás biztosításához.

Topológia Kivonat: Egy 64 karakteres hexadecimális karakterlánc, amely képviseli a gráf szerkezetének és adatainak egyedi állapotát. SHA-256 használatával számítják ki XOR-alapú akkumulációval, hogy biztosítsák, hogy a kivonat független legyen a csomópontok és élek beszúrási sorrendjétől.

Kvantumszámítási Kifejezések

Qubit: Egy normalizált két-komponensű komplex kvantumállapot, amelyet α (a) és β (b) amplitúdók képviselnek. A nsir_core-ban a qubitek automatikusan normalizálva vannak inicializáláskor, hogy biztosítsák, hogy a nagyságok négyzeteinek összege egyenlő legyen 1.0-val.

Bell Állapot (TwoQubit): Egy specifikus típusú összefonódott állapot, amely két qubitet érint. Az implementáció a Φ+ Bell állapotára fókuszál, amelyet négy komplex amplitúdó képvisel: amp00, amp01, amp10 és amp11.

Kvantum Kapu: Egy unitér művelet, amelyet egy Qubit-re alkalmaznak. Támogatott kapuk:

Hadamard (H): Szuperpozíciót hoz létre.

Pauli-X/Y/Z: Bit-flip, bit-és-fázis-flip és fázis-flip műveletek.

Phase Gate: Specifikus forgatást alkalmaz a fázisra.

Mérés (Összeomlás): A kvantumállapot megfigyelésének folyamata, amely kényszeríti azt egy klasszikus bázis állapotba (0 vagy 1). Az NSIR-ben egy összefonódott csomópont mérése szintén összeomlasztja a partnerét.

Adatszerkezet Definíciók

Node: Tartalmaz id-t, data-t, qubit állapotot, phase-t és egy metadata StringMap-et.

Edge: Összeköti a source-t a target-tel. Tartalmaz weight-et, quantum_correlation-t és fractal_dimension-t.

EdgeQuality: Enum: szuperpozíció, összefonódott, koherens, összeomlott, fraktál.

Complex: Struktúra re (valós) és im (imaginárius) lebegőpontos komponensekkel.

Modulációs Pipeline Zsargon

FP (Fixpontos): Egy egyedi fixpontos aritmetikai típus, amelyet a modulációs pipeline-ban használnak a numerikus stabilitás és determinizmus biztosítására. Egy egész szám alapot használ 10^8 skálával.

Modulációs Faktor: Egy konstans (1.05), amelyet az nsirForward passzban használnak azoknak az értékeknek a skálázására, amelyek meghaladják a jelenlegi aktivációs készlet átlagát.

Pipeline Szakaszok: A ML képzési pipeline műveleteinek sorozata:

1. Embedding: Kezdeti vektor ábrázolás.

2. OFTB: Ortogonális Funkció Transzform Blokk.

3. RSF: Relációs Struktúra Szűrő.

4. NSIR: Nem-lineáris Önismétlő Információ Ábrázolás moduláció.

5. Projection: Végső kimeneti leképezés.

Domain Specifikus Kifejezések

Arena/Pool/Buddy Allokátor: Különböző memóriakezelési stratégiák, amelyeket a Zig implementációban használnak a gráf életciklusához.

Kanonikus ID Mutató: Egy stratégia, ahol az élek mutatókat tárolnak a Node-ok által birtokolt ID karakterláncokhoz, hogy minimalizálják a memória duplikációt.

Xorshift Rng: Egy 64-bites pszeudo-véletlenszám generátor, amelyet a Lean 4 specifikációban használnak a kvantum mérés szimulálására.
