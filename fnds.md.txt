Fnds – Teljes dokumentáció (Magyar)

Áttekintés (Overview)

A Fractal Node Data Structure (**FNDS**) könyvtár egy specializált Zig nyelvű implementáció, amelyet hierarchikus, önhasonló adatmodellek kezelésére terveztek. A hagyományos lapos gráfoktól vagy merev fáktól eltérően az **FNDS** rekurzív rétegekbe szervezi az adatokat, ahol minden csomópont egyszerre képvisel egy adatpontot és egy alstruktúrát. Ez az architektúra olyan rendszerekre van optimalizálva, amelyek fraktáldimenzió-analízist, többskálájú mintaillesztést és hierarchikus kapcsolatok nagy teljesítményű gyorsítótárazását igénylik.

A könyvtár három alapelven nyugszik:

Önhasonlóság (Self-Similarity): Az adatok indexelése és tárolása oly módon történik, hogy a rendszer felismerhesse a mintákat a hierarchia különböző skálái között.

Fraktálanalízis (Fractal Analysis): Beépített algoritmusok számítják ki az adatklaszterek fraktáldimenzióját a komplexitás és az információsűrűség mérésére.

Nagyméretű teljesítmény (Performance at Scale): Egyedi, memóriahatékony struktúrák, mint a CoalescedHashMap és az integrált LRUCache teszik lehetővé a hatalmas adatkészletek minimális overheaddel való kezelését.

 Alapkomponensek

FNDSManager: A könyvtár legfelső szintű belépési pontja. Több FractalTree és SelfSimilarIndex példány nyilvántartójaként működik. Kezelési feladatokat lát el, mint a globális statisztikák nyomon követése az FNDSStatistics segítségével, és egységes keresési felületet biztosít egy belső LRUCache által támogatva.

FractalTree és FractalLevel: A FractalTree egyetlen hierarchikus adatkészletet képvisel. A csomópontokat FractalLevel szeletekbe particionálja skálájuk és mélységük alapján. A fa automatikusan kezeli az egyensúlyozást és a mélységoptimalizálást.

SelfSimilarIndex: A fizikai fastruktúrától függetlenül a SelfSimilarIndex mintaalapú lekérést tesz lehetővé. A PatternLocation segítségével karakterlánc-alapú mintákat képez le konkrét koordinátákra (fa azonosító, szint, csomópont azonosító) a rendszeren belül.

 Tervezési elvek

Manuális memóriafegyelem: Minden fontosabb struktúra implementálja az init, deinit és clone mintákat, explicit memória-életciklus-vezérléshez a std.mem.Allocator interfész segítségével.

Kriptográfiai azonosság: A csomópontok fractal_signature-t kapnak Sha256 használatával, biztosítva az adatok integritását és az egyedi azonosítást elosztott kontextusokban.

Matematikai szigor: A könyvtár natív támogatást nyújt a fraktáldimenziók kiszámításához dobozszámláló (box-counting) algoritmusokkal.

Egyedi gyűjteménytípusok: A nagy ütközési forgatókönyvekben a standard könyvtári implementációk overheadjének elkerülése érdekében az **FNDS** egy CoalescedHashMap-et használ belső tároláshoz.

---

 Bevezetés (Getting Started)

 Előfeltételek és függőségek

Az **FNDS** a Zig standard könyvtárra és egy alapvető függőségre támaszkodik a relációs gráftípusokhoz.

Zig verzió: Kompatibilis a legújabb Zig toolchain-ekkel (std.crypto.hash.sha2, std.hash.Wyhash, std.fifo használatával).

nsir_core.zig: Ennek a fájlnak az fnds.zig fájllal azonos könyvtárban kell lennie. Megadja az Node, Edge és SelfSimilarRelationalGraph alapvető típusokat, amelyeket az **FNDS** újraexportál.

Allocator: Az **FNDS** minden fontosabb struktúrája megkövetel egy std.mem.Allocator-t a manuális memóriakezeléshez, az init/deinit mintát követve.

 Integrációs folyamat

## Importálás és inicializálás

Az importáláshoz használd az fnds.zig fájlt. A könyvtár elsődleges belépési pontja az FNDSManager. Ez a manager több fraktálfa életciklusát kezeli, fenntart egy globális **LRU**-gyorsítótárat a keresési teljesítményhez, és nyomon követi a rendszerszintű statisztikákat.

## FractalTree létrehozása

A FractalTree egy hierarchikus konténer, ahol az adatokat skálájuk és elágazási tényezőik alapján szintekbe szervezik. A fát a manageren keresztül hozod létre, amely egy egyedi 32 bájtos tree_id-t ad vissza.

## Csomópontok beillesztése

A csomópontokat egy adott fába az insertIntoTree segítségével illeszted be. A rendszer automatikusan a megfelelő FractalLevel-re irányítja a csomópontot a csomópont adatainak Wyhash-e és a fa elágazási logikája alapján.

## Keresés és lekérés

A searchInTree metódus iteratív keresést végez a fa szintjein keresztül. Az FNDSManager egy LRUCache-sel egészíti ki ezt a keresést az azonos node_id ismételt keresésének gyorsítása érdekében.

 Alapvető műveletek összefoglalója

| Művelet | Függvény | Fő viselkedés |
|---|---|---|
| Inicializálás | FNDSManager.init | Lefoglalja az LRUCache-t és a trees map-et. |
| Fa létrehozása | FNDSManager.createTree | Véletlenszerű tree_id-t generál és inicializál egy FractalTree-t. |
| Csomópont beillesztése | FractalTree.insert | Rekurzívan megtalálja a helyes FractalLevel-t computeChildIndex használatával. |
| Keresés | FNDSManager.searchInTree | Először az LRUCache-t ellenőrzi; hiány esetén meghívja a FractalTree.searchLevel-t. |
| Felszabadítás | deinit | Minden struktúrát (FractalTree, FractalLevel, FractalNodeData) deinicializálni kell a lefoglalt karakterláncok és map-ek felszabadításához. |

---

 Architektúra áttekintése (Architecture Overview)

Az **FNDS** könyvtár háromrétegű hierarchikus architektúrára épül, amelyet többdimenziós, önhasonló adatok kezelésére terveztek. A rendszer a magas szintű kezelési regisztertől az egyes fa horizontális szeletéig halad, fraktálgeometria elveket alkalmazva az adatszervezéshez és lekéréshez.

 Rendszerhierarchia és adatfolyam

Az architektúra a következő rétegekből áll:

FNDSManager: A legfelső szintű orchestrátor és regiszter. Több FractalTree és SelfSimilarIndex példányt kezel, kezeli a globális statisztikákat, és **LRU**-gyorsítótárazási réteget biztosít a keresések gyorsítására.

FractalTree: Egy vertikális konténer, amely egy teljes hierarchikus adatkészletet képvisel. Kezeli a FractalLevel szeletek életciklusát, és elvégzi a szerkezeti műveleteket, mint az egyensúlyozás és a rekurzív bejárás.

FractalLevel: A fa horizontális szelete egy adott mélységben. Az FractalNodeData és FractalEdgeData elsődleges tárolásaként szolgál, és helyi geometriai számításokat végez, mint a dobozszámlálás a fraktáldimenzió becsléséhez.

 1. réteg: FNDSManager (Regiszter és Orchestráció)

Az FNDSManager a könyvtár belépési pontjaként szolgál. Fenntart egy StringHashMap-et a fákról és az indexekről, lehetővé téve a több-bérlős vagy több-kontextusú adattárolást.

- Regiszter: A trees-t és az indices-t egyedi karakterlánc-azonosítók alapján kezeli.
- Gyorsítótárazás: Implementál egy LRUCache-t, amely FractalNodeData mutatókat tárol. Összetett kulcsot használ, amelyet a buildCacheKey generál a tree_id és node_id kombinálásával.
- Statisztikák: Minden műveletnél frissíti az FNDSStatistics-t, nyomon követve a gyorsítótár-találati arányokat és a teljes memóriahasználatot.

 2. réteg: FractalTree (Hierarchikus konténer)

A FractalTree mélységalapú hierarchiába szervezi az adatokat. branching_factor-t és max_depth-t használ annak meghatározásához, hogyan oszlanak el a csomópontok a szintek között.

- Útválasztás: Az insert hívásakor a fa kiszámítja a célszintet és a computeChildIndex-et használja (Wyhash-en keresztül) a csomópont elhelyezésének meghatározásához.
- Egyensúlyozás: A checkBalance metódus figyeli a fa állapotát. Ha a mélység nem optimális, a balance() műveletet indítja el, amely összegyűjti az összes csomópontot és újraépíti a szinteket.
- Bejárás: Több sorrendet támogat (Preorder, Postorder, Szintsorend, Fraktálsorend) a hierarchián belüli csomópontok látogatásához.

 3. réteg: FractalLevel (Horizontális szelet)

A FractalLevel a szerkezeti szervezés atomi egysége. Minden szint egy adott *nagyítást* vagy *skálát* képvisel a fraktálban.

- Tárolás: StringHashMap-et használ az adott mélységhez tartozó nodes és edges tárolásához.
- Geometriai analízis: Implementálja a computeLocalFractalDimension-t dobozszámláló algoritmus segítségével. Becsüli az adateloszlás komplexitását a szinten belül.
- Szomszédosság: Kezeli a FractalEdgeData-t, amely hierarchical, sibling, cross_level vagy self_similar kapcsolatokat definiálhat csomópontok között.

 Belső teljesítményalrendszer: CoalescedHashMap

Nagy párhuzamossági és nagy terhelési forgatókönyvek támogatásához az architektúra egyedi CoalescedHashMap-et használ a belső indexeléshez. A standard hash map-ekkel ellentétben egy *pince* (cellar) területet használ az ütközések kezelésére, csökkentve a keresési sorozat hosszát.

| Funkció | Implementáció részlete |
|---|---|
| Ütközési stratégia | Pince-alapú összeolvasztásos hashing |
| Pince arány | Az összes kapacitás 14%-a |
| Terhelési tényező | Max. 0,86 |

---

 Alapvető adatstruktúrák (Core Data Structures)

Ez az oldal a Fractal Node Data Structure (**FNDS**) alapvető adattípusainak áttekintését nyújtja. A könyvtár hierarchikus, skálaállandó architektúra köré szervez, ahol az adatok csomópontokban tárolódnak, élekkel vannak összekötve, és szintekbe particionálva helyezkednek el egy fában.

 Alapegységek: Csomópontok és élek

A rendszer legalacsonyabb szintjén két primitív adatstruktúra található: FractalNodeData és FractalEdgeData.

FractalNodeData az információ egyetlen pontját képviseli. A standard azonosító- és adatmezőkön túl tartalmaz egy fractal_signature-t (**SHA**-**256** hash) és egy scale tényezőt, amelyet a hierarchiában elfoglalt pozíciójának meghatározásához használnak. Dinamikus metadata-t is támogat egy StringHashMap-en keresztül.

FractalEdgeData két csomópont közötti kapcsolatot definiál. Az EdgeType enummal kategorizálja a kapcsolatokat, megkülönböztetve a hierarchical, sibling, cross_level és self_similar kapcsolatokat. Nyomon követi a scale_ratio-t és a fractal_correlation-t annak számszerűsítéséhez, hogyan maradnak fenn a kapcsolatok a fa különböző szintjein.

 Szerkezeti konténerek: Szintek és fák

| Struktúra | Cél | Kulcsmezők |
|---|---|---|
| FractalNodeData | Atomi adategység | id, fractal_signature, scale, metadata |
| FractalEdgeData | Kapcsolategység | source_id, target_id, edge_type, scale_ratio |
| FractalLevel | Skálaspecifikus szelet | level_index, scale_factor, nodes, child_levels |
| FractalTree | Hierarchikus manager | max_depth, branching_factor, root_level |

---

 FractalNodeData és FractalEdgeData

 FractalNodeData

A FractalNodeData az FractalTree-n belüli információ elsődleges konténere.

Mezőspecifikációk:

| Mező | Típus | Leírás |
|---|---|---|
| id | []const u8 | A csomópont egyedi azonosítója. |
| data | []const u8 | A csomópontban tárolt tényleges tartalom vagy adat. |
| weight | f64 | A csomópont numerikus fontossága vagy nagysága. |
| scale | f64 | A fraktálskála, amelyen ez a csomópont létezik. |
| fractal_signature | [32]u8 | SHA-256 hash, amely a csomópont egyedi állapotát képviseli. |
| children_count | usize | Az ehhez a csomóponthoz kapcsolódó gyermekcsomópontok száma. |
| metadata | StringHashMap([]const u8) | Kulcs-érték tároló bővíthető attribútumokhoz. |

Fraktál-aláírás kiszámítása: Az inicializálás során az init-en keresztül a rendszer létrehoz egy fractal_signature-t. Ez egy kriptográfiai ujjlenyomat, amelyet a fa különböző szintjein az adatok integritásának és azonosságának ellenőrzésére használnak. Az aláírást a std.crypto.hash.sha2.Sha256 segítségével számítják ki, frissítve a hasher-t a következő mezőkkel: id, data, weight (bájtokként), scale (bájtokként).

Memóriakezelés és életciklus:
- Az init mély másolatokat végez az id és data stringekből allocator.dupe használatával, és inicializálja a metadata hash map-et.
- A clone metódus teljesen független másolatot készít a csomópontról, beleértve az összes metadata kulcs és érték mély másolatát.
- A deinit felszabadítja az id-t, a data-t, és végigjárja a metadata map-et minden tárolt kulcs és érték felszabadításához.

Gyors hashelés Wyhash-sel: A fractal_signature **SHA**-**256**-ot használ kriptográfiai egyediséghez, a computeHash metódus std.hash.Wyhash-t alkalmaz. Ez teljesítmény-kritikus műveletekhez, például gyorsítótár-kulcs generáláshoz és fa-útválasztáshoz használatos.

 FractalEdgeData

Mezőspecifikációk:

| Mező | Típus | Leírás |
|---|---|---|
| source_id | []const u8 | A kiindulási csomópont azonosítója. |
| target_id | []const u8 | A célcsomópont azonosítója. |
| weight | f64 | A kapcsolat erőssége. |
| scale_ratio | f64 | A forrás- és célcsomópontok skáláinak aránya. |
| edge_type | EdgeType | A kapcsolat kategorizálása. |
| fractal_correlation | f64 | Az él önhasonlóságának statisztikai mértéke. |

EdgeType enum:
- hierarchical: Szülő-gyermek kapcsolat.
- sibling: Azonos szinten lévő csomópontok közötti kapcsolat.
- cross_level: Nem szomszédos szinteket átívelő kapcsolat.
- self_similar: Speciális link, amely rekurzív mintaillesztést jelöl.

---

 FractalLevel

A FractalLevel struktúra a FractalTree horizontális szeletét képviseli egy adott mélységben. Térbeli adatok (csomópontok és élek) elsődleges konténereként szolgál egy adott felbontáson vagy skálán.

 Alapstruktúra és mezők

| Mező | Típus | Leírás |
|---|---|---|
| level_index | usize | Ennek a szintnek a mélysége a FractalTree-n belül (0 a gyökér). |
| scale_factor | f64 | A felbontás szorzója ezen a szinten, általában csökkenő mélységgel. |
| nodes | StringHashMap(FractalNodeData) | Csomópontok tárolása, egyedi id alapján indexelve. |
| edges | StringHashMap(FractalEdgeData) | Élek tárolása, összetett azonosító alapján indexelve. |
| parent_level | ?FractalLevel | Opcionális mutató a felette lévő szintre. |
| child_levels | ArrayList(FractalLevel) | Ebből a szeletből elágazó szintek dinamikus listája. |
| allocator | Allocator | Hivatkozás az allocator-ra a memóriakezeléshez. |

 Csomópont- és élműveletek (**CRUD**)

Csomópontkezelés:
- addNode(node: FractalNodeData): Csomópontot illeszt be a nodes map-be. Ha azonos azonosítójú csomópont már létezik, azt felváltja és a régi csomópont memóriáját felszabadítja.
- getNode(id: []const u8): Visszaad egy opcionális mutatót a csomópont adataira.
- removeNode(id: []const u8): Eltávolítja a csomópontot és egy boolean-t ad vissza, amely jelzi a sikert.

Élkezelés:
- addEdge(edge: FractalEdgeData): Az addNode-hoz hasonlóan kezeli az él beillesztését. Egyedi kulcsot épít az edges map-hez a forrás- és célazonosítók alapján.
- getEdge(source_id: []const u8, target_id: []const u8): Lekér egy élt a kapcsolati pár alapján.

 Fraktáldimenzió kiszámítása

A FractalLevel egyik elsődleges szerepe a lokális fraktáldimenziójának kiszámítása. Ez egy dobozszámláló algoritmussal valósul meg, amely becsüli, hogyan változik a *részlet* (csomópont-sűrűség) különböző skálákon.

A computeLocalFractalDimension metódus log-log lineáris regressziót (legkisebb négyzetek módszerét) implementál a skála és a *foglalt dobozok* száma közötti összefüggésen:
- Rögzített dobozméreteken iterál: {1.0, 2.0, 4.0, 8.0}.
- Minden mérethez meghívja az estimateBoxCount(box_size)-t.
- Kiszámítja a log(1/r) vs log(N(r)) regresszió meredekségét, ahol r a dobozméret és N(r) a szám.

 Bejárási és statisztikai segédprogramok

- getTotalNodeCount(): Rekurzívan összegzi a csomópontok számát ezen a szinten és az összes child_levels-ben.
- getMaxDepth(): Meghatározza az ettől a szelettől elérhető legmélyebb szintet.

---

 FractalTree

A FractalTree az **FNDS** könyvtár elsődleges hierarchikus konténere. Többrétegű struktúrát kezel, amelyet FractalLevel példányok alkotnak.

 Inicializálás és konfiguráció

| Paraméter | Típus | Leírás |
|---|---|---|
| max_depth | usize | A fa növekedési szintjeinek kemény korlátja. |
| branching_factor | usize | A csomópontonkénti gyermekek célszáma, az útválasztáshoz és egyensúlyozáshoz. |
| scale_factor | f64 | A gyökérszinthez rendelt kezdeti skála (általában 1.0). |

 A beillesztési folyamat

A FractalTree-be való beillesztés determinisztikus folyamat, amely hashelést alkalmaz a csomópontok konkrét szintekre és gyermekindexekre irányításához:

## Szintválasztás: A fa a 0. szintről indul.

## Gyermekindex kiszámítása: A rendszer computeChildIndex-et alkalmaz, amely a Wyhash algoritmust alkalmazza a csomópont azonosítójára. ## Dinamikus lefoglalás: Ha egy szükséges gyermekszint nem létezik, a fa dinamikusan lefoglal egy új FractalLevel-t. ## Skálacsökkentés: Ahogy a csomópontok mélyebbre kerülnek a fában, a scale_factor-uk a parent_scale / branching_factor képlettel csökken. ## Perzisztencia: A csomópont a célszint nodes map-jébe kerül tárolásra.

 Keresési stratégia

A search metódus egy iteratív felületet biztosít a csomópontok megtalálásához. Belsőleg a searchLevel-t hívja meg, amely Depth-First Search (**DFS**) keresést végez a szinteken. Először az aktuális szint nodes map-jét ellenőrzi, majd rekurzívan a child_levels-be megy a célcsomópont azonosítójának determinisztikus hash-indexe alapján.

 Bejárási stratégiák

A FractalTree négy különböző TraversalOrder módot támogat:

| Stratégia | Logika |
|---|---|
| pre_order | Meglátogatja az aktuális csomópontot, majd rekurzívan a gyermekekbe megy. |
| post_order | Rekurzívan végigmegy az összes gyermeken, mielőtt meglátogatná az aktuális csomópontot. |
| level_order | Breadth-First Search (BFS) egy std.fifo.LinearFifo sor használatával. |
| fractal_order | Nemlineáris bejárás: meglátogatja a gyökeret, rekurzívan végigmegy az első fél gyermeken előre, majd a második felet fordítva. |

 Egyensúly életciklusa

A teljesítményromlás (fa-torzulás) megelőzése érdekében a FractalTree figyeli a saját szerkezeti állapotát:

- Minden **100** beillesztésnél meghívja a checkBalance()-t.
- Az computeOptimalDepth formula logaritmikus megközelítést használ: log(total_nodes) / log(branching_factor).
- Ha a jelenlegi mélység lényegesen eltér az optimálistól, teljes rekonstrukció indul.

 Fraktáldimenziók aggregálása

A computeFractalDimension metódus a fa strukturális komplexitásának mértékét adja. Összesíti az összes alkotó FractalLevel lokális fraktáldimenzióit, és visszaadja az átlagos dimenziót az összes nem üres szinten.

---

 Indexelés és mintaillesztés (Indexing and Pattern Matching)

Az Indexelés és Mintaillesztés alrendszer mechanizmust biztosít az adatok fizikai fa-koordinátáktól független, szerkezeti vagy tartalom-alapú mintákon alapuló lekéréséhez. Ez az alrendszer két fő komponensre támaszkodik:

SelfSimilarIndex: Az a kezelési struktúra, amely tárolja a mintákat és hasonlóság-alapú kereséseket végez.

PatternLocation: Egy metaadatstruktúra, amely egy felfedezett mintát visszaképez konkrét fizikai helyére egy FractalTree-n belül.

 PatternLocation

A PatternLocation adatstruktúra pontos mutatóként szolgál, amely összekapcsol egy specifikus adatmintát (amelyet egy SelfSimilarIndex-ben tárolnak) annak fizikai megnyilvánulásával egy FractalTree-n belül.

| Mező | Típus | Leírás |
|---|---|---|
| tree_id | [32]u8 | A mintát tartalmazó FractalTree egyedi azonosítója. |
| level | usize | A mélység (FractalLevel) a fán belül, ahol a csomópont található. |
| node_id | []const u8 | Az adott FractalNodeData egyedi azonosítója. |
| offset | usize | A minta kezdő bájtpozíciója a csomópont data mezőjén belül. |
| length | usize | A minta hossza bájtokban. |
| confidence | f64 | Egy 0.0 és 1.0 közötti pontszám, amely a mintaillesztés megbízhatóságát jelöli. |

---

 SelfSimilarIndex

A SelfSimilarIndex egy specializált indexelési struktúra mintaalapú lekéréshez az **FNDS** könyvtáron belül. Tartalmalapú felfedezést tesz lehetővé, karakterlánc-mintákat képezve le egy vagy több FractalTree példányon belüli előfordulásaikra.

 Alapimplementáció

Adatstruktúra mezők:
- patterns: StringHashMap(ArrayList(PatternLocation)) - egy adott karakterlánc-mintát leképez az összes fizikai előfordulásának listájára.
- similarity_threshold: f64 érték (általában 0.0 és 1.0 között), amelyet arra használnak, hogy meghatározzák, két minta elég hasonló-e a homályos keresésekhez.
- dimension_estimate: f64, amely az indexelt minta-eloszlás számított fraktáldimenzióját képviseli.
- pattern_keys: ArrayList([]const u8) - a hasonlóság kiszámítása során az iterációhoz használt kulcsokat tárolja.

 Mintakezelés

Hozzáadás (addPattern): Ellenőrzi, hogy a minta létezik-e a patterns map-ben. Ha igen, végigiterálja a meglévő PatternLocation bejegyzéseket, hogy megakadályozza az ismétlődő bejegyzéseket ugyanarra a node_id-re és offset-re.

Eltávolítás (removePattern): Eltávolítja a megadott PatternLocation-t az indexből. Ha az eltávolított helyszín volt az utolsó egy mintához kapcsolódó, magát a mintát is eltávolítja.

 Mintakeresés és hasonlóság

Pontos keresés (findPattern): Konstans idejű keresést végez a patterns StringHashMap-ben. Visszaad egy opcionális PatternLocation objektumszeleget.

Homályos illesztés (findSimilarPatterns): Végigiterálja az összes regisztrált pattern_keys-t és kiszámít egy hasonlósági pontszámot a célszöveghez képest. A belső computeSimilarity segédfüggvény két tényező alapján számít arányt: a hosszarány és az elempozíció egyezése alapján. Ha az eredmény meghaladja a similarity_threshold-ot, a minta helyszínei hozzáadódnak az eredményhalmazhoz.

 Matematikai analízis: Fraktáldimenzió

A computeFractalDimension metódus az indexelt adatok komplexitását becsüli a mintahosszak eloszlásának elemzésével, log-log regressziót (legkisebb négyzetek módszere) alkalmazva: ## Eloszlás gyűjtése: Megszámolja az egyes egyedi hosszúságú minták előfordulásait. ## Log-log leképezés: Minden L hosszú, N frekvenciájú mintához kiszámítja az x = ln(L) és y = ln(N) értéket. ## Lineáris regresszió: Kiszámítja a legjobban illeszkedő vonal meredekségét, amely a mintaeltér fraktáldimenzióját képviseli.

| Függvény | Komplexitás | Leírás |
|---|---|---|
| addPattern | O(N) | Hozzáad egy PatternLocation-t; N az adott mintán lévő helyek száma. |
| findPattern | O(1) | Pontos keresés StringHashMap-en keresztül. |
| findSimilarPatterns | O(K  L) | K = összes egyedi minta, L = átlagos mintahossz. |
| computeFractalDimension | O(K + D) | K = összes egyedi minta, D = különböző hosszok száma. |

---

 FNDSManager: Központi regiszter és orchestráció

Az FNDSManager a legfelső szintű belépési pont és a könyvtár központi regisztere. Egységes felületet biztosít több fraktálfa és index kezeléséhez, miközben belső alrendszereket, például az **LRU**-gyorsítótárat és a globális statisztika-nyomon követést koordinálja.

 Alapvető felelősségek

Regiszterkezelés: Egyedi azonosítók és FractalTree és SelfSimilarIndex példányok közötti leképezés fenntartása.

Teljesítmény-orchestráció: Egy globális LRUCache kezelése a keresési műveletek gyorsítására az összes regisztrált fán.

Megfigyelhetőség: Valós idejű mérőszámok összesítése az FNDSStatistics objektumba a rendszer állapotának és teljesítményének figyelésére.

 Fa- és indexkezelés

| Művelet | Kódentitás | Leírás |
|---|---|---|
| Inicializálás | init | Beállítja a managert alapértelmezett LRUCache-sel (1000 kapacitás, 10 MB korlát). |
| Fa létrehozása | createTree | Véletlenszerű azonosítót generál és inicializál egy új FractalTree-t. |
| Index létrehozása | createIndex | Inicializál egy SelfSimilarIndex-et mintaalapú lekéréshez. |
| Adatok beillesztése | insertIntoTree | Az adatokat a konkrét fára irányítja és frissíti a globális statisztikákat. |
| Adatok lekérése | searchInTree | Gyorsítótárazott keresést végez, mielőtt a fa bejárásához folyamodna. |

 Teljesítmény és statisztikák

Minden a manageren keresztül végzett műveletnél az FNDSStatistics alrendszerben frissítés történik. A manager számos mezőt követ nyomon:
- Gyorsítótár teljesítmény: cache_hits, cache_misses, és cache_hit_ratio.
- Szerkezeti egészség: average_tree_depth és total_nodes_across_trees.
- Erőforráshasználat: memory_used és last_operation_time_ns.

---

 FNDSManager **API** referencia

 Inicializálás és konfiguráció

Az FNDSManager egy alapértelmezett LRUCache konfigurációval inicializálódik:

| Paraméter | Alapértelmezett érték | Leírás |
|---|---|---|
| Kapacitás | 1000 bejegyzés | Az LRU-ban tárolt egyedi keresési eredmények maximális száma. |
| Maximális memória | 10 MB | A gyorsítótárazott csomópontadatokhoz lefoglalt maximális heap memória. |

 Core **API** metódusok

createTree(max_depth, branching_factor): Új FractalTree-t generál egyedi 32 bájtos azonosítóval. Kriptográfiai biztonságú véletlenszerű azonosítót generál std.crypto.random használatával, és hozzáadja a fát a trees map-hez.

getTree(tree_id): Mutatót ad vissza egy FractalTree-re a 32 bájtos azonosítója alapján. null-t ad vissza, ha a fa nem létezik.

removeTree(tree_id): Eltávolítja a fát a regiszterből és meghívja a deinit() metódusát az összes kapcsolódó memória felszabadításához.

insertIntoTree(tree_id, node_data): Csomópontot irányít egy konkrét fára hierarchikus beillesztéshez. Növeli a total_nodes_across_trees-t és frissíti a last_operation_time_ns-t.

searchInTree(tree_id, node_id): Gyorsítótárazott csomópontkeresést végez: ## Meghívja a buildCacheKey-t egy 64 bájtos összetett kulcs létrehozásához. ## Ha a csomópont a gyorsítótárban van, rögzíti a cache_hit-et és visszaad egy klónozott másolatot. ## Gyorsítótár-hiány esetén iteratív keresést végez a FractalTree-n belül, és az eredményt hozzáadja a gyorsítótárhoz.

computeGlobalFractalDimension(): Az összes aktív FractalTree példány és az SelfSimilarIndex minták dimenzióinak aritmetikai átlagát számítja ki.

 Belső regiszterstruktúra

| Mező | Típus | Szerepkör |
|---|---|---|
| trees | StringHashMap(FractalTree) | 32 bájtos fa azonosítókat képez le heap-allokált FractalTree példányokra. |
| indices | StringHashMap(SelfSimilarIndex) | Neveket képez le SelfSimilarIndex példányokra mintaillesztéshez. |
| stats | FNDSStatistics | Nyomon követi a számlálókat (találatok, hiányok, memória, csomópontszámok). |
| cache | LRUCache | A CoalescedHashMap alapú gyorsítótár a keresési eredményekhez. |

---

 FNDSStatistics

Az FNDSStatistics egy specializált struktúra az **FNDS** könyvtáron belül, amelyet valós idejű telemetria és teljesítményfigyelés biztosítására terveztek az FNDSManager számára.

 Adatmezők

| Mező | Típus | Leírás |
|---|---|---|
| total_trees | usize | A kezelt FractalTree példányok teljes száma. |
| total_indices | usize | A kezelt SelfSimilarIndex példányok teljes száma. |
| cache_hits | usize | Sikeres keresések száma az LRUCache-ben. |
| cache_misses | usize | Sikertelen keresések száma, amelyek teljes fa-bejárást igényeltek. |
| average_tree_depth | f64 | Az összes aktív fraktálfa átlagos mélysége. |
| memory_used | usize | Becsült teljes memóriafogyasztás bájtokban. |
| total_nodes_across_trees | usize | Az összes kezelt fában lévő csomópontok halmozott száma. |
| total_patterns_indexed | usize | Az összes indexben tárolt minták teljes száma. |
| cache_hit_ratio | f64 | A találatok és az összes keresés aránya (0.0-tól 1.0-ig). |
| last_operation_time_ns | i64 | A legutóbbi művelet végrehajtási ideje nanoszekundumokban. |

 Statisztikai frissítési logika

- recordCacheHit() / recordCacheMiss(): Egyszerű növelők a nyers számlálókhoz.
- updateCacheHitRatio(): Kiszámítja a találati arányt. Ha az összes keresés nulla, akkor alapértelmezetten 0.0, hogy elkerülje a nullával való osztást.
- updateAverageTreeDepth(): Elfogad egy szeleteket az összes fa mélységéből. Összegzést végez és az összes fával elosztva frissíti a globális átlagot.

---

 Teljesítményalrendszerek (Performance Subsystems)

A rendszer két elsődleges alrendszerre támaszkodik az összetett fraktálbejárások és nagy frekvenciájú keresések hatékonyságának biztosítása érdekében: egy specializált LRUCache a fa-csomópontok lekéréséhez és egy egyedi CoalescedHashMap az ütközés-ellenálló tároláshoz.

| Funkció | LRUCache | CoalescedHashMap |
|---|---|---|
| Elsődleges cél | Fa-bejárás minimalizálása | Hatékony kulcs-érték tárolás |
| Kiürítés | LRU (Legrégebben Használt) | Nincs (Terhelésnél átméretez) |
| Ütközési stratégia | Hash-map alapú | Pince-alapú összeolvasztásos láncolás |
| Memóriakorlát | Kemény korlát (pl. 10MB) | Dinamikus (Adatokkal növekszik) |
| Kulcs típusa | [64]u8 (Összetett) | Generikus K |

---

 LRUCache

Az LRUCache egy teljesítmény-kritikus alrendszer az FNDSManager-en belül, amelyet az ismételt teljes fa-bejárások számítási költségének csökkentésére terveztek.

 Keresési és gyorsítótár-életciklus adatfolyama

Amikor az FNDSManager.searchInTree kerül meghívásra, a rendszer először megpróbálja feloldani a kérést a gyorsítótáron keresztül:

## Kulcs generálás: A tree_id és node_id kombinálódik egy 64 bájtos összetett kulcsba a buildCacheKey segítségével.

## Keresés:
    - Találat: Az FNDSStatistics.recordCacheHit kerül meghívásra, a csomópont a *legutóbb használt* pozícióba kerül, és egy klónozott másolat kerül visszaadásra.
    - Hiány: Az FNDSStatistics.recordCacheMiss kerül meghívásra. A manager elvégzi az FractalTree.searchLevel bejárást.
## Feltöltés: Ha a csomópont a bejárás során megtalálható, az LRUCache.put-on keresztül kerül be a gyorsítótárba.

 Kulcskomponensek és implementáció

Összetett kulcskonstrukció: A gyorsítótár egy 64 bájtos egyedi azonosítót használ a különböző fákban lévő azonos csomópontazonosítók közötti ütközések megelőzésére. Inicializál egy 64 bájtos puffert a tree_id-vel, majd a node_id-n std.hash.Wyhash-t alkalmaz egy 64 bites hash generálásához.

Kettős kiürítési szabályzat: A gyorsítótár két mérőszámot követ a kiürítés indításához:
- capacity: Maximum bejegyzések száma (alapértelmezetten **1000**).
- max_memory: Maximum bájtok a csomópontadatokhoz (alapértelmezetten **10MB**).

Kiürítési folyamat: A kiürítési folyamat végigiterálja a entries map-et, hogy megtalálja a minimális last_access értékű csomópontot, majd: kivonja a csomópont memória-lábnyomát a current_memory-ból, meghívja a deinit()-t az FractalNodeData-n, eltávolítja a kulcsot a entries hash map-ből.

 Függvény referencia

| Függvény | Leírás |
|---|---|
| init(allocator, capacity, max_memory) | Inicializálja a gyorsítótárat a megadott korlátokkal. |
| get(key) | Lekér egy csomópontot és frissíti a last_access időbélyegét. |
| put(key, value) | Beilleszt egy csomópontot, esetleg a legrégebbi bejegyzés kiürítését indítva el. |
| evict() | Belső segédfüggvény, amely eltávolítja a legrégebbi last_access idejű bejegyzést. |

---

 CoalescedHashMap

A CoalescedHashMap egy egyedi, magas teljesítményű generikus hash map implementáció az **FNDS** könyvtárban. A standard nyílt-címzési hash map-ekkel ellentétben pince-alapú összeolvasztásos hashing stratégiát alkalmaz.

 Alapstruktúra és stratégia

A map belső tárolóját két különálló régióra osztja: Cím-régió (elsődleges vödrök) és Pince (túlcsordulási tároló). Amikor egy ütközés történik egy elsődleges vödörben, az implementáció keresi a pincében egy üres helyet az új bejegyzés elhelyezéséhez, és az elsődleges vödör láncához csatolja.

Kulcsállandók és konfiguráció:

| Állandó | Érték | Leírás |
|---|---|---|
| CELLAR_RATIO | 0.14 (14%) | Az összes kapacitásból a pincéhez fenntartott százalék. |
| DEFAULT_MAX_LOAD_FACTOR | 0.86 | A küszöb, amelynél egy teljes átméretezés indul el. |

CoalescedEntry struktúra: Minden bejegyzés CoalescedEntry-ként kerül tárolásra, amely nyomon követi az adatokat és a lánc metaadatokat: key, value, next_index (opcionális index az ütközési láncban a következő elemre mutatva), is_primary (jelzi, hogy a bejegyzés a természetes hash-levezetett vödrében van-e).

 Implementációs logika

A Put algoritmus:
1. std.hash.Wyhash segítségével 64 bites hash-t generál a kulcsból.
## A hash-t az indexelhető régión belüli indexre képezi le.
## Ha az elsődleges vödör üres, beilleszti a bejegyzést és is_primary = true-ra jelöli.
## Ha a vödör foglalt, végigmegy a meglévő láncon.
5. Új helyet foglal le a Pincéből (a tetejéről, cellar_next-en keresztül).
## Az új bejegyzést next_index segítségével kapcsolja hozzá.

Lekérés: A lekérés követi az elsődleges vödör indexénél induló láncot. Mivel az ütközések explicit láncokba *olvadnak össze*, a get művelet csak azokat a csomópontokat látogatja meg, amelyek ténylegesen ütköztek az adott hash-indexnél.

Teljesítmény-összehasonlítás:

| Funkció | Összeolvasztásos hashelés (FNDS) | Standard nyílt-cím |
|---|---|---|
| Ütközéskezelés | Explicit láncok a pincében | Szondázás (lineáris/kvadratikus) |
| Max terhelési tényező | 0.86 (magas) | Jellemzően 0.5 – 0.7 |
| Legrosszabb eset | O(lánc hossza) | O(klaszter mérete) |

---

 Memóriakezelés és biztonsági minták (Memory Management and Safety Patterns)

Az **FNDS** könyvtár manuális memóriakezelési fegyelmet alkalmaz a std.mem.Allocator interfész köré szervezve. Mivel az adatstruktúra összetett hierarchikus kapcsolatokat, metaadat-tárolást és gyakori újraegyensúlyozást foglal magában, a kódbázis szigorú mintákat követ a tulajdonjoghoz, a mély másoláshoz és a részleges inicializálás biztonságához.

 Tulajdonjog és az Allocator interfész

Az **FNDS** objektumok nem csupán külső memóriára mutatnak, hanem veszik a tulajdonjogot az adatuk felett. Amikor egy karakterlánc (pl. egy id vagy data mező) átadódik egy init függvénynek, a struktúra allocator.dupe segítségével privát másolatot készít.

Kulcsbiztonsági minták:
- Tárolt Allocator-ok: Az olyan struktúrák, mint FractalNodeData, FractalEdgeData és FractalLevel, tárolják a létrehozásukhoz használt Allocator-t.
- Rekurzív Deinicializálás: Az FractalLevel.deinit felelős a saját StringHashMap-jének csomópontokkal és élekkel való megtisztításáért, majd rekurzívan a child_levels tömb összes szintjén meghívja a deinit-et.
- StringHashMap kulcs/érték tulajdonjog: A metaadatoknál a StringHashMap egyenként lefoglalt kulcsokat és értékeket tárol.

 Biztonság errdefer-rel

A részleges inicializálás (ahol az egyik lefoglalás sikerül, de egy következő nem) alatti memóriaszivárgás megelőzéséhez az **FNDS** Zig errdefer kulcsszavát alkalmazza. Ez a Zig kulcsszó biztosítja, hogy ha egy függvény hibát ad vissza, a megadott tisztítási kód végrehajtódik, de figyelmen kívül hagyódik, ha a függvény sikeresen tér vissza.

 Clone és mély másolási szemantika

A könyvtár implementál egy clone metódust az adatokat tároló struktúrákhoz. A mély másolás magában foglalja: a mezők duplikálását (az id és data karakterláncok újrafoglalása és másolása), a gyűjtemény iterálást (StringHashMap metaadatokon végig iterálva minden kulcs-érték pár duplikálásával), és a függetlenséget (a klónozás után az új objektum teljesen független az eredetitől).

---

 Allocator minták és errdefer

 Allocator tárolás és tulajdonjog

Az **FNDS** könyvtár minden fontosabb struktúrája, mint például FractalNodeData és FractalEdgeData, tárolja a létrehozásukhoz használt Allocator referenciát. Ez lehetővé teszi, hogy a struktúrák önkezelők legyenek.

Kulcstulajdonjog-elvek:
- Karakterlánc-duplikáció: Az init metódusoknak átadott karakterláncok szinte mindig allocator.dupe segítségével kerülnek duplikálásra.
- Önkezelt tisztítás: A struktúrák deinit metódust implementálnak, amely a belső allocator mezőt használja az összes tulajdonában lévő szelet és hash map bejegyzés felszabadításához.
- Mély másolás: A clone metódus teljes mély másolatot végez az összes mezőről, beleértve a belső map-ek végig iterálását minden kulcs és érték duplikálásához.

Biztonságos map-bejegyzés-csere: A setMetadata függvény bemutatja a StringHashMap biztonságos frissítésének mintáját, ahol mind a kulcsok, mind az értékek a struktúra tulajdonában vannak. A fetchRemove segítségével biztosítja, hogy ha egy kulcs már létezik, a meglévő memóriája felszabaduljon az új adatok beillesztése előtt.

 Összefoglaló minták

| Minta | Kódentitás | Cél |
|---|---|---|
| Dupe-on-Init | FractalNodeData.init | Biztosítja, hogy a struktúra a hívótól függetlenül tulajdonolja a karakterlánc-adatait. |
| Tárolt Allocator | FractalEdgeData.allocator | Lehetővé teszi a deinit-nek, hogy a hívó újbóli allocator-megadása nélkül működjön. |
| Rekurzív Deinit | FractalLevel.deinit | Biztosítja a beágyazott struktúrák (gyermekszintek) egyetlen hívással való megtisztítását. |
| Fetch-and-Free | FractalNodeData.setMetadata | Megakadályozza a szivárgásokat a StringHashMap-ben lévő kulcsok felülírásakor. |
| Clone-errdefer | FractalNodeData.clone | A struktúra saját deinit-jét használja errdefer célpontként összetett másolatok során. |

---

 Clone és mély másolási szemantika

 Az Clone minta áttekintése

Az **FNDS**-ben az egyszerű mező-szerinti másolás (sekély másolat) nem elegendő, mert az olyan struktúrák, mint FractalNodeData és FractalEdgeData, heap-allokált karakterláncokat és dinamikus map-eket tartalmaznak. A sekély másolat kettős-free hibákhoz vagy use-after-free összeomlásokhoz vezetne.

A clone metódus kritikus a következőkhöz: ## Egyensúly-rekonstrukció: Amikor egy FractalTree újraegyensúlyozódik, a csomópontok összegyűjtése és egy új struktúrába való újra-beillesztése történik. ## Gyorsítótár tárolás: Az FNDSManager-ben lévő LRUCache keresési eredményeket tárol, amelyeknek érvényesnek kell maradniuk akkor is, ha az eredeti fastruktúra módosul vagy törlődik.

Mély másolás entitás-leképezés:

| Koncepció | Kódentitás | Implementáció részlete |
|---|---|---|
| Csomópont mély másolás | FractalNodeData.clone | Duplikálja az id-t, data-t és az összes metadata bejegyzést. |
| Él mély másolás | FractalEdgeData.clone | Duplikálja a source_id-t és a target_id-t. |
| Minta mély másolás | PatternLocation.clone | Duplikálja a node_id-t és a tree_id-t. |
| Biztonsági őr | errdefer | Biztosítja a részleges klónok megtisztítását lefoglalási hiba esetén. |

---

 Algoritmusok és matematika (Algorithms and Mathematics)

 Matematikai alapok és fraktálanalízis

Az **FNDS** a fraktáldimenziót elsődleges mérőszámként használja a hierarchikus struktúrákban tárolt adatok komplexitásának és önhasonlóságának jellemzéséhez. A rendszer két különböző megközelítést alkalmaz a dimenzió kiszámítására:

- Strukturális dimenzió: A FractalLevel-en kiszámítva dobozszámláló becslés segítségével. Log-log lineáris regressziót végez dobozméret-számpárokban.
- Mintadimenzió: Az SelfSimilarIndex-en belül kiszámítva a mintahosszak frekvenciaeloszlásának elemzésével.
- Aggregálás: A FractalTree ezeket a lokális méréseket egyetlen globális szerkezeti mérőszámba aggregálja.

 Bejárási stratégiák

A FractalTree négy különböző bejárási módot támogat a TraversalOrder enumon keresztül. Minden bejárás TraversalCallback függvénymutatót alkalmaz.

 Hashing stratégia

Az **FNDS** kétrétegű hashing stratégiát alkalmaz:

| Kontextus | Algoritmus | Kódentitás | Cél |
|---|---|---|---|
| Integritás | SHA-256 | FractalNodeData.init | fractal_signature generálása |
| Útválasztás | Wyhash | FractalTree.computeChildIndex | Csomópontok célgyermek-szintre való meghatározása |
| Keresés | Wyhash | FractalNodeData.computeHash | Gyors egyenlőség-ellenőrzések |
| Gyorsítótárazás | Wyhash | FNDSManager.buildCacheKey | (tree_id + node_id) gyorsítótár-slotokra való leképezése |

---

 Fraktáldimenzió kiszámítása

 Az algoritmusok áttekintése

Az **FNDS** háromrétegű fraktáldimenzió-analízist biztosít:

## Lokális (Szint-alapú): Dobozszámláló módszert alkalmaz egy konkrét FractalLevel komplexitásának becslésére.

## Globális (Fa-alapú): Aggregálja a lokális dimenziókat egy FractalTree hierarchiáján keresztül. ## Minta-alapú (Index-alapú): Elemzi az indexelt minták önhasonlóságát egy SelfSimilarIndex-en belül.

 Matematikai alap: Log-Log regresszió

Mindkét elsődleges algoritmus log-transzformált adatpontokon alkalmazott legkisebb négyzetek lineáris regresszióját alkalmazza a fraktáldimenzió (D) meghatározásához:

log(N(r)) = D · log(1/r) + C

ahol r a skála (dobozméret vagy mintahossz) és N(r) az adott skálán lévő szám vagy frekvencia.

 FractalLevel: Dobozszámláló becslés

Implementáció részletei:
- Dobozméret: Az algoritmus négy rögzített dobozméret halmazát használja: {1, 2, 4, 8}.
- Becslés: Az estimateBoxCount segítségével közelíti meg minden r esetén a térbeli foglaltságot.
- Lineáris regresszió: Az (x, y) párok ahol x = log(1/r) és y = log(N(r)) a legkisebb négyzetek megoldóján keresztül kerülnek átadásra.

 SelfSimilarIndex: Minta-frekvencia regresszió

Implementáció részletei:
- Frekvencia-leképezés: Végigiterálja az összes mintakulcsot és megszámolja az egyes mintahosszak előfordulásait.
- Log-Log analízis: A mintahosszt *skálaként* (r), és ennek a hossznak a frekvenciáját *számként* (N(r)) kezeli.
- Korlát: Minimum két különböző mintahossz szükséges a regresszió elvégzéséhez.

 FractalTree: Rekurzív aggregálás

A FractalTree nem számít új dimenziót az alapoktól, hanem összesíti az összes alkotó FractalLevel objektum lokális dimenzióit. Rekurzív bejárást végez a szinteken, meghívja a computeLocalFractalDimension-t minden szinten, majd az összes nem-nulla szintdimenzió aritmetikai átlagát adja vissza.

---

 Fa-bejárási stratégiák (Tree Traversal Strategies)

 A bejárás alapjai

A bejárások az **FNDS**-ben a TraversalOrder enummal és egy szabványosított visszahívási függvény-mutatóval kerülnek irányításra.

TraversalOrder enum:

| Mód | Leírás | Logika |
|---|---|---|
| pre_order | Gyökér-első DFS | Meglátogatja az aktuális csomópontot, majd rekurzívan az összes gyermekszintre megy. |
| post_order | Gyermek-először DFS | Rekurzívan az összes gyermekszintre megy, majd meglátogatja az aktuális csomópontot. |
| level_order | Szélességi keresés | Csomópontokat szint-szint alapján látogat meg FIFO sort használva. |
| fractal_order | Szimmetrikus rekurzív | Meglátogatja a gyökeret, rekurzívan végigmegy az első fél gyermeken előre, majd a második felet fordítva. |

TraversalCallback: A rendszer függvénymutatót alkalmaz az összes bejárási művelethez: pub const TraversalCallback = const fn (node: const FractalNodeData) anyerror!void;

 Bejárás implementációs logikája

Mélységi stratégiák (Pre/Post Order): A pre_order és post_order esetén a rendszer rekurzív ereszkedést végez a child_levels tömbön az egyes FractalLevel-eken belül.

Szintsorend (**BFS**): A szintsorend bejárás egy LinearFifo-t alkalmaz a látogatandó szintek határának kezelésére. Inicializálódik a gyökérszinttel, majd amíg a sor nem üres, kivesz egy FractalLevel-t, végrehajtja a visszahívást a csomópontjaira, és betolja az összes child_levels-t a sor hátulján.

Fraktálsorend: Meglátogatja a gyökér csomópontjait, előre iterálja az első fél child_levels-t (0-tól középig), majd visszafelé iterálja a második felet.

 Bejárási stratégiák összehasonlítása

| Stratégia | Memóriakomplexitás | Időkomplexitás | Legjobb felhasználás |
|---|---|---|---|
| Pre-Order | O(Mélység) | O(N) | Fák klónozása, prefixum-alapú műveletek. |
| Post-Order | O(Mélység) | O(N) | Fák törlése (alulról felfelé megtisztítás), függőség-feloldás. |
| Level-Order | O(Szélesség) | O(N) | A gyökér közelében lévő csomópontok keresése, szintszintű statisztikák. |
| Fractal-Order | O(Mélység) | O(N) | Önhasonló mintaillesztés, kiegyensúlyozott térbeli feldolgozás. |

Technikai korlátok:
- A pre_order, post_order és fractal_order stack-korlátok alá esik. Rendkívül mély fáknál (amelyek meghaladják a standard stack-kereteket) a level_order preferált.
- A level_order aktív Allocator-t igényel a **FIFO** sor inicializálásához, míg a **DFS** bejárások nulla lefoglalással járnak (a stack terét kivéve).

---

 Hashing stratégia (Hashing Strategy)

Az **FNDS** könyvtár kétrétegű hashing stratégiát alkalmaz a kriptográfiai integritás és a magas teljesítményű fa-műveletek egyensúlya érdekében.

 1. Kriptográfiai azonosság: **SHA**-**256**

A fractal_signature egy egyedi ujjlenyomat, amelyet egy FractalNodeData objektum inicializálása során számítanak ki. Ez az aláírás az adatoknak a fraktálstruktúrán belüli megváltozhatatlan azonosságaként szolgál.

Az aláírás generálásának adatfolyama:

| Input mező | Forrás | Szerepe az aláírásban |
|---|---|---|
| id | []const u8 | Egyedi azonosító karakterlánc |
| data | []const u8 | A hasznos tartalom |
| weight | f64 | Fontossági/prioritási mérőszám |
| scale | f64 | Térbeli/hierarchikus dimenzió |

 2. Teljesítmény-kritikus hashing: Wyhash

Minden futásidejű műveletnél, ahol a sebesség az elsődleges korlát, az **FNDS** Wyhash-t alkalmaz (std.hash.Wyhash). A Wyhash egy nem kriptográfiai hash-függvény, amelyet a modern 64 bites hardveren való kiváló teljesítménye és az eloszlás magas minősége miatt választottak.

Csomópontállapot-hashing: A computeHash metódus az FractalNodeData-n egy 64 bites pillanatfelvételt ad a csomópont teljes állapotáról, beleértve a metaadatait is.

Fa-útválasztás és beillesztés: Az FractalTree-be való beillesztéskor a computeChildIndex függvény Wyhash-t alkalmaz a bemeneti adatokra és modulo operációt végez a fa branching_factor-a alapján.

Belső adatstruktúrák: A CoalescedHashMap Wyhash-t alkalmaz az elsődleges vödör-indexek generálásához, az LRUCache pedig buildCacheKey-t alkalmaz egy összetett 64 bájtos kulcs összeállítására.

 3. A hashing szerepek összefoglalója

| Kontextus | Algoritmus | Entitás/Függvény | Cél |
|---|---|---|---|
| Azonosság | SHA-256 | fractal_signature | Csomópont megváltozhatatlan magjának kriptográfiai ujjlenyomata. |
| Integritás | Wyhash | computeHash | Csomópont aktuális állapotának 64 bites hash-e beleértve metaadatait. |
| Útválasztás | Wyhash | computeChildIndex | Adatok determinisztikus leképezése gyermek-ágakra. |
| Gyorsítótárazás | Wyhash | buildCacheKey | Gyors keresés az FNDSManager LRU-gyorsítótárához. |
| Tárolás | Wyhash | CoalescedHashMap | Belső index-generálás az egyedi hash map-hez. |

---

 Külső függőségek és integráció (External Dependencies and Integration)

Az **FNDS** könyvtár az fnds.zig és a külső környezete közötti kapcsolatát dokumentálja, különösen az nsir_core.zig függőségre és a Zig Standard Könyvtár használatára fókuszálva.

 Kapcsolati áttekintés

Az **FNDS** könyvtár a relációs adatstruktúrák specializált implementációjaként működik. Az nsir_core.zig-re támaszkodik az alap gráfdefiníciókért, és a Zig Standard Könyvtárat alkalmazza kriptográfiai hasheléshez, memóriakezeléshez és időzítéshez.

 nsir_core integráció

Az fnds.zig könyvtár importálja és újraexportálja az nsir_core.zig több kulcstípusát:

| Újraexportált típus | Forrás entitás | Leírás |
|---|---|---|
| SelfSimilarRelationalGraph | nsir_core.SelfSimilarRelationalGraph | Az alapvető gráf konténer relációs adatokhoz. |
| Node | nsir_core.Node | A relációs gráf alapegysége. |
| Edge | nsir_core.Edge | Kapcsolat két Node entitás között. |
| EdgeQuality | nsir_core.EdgeQuality | Metaadat a relációs kapcsolat erősségének meghatározásához. |
| EdgeKey | nsir_core.EdgeKey | Az egyedi azonosító az él-keresésekhez hash map-ekben. |

 Zig Standard Könyvtár használata

| Komponens | Használat az FNDS-ben |
|---|---|
| std.mem.Allocator | Manuális memóriakezelés az összes struktúrában. |
| std.crypto.hash.sha2.Sha256 | A fractal_signature generálása az FractalNodeData-hoz. |
| std.hash.Wyhash | Gyors hashing a CoalescedHashMap-hez és a gyermekindex-útválasztáshoz. |
| std.fifo.LinearFifo | Szintsorend (BFS) fa-bejárások kezelése. |
| std.time.nanoTimestamp | Műveleti késleltetés nyomon követése az FNDSStatistics-ban. |

Verzió és kompatibilitási szempontok: A könyvtár Zig 0.11.0 vagy újabbra lett tervezve. Kompatibilis a std.heap.GeneralPurposeAllocator, std.heap.ArenaAllocator vagy egyéni lap-allokátorokkal. Minden standard könyvtári hiba (pl. OutOfMemory) a !Self vagy !void visszatérési típusokon keresztül kerül propagálásra.

---

 nsir_core integráció

 Cél és hatókör

Az fnds.zig könyvtár az nsir_core.zig-re támaszkodik mint alapvető gráfelméleti szubsztrátumra. Míg az **FNDS** a hierarchikus fraktálszervezésre és önhasonló indexelésre fókuszál, az nsir_core a relációs modellezés alacsony szintű primitíveit biztosítja.

 Fogalmi kapcsolat: **NSIR** vs. **FNDS**

**NSIR** Core (Relációs): A *Mit* és *Kit* fókuszálja. Meghatározza, hogyan viszonyulnak egymáshoz csomópontok éleken keresztül hagyományos gráf értelemben. Optimalizált a kapcsolódásra és a szolgáltatásminőségi mérőszámokra.

**FNDS** (Fraktál/Strukturális): A *Hol* és *Milyen mélyen* fókuszálja. Adatokat burkol FractalNodeData-ba és FractalEdgeData-ba, egy FractalTree-n belül elhelyezve. Optimalizált skálaállandó keresésre, hierarchikus tartalmazásra és dobozszámláló dimenzióanalízisre.

 Implementációs iránymutatás

Az nsir_core kibővítésekor a következő mintákat kell követni: ## Típus-konzisztencia: Az nsir_core-hoz adott új relációs típusokat pub const deklarációkon keresztül kell közzétenni az fnds.zig-ben. ## Aláírás-összehangolás: Az FNDS Sha256-ot alkalmaz a fractal_signature-hoz. Ha az nsir_core entitások egyedi azonosítókat igényelnek, kompatibilis hashing stratégiákat kell használni. ## Memóriakezelés: Mindkét könyvtár az Allocator mintát követi. Amikor egy Node-ot az nsir_core-ból egy FNDS FractalTree-be adunk át, az FractalNodeData.init függvényt kell használni a mély másolat készítéséhez, mivel az FNDS átveszi a belső csomópontkarakterlánc-adatok tulajdonjogát.

---

 Zig Standard Könyvtár használata

 Az alapimportok és szimbólumok

| Szimbólum | Standard könyvtár komponens | Cél az FNDS-ben |
|---|---|---|
| Allocator | std.mem.Allocator | Manuális memóriakezelés és erőforrás-nyomon követés. |
| ArrayList | std.ArrayList | Dinamikus tömbök gyermekszintekhez és mintakulcsokhoz. |
| StringHashMap | std.StringHashMap | Kulcs-érték tárolás a metaadatokhoz és csomópont-keresésekhez. |
| AutoHashMap | std.AutoHashMap | Típusbiztos leképezés belső azonosítókhoz. |
| Sha256 | std.crypto.hash.sha2.Sha256 | Egyedi csomópont fraktál-aláírások generálása. |
| Random | std.crypto.random | Kriptográfiailag biztonságos fa-azonosító generálás. |
| Wyhash | std.hash.Wyhash | Nagy sebességű nem-kriptográfiai hashing az indexekhez. |
| Complex | std.math.Complex | Importálva a fejlett fraktálszámításokhoz. |

 Memóriakezelési minták

## Duplikáció: allocator.dupe(u8, ...) segítségével biztosítja, hogy a könyvtár tulajdonában legyen a karakterláncok memóriája.

## Hibakezelés: Széles körű errdefer használat a részlegesen sikertelen inicializálások alatti memóriaszivárgások megelőzésére. ## Megtisztítás: A deinit mintát rekurzívan alkalmazza; pl. FractalLevel.deinit végigiterálja a StringHashMap és ArrayList tagjait az összes lefoglalt memória felszabadításához.

---

 Szószedet (Glossary)

 Alapvető architektúrális fogalmak

| Kifejezés | Definíció | Kódentitás |
|---|---|---|
| FNDSManager | A legfelső szintű orchestrátor. Több fa és index életciklusát kezeli, a gyorsítótárazást, és nyomon követi a globális statisztikákat. | FNDSManager |
| FractalTree | Egy hierarchikus konténer, amely csomópontokat skálájuk és elágazási tényezőik alapján rekurzív szintekbe szervez. | FractalTree |
| FractalLevel | A FractalTree horizontális szelete egy adott mélységben vagy skálán. Csomópontok és élek gyűjteményét tartalmazza. | FractalLevel |

 Adatstruktúrák és tárolás

FractalNodeData: A tárolás alapegysége. A standard gráf-csomóponttal ellentétben fraktáltulajdonságokat tartalmaz a többskálájú analízishez.
- Fraktál-aláírás: **256** bites kriptográfiai hash (**SHA**-**256**) a csomópont azonosítójából, adataiból, súlyából és skálájából.
- Súly/Skála: Lebegőpontos értékek az adatok relatív fontosságának és felbontási szintjének megjelenítéséhez.
- Metaadat: Dinamikus StringHashMap tetszőleges kulcs-érték párok tárolásához.

FractalEdgeData: Csomópontok közötti kapcsolatokat képvisel.
- EdgeType: hierarchical (szülő-gyermek), sibling (azonos szint), cross_level (különböző ágak/mélységek), vagy self_similar (minta-alapú).
- Fraktál-korreláció: Mérőszám a forrás- és célcsomópontok önhasonlóságának erősségéről.

CoalescedHashMap: Egyedi hash map implementáció pince-alapú ütközési stratégiával. Tárolóját elsődleges vödrökre és a túlcsordulások számára fenntartott *pincére* osztja.

 Algoritmikus kifejezések

Fraktáldimenzió: Az adatok strukturális komplexitásának és önhasonlóságának mértéke. A kódbázis két elsődleges módszert implementál: dobozszámlálás (lokális) és mintaeloszlás (globális).

Bejárási rendek: A könyvtár négy konkrét módot támogat egy FractalTree navigálásához a TraversalOrder enumon keresztül: pre_order, post_order, level_order (**BFS** LinearFifo segítségével), fractal_order.

 Technikai rövidítések

| Rövidítés | Teljes forma | Kontextus |
|---|---|---|
| LRU | Legrégebben Használt (Least Recently Used) | Az FNDSManager gyorsítótár kiürítési szabályzata. |
| DFS | Mélységi Keresés (Depth First Search) | A pre_order és post_order bejárások mögöttes mechanizmusa. |
| BFS | Szélességi Keresés (Breadth First Search) | A level_order bejárás mögöttes mechanizmusa. |
| SHA-256 | Secure Hash Algorithm 2 | A csomópont integritásának fractal_signature generálásához használt. |
| Wyhash | Wyhash | Gyors, nem-kriptográfiai hash, amelyet a belső map-indexeléshez és gyermek-útválasztáshoz használnak. |
