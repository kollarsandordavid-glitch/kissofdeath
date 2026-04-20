Esso — Teljes Wiki (Magyar)

---

 1. Áttekintés

Az Entangled Stochastic Symmetry Optimizer (ESSO) egy Zig nyelven írt, nagy teljesítményű optimalizációs motor. Arra tervezték, hogy komplex, önhasonló gráfokként ábrázolt relációs struktúrákat optimalizáljon a szimulált hűtés (simulated annealing), a kvantummechanika és a fraktálgeometria technikáinak ötvözésével.

A projekt azt a kihívást kezeli, hogy globális minimumokat találjon olyan többdimenziós állapottérben, ahol a hagyományos gradiens ereszkedés (gradient descent) kudarcot vall a rögös energiatájképek miatt. A Symmetry Detection (szimmetria detektálás) kihasználásával az optimalizáló nagy léptékű kvantumugrásokat hajthat végre a keresési térben, míg az Entanglement (összefonódás) modellek hosszú távú korrelációkat biztosítanak a gráf csomópontjai között, amelyek irányítják a sztochasztikus keresési folyamatot.

 Tartományi integráció

Az ESSO négy fő elméleti tartomány metszéspontjában működik:

1. Simulated Annealing: A magmotor egy Metropolis-Hastings elfogadási kritériumot és egy hűtési ütemtervet használ a lokális minimumokból való kilépéshez.
2. Kvantummechanika: A csomópontokat Qubit-ként kezeli komplex amplitúdókkal és fázisokkal. Az optimalizációs lépések tartalmazhatnak kvantumállapot-transzformációkat.
3. Gráfelmélet: A rendszer SelfSimilarRelationalGraph struktúrákat optimalizál, módosítva az élsúlyokat és a topológiát egy célenergia minimalizálása érdekében.
4. Fraktálgeometria: Az optimalizáló nyomon követi és perturbálja a csomópontok fractal_dimension értékét, lehetővé téve az önhasonló strukturális minták kialakulását.

 Fő komponensek

Az optimalizációs motor
Az elsődleges belépési pont az EntangledStochasticSymmetryOptimizer. Ez kezeli az optimalizációs életciklust, beleértve a hőmérséklet-szabályozást, az iterációs korlátokat és az optimize() ciklus meghívását.

Állapot és összefonódás
Az OptimizationState tárolja a gráf és metaadatainak aktuális pillanatképét. Kritikus funkció az entanglement_map, amely a NodePairKey-t használja a csomópontok közötti EntanglementInfo nyomon követésére, reprezentálva a történelmi korrelációkat, amelyek befolyásolják a jövőbeli lépéseket.

Szimmetria és transzformációk
A rendszer rendszeresen futtatja a detectSymmetries függvényt a strukturális minták (pl. forgatások vagy tükrözések) azonosítására. Ezeket SymmetryPattern objektumokként tárolja, és arra használja, hogy SymmetryTransform műveleteket alkalmazzon a gráf kvantumállapotaira.

---

 2. Első lépések

Az Entangled Stochastic Symmetry Optimizer (ESSO) egy speciális optimalizációs motor, amelyet önhasonló relációs gráfok manipulálására terveztek a szimulált hűtés, a kvantumlogika és a geometriai szimmetria detektálás elveinek felhasználásával. Ez a fejezet gyakorlati útmutatót nyújt az esso_optimizer.zig modul Zig projektbe történő integrálásához és egy alapvető optimalizációs ciklus végrehajtásához.

 Integráció és függőségek

Az ESSO használatához a projektnek tartalmaznia kell az esso_optimizer.zig fájlt és annak alapvető függőségeit. Az optimalizáló a gráfstruktúrákhoz az nsir_core modulra, az állapotmanipulációkhoz pedig a quantum_logic modulra támaszkodik.

Szükséges fájlok:
- esso_optimizer.zig — Az optimalizáló fő belépési pontja.
- nsir_core.zig — Biztosítja a SelfSimilarRelationalGraph, Node, Edge és Qubit típusokat.
- quantum_logic.zig — Biztosítja a QuantumState és RelationalQuantumLogic típusokat.

 Az optimalizáló példányosítása

Az EntangledStochasticSymmetryOptimizer az elsődleges motor. Szüksége van egy Allocator-ra a belső állapot kezeléséhez, beleértve az energiatörténetet, a hőmérséklettörténetet és a szimmetriamintákat.

 Inicializálási módszerek

Az optimalizáló inicializálására három elsődleges mód van:

1. initDefault(allocator) — Szabványos heurisztikus értékekkel inicializál (pl. initial_temperature = 100.0, cooling_rate = 0.95).
2. init(allocator, params) — Lehetővé teszi a hűtési ütemterv és a szimmetria intervallumok teljes manuális konfigurálását.
3. initWithSeed(allocator, seed) — Hasonló az initDefault-hoz, de lehetővé teszi egy specifikus seed megadását a PRNG számára a reprodukálható optimalizációs futtatások biztosítása érdekében.

 Alapértelmezett konfigurációs konstansok

Az initDefault használatakor érvényes alapértelmezések:

| Konstans | Érték |
|---|---|
| DEFAULT_INITIAL_TEMP | 100.0 |
| DEFAULT_COOLING_RATE | 0.95 |
| DEFAULT_MAX_ITERATIONS | 10 000 |
| DEFAULT_SYMMETRY_INTERVAL | 100 iteráció |

 Az optimalizációs folyamat

Az optimize() függvény mély másolatot (deep copy) készít a bemeneti gráfról, biztosítva, hogy az eredeti érintetlen maradjon.

Amikor az optimize() meghívásra kerül, a motor:

1. Klónozza a bemeneti gráfot egy belső OptimizationState-be.
2. Szimmetriákat detektál a kezdeti SymmetryPattern lista feltöltéséhez.
3. Iterál a lépéseken (élperturbációk, fáziseltolások, szimmetria-transzformációk).
4. Elfogadja/elutasítja a lépéseket az acceptMove függvény segítségével, amely a Metropolis-Hastings kritériumot valósítja meg: P(accept) = exp(-ΔE / T).

---

 3. Architektúra és modulhatárok

Az ESSO elsősorban egyetlen fájlból álló motorként, az esso_optimizer.zig-ben van implementálva, amely magas szintű optimalizációs logikát hangszerel a gráfelméleti struktúrák és a kvantumlogikai definíciók integrálásával. Az architektúra egy Single-File Engine mintát követ, ahol az optimalizáló állapota, a szimmetria detektáló gépezet és a sztochasztikus keresési ciklus együtt helyezkedik el.

 Modulfüggőségek és importok

Az esso_optimizer.zig fájl integrációs rétegként szolgál az nsir_core és a quantum_logic modulok számára.

1. nsir_core.zig — A rendszer strukturális alapja:
- SelfSimilarRelationalGraph — Az optimalizálandó elsődleges adatszerkezet.
- Node, Edge, EdgeKey, EdgeQuality — Primitív gráfkomponensek.
- Qubit — Az állapot alapvető egysége a csomópontokon belül.

2. quantum_logic.zig — A kvantumállapot-manipuláció matematikai és logikai keretrendszere:
- QuantumState — A csomópont komplex amplitúdóját és fázisát képviseli.
- RelationalQuantumLogic és LogicGate — Transzformációk és állapotkonzisztencia értékelésére szolgál.

 Nyilvános API felület

| Entitás | Szerep |
|---|---|
| EntangledStochasticSymmetryOptimizer | A fő motor, amely az optimize() ciklusért felelős. |
| OptimizationState | A gráf és kvantumtulajdonságainak pillanatképe egy adott iterációban. |
| ObjectiveFunction | Egy függvénymutató típus, amelyet az energiatájék definiálására használnak. |
| SymmetryGroup | Egy enum, amely meghatározza a támogatott geometriai transzformációkat. |

 Modulhatárok és adatfolyam

Az optimalizáló és a gráf közötti határt az OptimizationState kezeli. Ez a struct burkolóként (wrapper) működik a SelfSimilarRelationalGraph körül, kiegészítve azt optimalizáció-specifikus metaadatokkal.

Adatfolyam jellemzői:

1. Tulajdonjog (Ownership): Az optimalizáló jellemzően klónozza a bemeneti gráfot a cloneGraph használatával, hogy biztosítsa, az eredeti adatok nem mutálódnak a sztochasztikus keresés során.
2. Szimmetria alkalmazása: A szimmetria detektáló logika azonosítja a SymmetryPattern objektumokat, amelyek SymmetryTransform példányokat tartalmaznak. Ezeket a transzformációkat a QuantumState objektumokra alkalmazzák a megoldástér felfedezéséhez.
3. Állapot visszaállítása: Az UndoLog biztosítja, hogy az aktuális és javasolt állapot közötti határ szigorúan fennmaradjon. Ha egy lépést elutasítanak, az UndoLog visszaállítja az élsúlyokat, csomópont állapotokat, vagy egy teljes gráf pillanatképet.

---

 4. Alapvető adatszerkezetek

Ez a fejezet áttekintést nyújt az ESSO motorban használt elsődleges adatszerkezetekről. Ezek a struktúrák képviselik az optimalizációs folyamat állapotát, a csomópontok közötti kvantum-összefonódások metaadatait, valamint a szimulált hűtési folyamat statisztikai nyomon követését.

Az alapvető entitások közötti kapcsolat az OptimizationState köré összpontosul, amely konténerként működik az optimalizált gráf és a hozzá tartozó kvantum metaadatok számára.

 OptimizationState

Az OptimizationState a központi struktúra, amely nyomon követi a SelfSimilarRelationalGraph aktuális konfigurációját egy optimalizációs futtatás során.

Főbb felelősségek:
- Gráf tulajdonjog: Kezeli, hogy az állapot birtokolja-e a gráf memóriáját (owns_graph jelző).
- Összefonódás kezelése: Kiszámítja és frissíti az entanglement_percentage értéket a teljes gráfon.
- Állapot klónozása: Mély másolási funkcionalitást biztosít a clone() segítségével a legjobb eddigi állapot nyomon követésének támogatására.

 EntanglementInfo és NodePairKey

A csomópontok közötti kvantumkorrelációkat nem az alap gráfstruktúra tárolja, hanem metaadatként kezelik az optimalizálón belül.

- EntanglementInfo — Tárolja egy kvantum-összefonódási kapcsolat fizikai tulajdonságait: korrelációs erősség, fáziskülönbség, létrehozási idő.
- NodePairKey — Lexikografikus normalizálást valósít meg, biztosítva hogy az A–B csomópont párja azonos a B–A párral. A kisebb csomópont ID mindig elsőként kerül tárolásra.

 OptimizationStatistics

Az OptimizationStatistics struct átfogó telemetriai csomagot biztosít az optimalizációs folyamathoz.

| Metrika | Cél |
|---|---|
| acceptance_rate | Az elfogadott lépések aránya; adaptív hűtéshez használatos. |
| energy (legjobb/aktuális) | Nyomon követi a célfüggvény minimalizálásának előrehaladását. |
| convergence_delta | Az energiaváltozás egy csúszóablak felett, fennsíkok észlelésére. |
| symmetries_detected | A gráfban talált geometriai minták száma. |

---

 5. OptimizationState

Az OptimizationState struct az elsődleges adatkonténer, amely a megoldástér egyetlen pontját képviseli az optimalizációs folyamat során. Magában foglalja a gráf strukturális topológiáját, kvantumállapot-tulajdonságait és a csomópontok közötti összefonódások komplex hálóját.

 Alapvető struktúra és mezők

| Mező | Típus | Leírás |
|---|---|---|
| graph | SelfSimilarRelationalGraph | Mutató a csomópontokat és éleket tartalmazó alapul szolgáló gráfstruktúrára. |
| energy | f64 | A kiszámított skaláris érték, amely az aktuális állapot költségét képviseli. |
| entanglement_percentage | f64 | Normalizált érték (0.0–1.0), amely az összefonódott párok sűrűségét képviseli. |
| iteration | usize | Az aktuális lépésszám az optimalizációs életcikluson belül. |
| owns_graph | bool | Életciklus jelző: a struct felelős-e a graph memória felszabadításáért. |
| entanglement_map | AutoHashMap(NodePairKey, EntanglementInfo) | A specifikus csomópontpárok közötti kvantumkorrelációs adatok. |

 Életciklus és memóriatulajdonjog

- init — Inicializálja az entanglement_map-et, nullára állítja a kezdeti metrikákat. Egy mutatót vesz át a gráfra, nem foglalja le magát a gráfot.
- deinit — Törli az entanglement_map-et. Ha owns_graph = true, meghívja a graph.deinit() függvényt is.

Mély másolás a clone segítségével: A globális cloneGraph segédprogramot használja a gráf topológiájának és metaadatainak replikálására, biztosítva, hogy az új OptimizationState teljesen független legyen a forrástól. Az owns_graph értékét true-ra állítja az új példányhoz.

 Összefonódás kezelése

| Metódus | Leírás |
|---|---|
| addEntanglement | Létrehoz egy új EntanglementInfo bejegyzést egy csomópontpárhoz. |
| updateEntanglement | Frissíti a korrelációs erősséget és fázist; szinkronizálja a metrikákat. |
| getEntanglement | Lekéri az EntanglementInfo-t egy adott párhoz, vagy null-t ad vissza. |
| hasEntanglement | Logikai ellenőrzés két csomópont közötti korreláció meglétére. |
| averageEntanglement | Kiszámítja az átlagos correlation_strength értéket az összes párra. |
| refreshEntanglementPercentage | Frissíti az entanglement_percentage mezőt az aktív és lehetséges párok arányaként. |

---

 6. EntanglementInfo és NodePairKey

Ezek az adatszerkezetek az EntangledStochasticSymmetryOptimizer által a csomópontok közötti kvantum-ihletésű korrelációk kezelésére és nyomon követésére használt struktúrák.

 NodePairKey és lexikografikus normalizálás

A NodePairKey struct egy egyedi, irányítatlan kapcsolatot képvisel két csomópont között. Mivel az összefonódás szimmetrikus, az (A, B) párt azonos módon kell kezelni mint a (B, A) párt.

| Mező | Típus | Leírás |
|---|---|---|
| node_a_id | [32]u8 | Az első csomópont SHA-256 azonosítója (lexikografikusan kisebbre normalizálva). |
| node_b_id | [32]u8 | A második csomópont SHA-256 azonosítója (lexikografikusan nagyobbra normalizálva). |

Főbb függvények:
- init(id1, id2) — Összehasonlítja a két azonosítót a std.mem.order használatával; a kisebbet a node_a_id-hez, a nagyobbat a node_b_id-hez rendeli. Így a getEntanglement(A, B) és getEntanglement(B, A) mindig ugyanarra a hash map bejegyzésre oldódik fel.
- hash(self, context) — Kiszámítja mindkét azonosító kombinált hash-ét.
- eql(self, other, context) — Konstans idejű memória-összehasonlítást végez mindkét azonosítón.

 EntanglementInfo

| Mező | Típus | Leírás |
|---|---|---|
| correlation_strength | f64 | Az összefonódás nagysága (0.0–1.0). |
| phase_difference | f64 | A relatív kvantumfázis a két csomópont között. |
| creation_time | i64 | Időbélyeg (ms), amikor az összefonódás először létrejött. |
| last_update_time | i64 | A legutóbbi interakció időbélyege (ms). |
| interaction_count | u64 | Azon alkalmak száma, ahányszor ez a pár részt vett egy optimalizációs lépésben. |

Életciklus:
1. init(strength, phase) — Beállítja a kezdeti állapotot és rögzíti az aktuális rendszeridőt.
2. update(strength_delta, phase_new) — Növeli az interaction_count értékét, frissíti az időbélyeget, és a correlation_strength értékét 0.0–1.0 közé szorítja.
3. getAge(current_time) — Kiszámítja az utolsó frissítés óta eltelt időt.

 Bomlási mechanizmus

Az ESSO motor exponenciális bomlási modellt valósít meg az összefonódásra, megakadályozva, hogy az optimalizáló elavult korrelációk csapdájába essen.

Exponenciális bomlási képlet:

$$\text{Faktor} = e^{-\ln(2) \cdot (\Delta t \;/\; t_{1/2})}$$

ahol:
- $\Delta t$ — a last_update_time óta eltelt idő
- $t_{1/2}$ — a half_life_ms paraméter (az optimalizáló konfigurációja biztosítja)

Amikor a getEntanglement meghívásra kerül, nem csak a nyers correlation_strength-et adja vissza, hanem alkalmazza a bomlási tényezőt is, biztosítva, hogy az optimalizáló a friss, aktív korrelációkat részesíti előnyben.

---

 7. OptimizationStatistics

Az OptimizationStatistics struct átfogó telemetriai konténer, amelyet az EntangledStochasticSymmetryOptimizer használ az optimalizációs folyamat egészségének, előrehaladásának és teljesítményének nyomon követésére.

 Adatszerkezet

| Mező | Típus | Leírás |
|---|---|---|
| iterations_completed | usize | A végrehajtott fő ciklusok teljes száma. |
| moves_accepted | usize | Azon állapotátmenetek száma, amelyek megfeleltek a Metropolis kritériumnak. |
| moves_rejected | usize | Azon javasolt lépések száma, amelyeket az UndoLog segítségével visszavontak. |
| best_energy | f64 | Az optimalizálás kezdete óta talált legalacsonyabb energiaállapot. |
| current_energy | f64 | Az aktuális rendszerállapot energiája. |
| symmetries_detected | usize | A gráfban talált egyedi SymmetryPattern példányok száma. |
| entangled_pairs | usize | Az aktív bejegyzések száma az entanglement_map-ben. |
| elapsed_time_ms | i64 | Az optimize() függvényben eltöltött teljes falióra idő. |
| acceptance_rate | f32 | Az elfogadott lépések aránya (0.0–1.0). |
| cooling_factor_applied | f64 | A hőmérsékletre jelenleg alkalmazott tényleges szorzó. |
| local_minima_escapes | usize | Azon alkalmak száma, amikor a reheat_factor aktiválódott stagnálás miatt. |
| convergence_delta | f64 | Az energiaváltozás az utolsó két sikeres lépés között. |
| temperature | f64 | Az aktuális termodinamikai hőmérséklet, amely a lépések elfogadását szabályozza. |
| total_energy_evaluations | usize | Azon alkalmak száma, ahányszor az ObjectiveFunction meghívásra került. |
| average_move_delta | f64 | A javasolt lépések energiaváltozásainak (ΔE) mozgóátlaga. |

 Segédmetódusok

updateAcceptanceRate
Kiszámítja az aktuális elfogadási arányt. Képlet: moves_accepted / (moves_accepted + moves_rejected). Nullával való osztás esetén 0.0-t ad vissza.

updateElapsedTime
Frissíti az elapsed_time_ms mezőt: std.time.milliTimestamp() - start_time.

iterationsPerSecond
Kiszámítja az optimalizáló áteresztőképességét: (iterations_completed × 1000) / elapsed_time_ms.

isConverged
true-t ad vissza, ha a convergence_delta kisebb, mint a küszöbérték és a temperature közel van a min_temperature padlóhoz.

 Konvergencia és stagnálás

1. Stagnálás észlelése: Ha a moves_accepted nem növekszik egy beállított ablakon keresztül, a local_minima_escapes számláló inkrementálódik és a hőmérsékletet a reheat_factor segítségével visszaállítják.
2. Adaptív hűtés: Ha az acceptance_rate meghaladja a 0.6-ot, a cooling_factor_applied növekszik. Ha 0.2 alá esik, a hűtés lelassul.

---

 8. Szimmetria alrendszer

A Szimmetria alrendszer biztosítja azt a geometriai és algebrai gépezetet, amelyet az ESSO optimalizáló használ a SelfSimilarRelationalGraph-on belüli strukturális szabályosságok detektálására, reprezentálására és kiaknázására. A szimmetriák azonosításával a rendszer összehangolt szimmetria-tudatos lépéseket alkalmazhat, amelyek hatékonyabban fedezik fel a megoldásteret, mint a véletlenszerű perturbációk önmagukban.

 Architekturális szerep

A szimmetria detektálás közvetlenül integrálva van az optimalizációs ciklusba. Minden symmetry_detection_interval iterációban a rendszer elemzi az aktuális gráfállapotot, hogy azonosítsa a csomópontpozíciók és kvantumfázisok ismétlődő mintáit. Ezeket a mintákat azután az applyMove (3-as lépéstípus) tájékoztatására használják.

 Szimmetria reprezentáció

| Entitás | Szerep | Főbb komponensek |
|---|---|---|
| SymmetryGroup | A szimmetria típusának kategorikus osztályozása. | reflection, rotation_90, translation stb. |
| SymmetryTransform | Egy matematikai operátor, amely leképezi a koordinátákat és fázisokat. | origin_x, origin_y, scale_factor, parameters. |
| SymmetryPattern | Egy szimmetria konkrét példánya, amely a gráfban található. | pattern_id (SHA-256), nodes lista, symmetry_score. |

 Detektálás és életciklus

A szimmetria detektálás egy ismétlődő folyamat, amely alkalmazkodik, ahogy a gráf fejlődik a szimulált hűtés során. A detectSymmetries függvény a gráf qubit komponenseinek súlypontját (centroid) használja referenciapontként az invariáns tulajdonságok ellenőrzésére.

 Integráció az optimalizálással

1. Kezdeti detektálás — Egyszer hívódik meg az optimize() elején.
2. Időszakos újra-detektálás — Minden symmetry_detection_interval iterációban aktiválódik.
3. Szimmetria-tudatos lépések — Az applyMove-ban a 3-as lépéstípus kiválaszt egy véletlenszerű SymmetryPattern-t, és alkalmazza annak SymmetryTransform-ját az összes alkotó csomópontra.

---

 9. SymmetryGroup és SymmetryTransform

 SymmetryGroup Enum

A SymmetryGroup enumeráció meghatározza az optimalizáló által támogatott szimmetriák alapvető típusait.

| Tag | Érték | Leírás |
|---|---|---|
| identity | 0 | Nincs transzformáció alkalmazva. |
| reflection | 1 | Tükrözés a parameters[3] által meghatározott tengelyen. |
| rotation_90 | 2 | 90 fokos forgatás az óramutató járásával megegyező irányba. |
| rotation_180 | 3 | 180 fokos forgatás. |
| rotation_270 | 4 | 270 fokos forgatás (vagy 90 fokos ellentétes irányba). |
| translation | 5 | Lineáris eltolás az XY síkban. |

Segédmetódusok:
- toString() — Visszaadja az enum tag karakterlánc reprezentációját.
- fromString(s) — Egy karakterláncot SymmetryGroup taggá elemez, null-t adva vissza egyezés hiányában.
- getAngle() — Visszaadja a forgatás radián egyenértékét. Az identity, reflection és translation 0.0-t ad vissza.
- getOrder() — Visszaadja a csoport rendjét (pl. rotation_90 rendje 4, mert 4 alkalmazás visszatér az identitáshoz). A translation 0-t ad vissza, mivel végtelen rendű egy folytonos térben.

 SymmetryTransform Struct

 Mező definíciók

| Mező | Típus | Leírás |
|---|---|---|
| group | SymmetryGroup | A szimmetria művelet típusa. |
| origin_x | f64 | A transzformáció középpontjának X-koordinátája. |
| origin_y | f64 | A transzformáció középpontjának Y-koordinátája. |
| parameters | [4]f64 | Kiegészítő adatok: [0,1] az eltoláshoz, [2] a skálához, [3] a szöghöz. |
| scale_factor | f64 | A transzformáció során alkalmazott skálázási szorzó. |

Konstrukció:
- init(group) — Létrehoz egy alapértelmezett transzformációt (0,0) origóval, 1.0 skálával és [0, 0, 1, 0] alapértelmezett paraméterekkel.
- initWithParams(group, params) — Létrehoz egy transzformációt egy paramétertömb alapján, automatikusan beállítva az origin_x, origin_y és scale_factor értékeket.

 Térbeli és kvantum alkalmazás

1. applyToComplex(z: Complex(f64)) — Burkolja az apply-t a std.math.Complex típusok kezelésére.
2. applyToQuantumState(state) — Alkalmazza a szimmetriát egy QuantumState-re, kifejezetten a phase mezőt módosítja. Forgatások esetén az új fázis az eredeti fázis plusz a forgatási szög, $[0, 2\pi)$ tartományra normalizálva.

 Algebrai műveletek

Az inverse() metódus egy SymmetryTransform-ot ad vissza, amely megfordítja az eredeti műveletet:
- Forgatások: rotation_90 → rotation_270 és fordítva.
- Skála: Az inverz az 1.0 / scale_factor-t használja.
- Tükrözés / Identitás: Ezek öninverzálóak.

---

 10. SymmetryPattern és szimmetria detektálás

 A SymmetryPattern Struct

 Életciklus és adatszerkezet

- init — Beállítja az ArrayList(u64)-et a csomópontokhoz, és hozzárendel egy létrehozási időbélyeget.
- addNode — Hozzáfűz egy csomópont ID-t a minta taglistájához.
- getPatternIdHex — Egyedi SHA-256 ujjlenyomatot generál a transzformáció paraméterei és a tagcsomópontok rendezett listája alapján.
- deinit — Felszabadítja a csomópontlistához lefoglalt memóriát.

 Főbb mezők

| Mező | Típus | Leírás |
|---|---|---|
| pattern_id | [32]u8 | SHA-256 hash, amely egyedileg azonosítja a minta konfigurációt. |
| transform | SymmetryTransform | A szimmetriát meghatározó geometriai művelet. |
| nodes | ArrayList(u64) | A transzformáció alatt egymásra képeződő csomópontok ID-jainak listája. |
| symmetry_score | f64 | Kvantitatív mérőszám arra vonatkozóan, hogy a szimmetria mennyire tökéletesen fejeződik ki. |
| resonance_frequency | f64 | A detektálás gyakoriságából vagy az iterációk során mutatott stabilitásból származtatott érték. |

 Szimmetria detektáló algoritmus

 1. Súlypont számítás

Az algoritmus a gráf geometriai súlypontjának (centroid) kiszámításával kezdődik. Minden csomópont Qubit-jének re (valós) és im (képzetes) komponensét térbeli koordinátákként $(x, y)$ kezeli.

 2. Minta heurisztikák

- Tükrözés detektálása — A csomópontfokok és a frekvenciakomponensek közötti egyensúly váltja ki. Értékeli, hogy a csomópontok tükrözhetők-e egy a súlyponton áthaladó tengelyen.
- Forgatás (90°/270°) detektálása — Kifejezetten olyan csomópontokat keres, ahol a fok négy többszöröse. Érvényesíti, hogy egy 90 fokos forgatás alkalmazása egy csomópont komplex amplitúdóját egy másik meglévő csomópont állapotára képezi-e le.
- Forgatás (180°) detektálása — A csomópontfázisok körkörös átlagával számítva. Ha a fáziseloszlás erős 2-szeres torzítást mutat, egy 180 fokos transzformációt tesztel.

 3. Deduplikáció és tárolás

Az újonnan detektált mintákat összehasonlítják a meglévő mintákkal SHA-256 ujjlenyomatjuk alapján. Ha egy minta egyedi, hozzáadódik a symmetries listájához; ellenkező esetben a meglévő minta resonance_frequency értéke inkrementálódik.

 Integráció az optimalizációs ciklusban

Időszakos detektálás: Minden symmetry_detection_interval iterációban (alapértelmezés: 100) elindul a detectSymmetries függvény.

Minta hash-elés (getPatternIdHex):
1. A SymmetryGroup és a parameters beírása egy pufferbe.
2. A csomópont ID-k rendezése a nodes listában (hash sorrendtől független legyen).
3. A rendezett csomópontlista betáplálása a std.crypto.hash.sha2.Sha256-ba.

---

 11. Optimalizációs motor

Az Optimalizációs motor az Esso projekt alapvető számítási komponense, amely az EntangledStochasticSymmetryOptimizer köré épül. Egy hibrid metaheurisztikát valósít meg, amely ötvözi a szimulált hűtést a kvantum-ihletésű mechanikával (összefonódás és szimmetria-alapú állapottranszformációk).

A motor feltérképezi egy SelfSimilarRelationalGraph konfigurációs terét egy felhasználó által definiált ObjectiveFunction minimalizálása érdekében.

Konfiguráció és életciklus
Az optimalizálót az EntangledStochasticSymmetryOptimizer struct konfigurálja. Több inicializálási mintát támogat:
- initDefault — Szabványos konstansokat használ (DEFAULT_INITIAL_TEMP = 100.0).
- initWithSeed — Lehetővé teszi a reprodukálható futtatásokat a belső PRNG seed-elésével.

Az optimalizációs ciklus
Az optimize() függvény hajtja végre az elsődleges életciklust. A bemeneti gráf klónozásával és egy kezdeti szimmetria detektálás elvégzésével kezdődik. A fő ciklus iteratívan alkalmazza a perturbációkat, értékeli az energiaváltozásokat, és frissíti az entanglement_map-et.

Lépéstípusok és az UndoLog
A motor hét különböző lépéstípus segítségével fedezi fel a megoldásteret. Az atomicitás biztosítása érdekében az UndoLog rögzíti a változásokat, lehetővé téve az undoMove() számára az állapot visszaállítását.

Elfogadás és hűtés
A motor Metropolis elfogadási kritériumot alkalmaz. Az energiát növelő lépéseket $P = \exp(-\Delta E / T)$ valószínűséggel fogadja el. A $T$ hőmérséklet idővel csökken geometriai hűtés vagy adaptív hűtési stratégia alapján.

---

 12. EntangledStochasticSymmetryOptimizer: Konfiguráció és életciklus

 Alapértelmezett konstansok

| Konstans | Érték | Leírás |
|---|---|---|
| DEFAULT_INITIAL_TEMP | 100.0 | Kezdeti hőmérséklet a hűtési folyamathoz. |
| DEFAULT_COOLING_RATE | 0.95 | A hőmérsékletre minden iterációban alkalmazott szorzó. |
| DEFAULT_MAX_ITERATIONS | 10 000 | A megkísérelendő lépések maximális száma. |
| DEFAULT_MIN_TEMP | 0.001 | A hőmérsékleti padló, ahol a hűtés leáll. |
| DEFAULT_REHEAT_FACTOR | 1.5 | Szorzó a hőmérséklethez stagnálás esetén. |
| DEFAULT_SYMMETRY_INTERVAL | 100 | Iterációk a globális szimmetria detektálási menetek között. |
| DEFAULT_CONVERGENCE_THRESHOLD | 1e-6 | Energia delta, amely alatt a rendszer konvergáltnak tekintendő. |
| DEFAULT_DECAY_HALF_LIFE | 5000.0 | Idő ms-ban, amíg az összefonódás erőssége a felére csökken. |

 Struct mezők

- initial_temperature — A kezdő $T$ a Metropolis kritériumhoz.
- cooling_rate — A termikus bomlás sebessége.
- max_iterations — Szigorú korlát az optimalizációs ciklusra.
- min_temperature — A minimálisan megengedett $T$.
- reheat_factor — A lokális minimumokból való kilépéshez használatos.
- entanglement_decay_half_life — Az EntanglementInfo időbeli bomlásának szabályozása.
- symmetry_detection_interval — A detectSymmetries hívások gyakorisága.
- convergence_threshold — Kritériumok a korai befejezéshez.
- adaptive_cooling — Logikai jelző a dinamikus hűtési sebesség beállítások engedélyezéséhez.
- prng — Egy std.rand.DefaultPrng példány a sztochasztikus lépésekhez.
- energy_history — ArrayList(f64) az energia időbeli nyomon követésére.
- temperature_history — ArrayList(f64) a $T$ hőmérséklet nyomon követésére.

 Életciklus kezelés

 Konstruktor változatok

1. init(allocator, initial_temp, cooling_rate, max_iterations) — Az elsődleges hűtési paraméterek teljes manuális konfigurálása.
2. initDefault(allocator) — Inicializál a DEFAULT_ konstansokkal.
3. initWithSeed(allocator, seed) — Determinisztikus optimalizációs futtatásokhoz.

 Konfigurációs beállítók

| Setter | Leírás |
|---|---|
| setObjectiveFunction(func) | Hozzárendeli az energia kiszámításához használt ObjectiveFunction mutatót. |
| setAdaptiveCooling(enabled) | Átkapcsolja az adaptív hűtési logikát. |
| setMinTemperature(temp) | Felülbírálja az alapértelmezett padlót. |
| setReheatFactor(factor) | Beállítja a lokális minimumból való kilépés szorzóját. |
| setSymmetryDetectionInterval(interval) | Beállítja a geometriai mintakeresés gyakoriságát. |

 De-inicializálás

A deinit() függvényt meg kell hívni az energy_history és a temperature_history listák felszabadításához. Az optimalizáló nem birtokolja az optimize hívás során átadott SelfSimilarRelationalGraph-ot.

 Belső történet nyomon követése

| Mező | Típus | Cél |
|---|---|---|
| energy_history | ArrayList(f64) | Az ObjectiveFunction eredménye minden iterációban. Stagnálás észlelésére. |
| temperature_history | ArrayList(f64) | Az aktuális $T$ hőmérséklet. A hűtési ütemterv és az újramelegítési tüskék vizualizálása. |

---

 13. Az optimalizációs ciklus

Az optimize() függvény az EntangledStochasticSymmetryOptimizer alapvető végrehajtó motorja. Egy speciális szimulált hűtési algoritmust valósít meg, amely integrálja a kvantum-összefonódási dinamikát és a geometriai szimmetria detektálást.

 Magas szintű végrehajtási folyamat

1. Inicializálás — A bemeneti gráf mély klónozása és a kezdeti OptimizationState beállítása.
2. Kezdeti elemzés — Szimmetria detektálás és az összefonódás feltérképezésének első menete.
3. A fő ciklus — Iterálás a max_iterations eléréséig vagy amíg a convergence_threshold nem teljesül:
   - Perturbáció: Egy sztochasztikus lépés kiválasztása és alkalmazása.
   - Értékelés: Az új energia kiszámítása az ObjectiveFunction segítségével.
   - Kiválasztás: A Metropolis kritérium alkalmazása.
   - Karbantartás: Hőmérséklet hűtése és időszakos szimmetria újra-detektálás.
4. Véglegesítés — A legjobbnak talált állapot kinyerése és az ideiglenes erőforrások tisztítása.

 Lépésről lépésre történő implementáció

 1. Beállítás és kezdeti állapot
- Gráf klónozás — A cloneGraph mély másolatot készít az összes csomópontról és élről.
- Állapot beállítás — Az OptimizationState.init meghívásra kerül owns_graph = true értékkel.
- Kezdeti metrikák — A ciklus kiszámítja a kezdeti energiát és feltölti a kezdeti összefonódási térképet.

 2. Szimmetria és összefonódás dinamika
- Összefonódás frissítések — Az updateEntanglementMap meghívásra kerül a régi korrelációk bomlasztására.
- Időszakos szimmetria detektálás — Minden symmetry_detection_interval után a detectSymmetries aktiválódik.

 3. Lépés alkalmazása és Undo logika

| Entitás | Szerep |
|---|---|
| UndoLog | Tárolja az élsúlyok, csomópont állapotok vagy a gráf topológia korábbi értékeit. |
| applyMove() | Módosítja az OptimizationState-et és rögzíti a változásokat az UndoLog-ban. |
| undoMove() | Visszaállítja az állapotot az UndoLog-ból, ha egy lépést elutasítanak. |

 4. Energia értékelés és elfogadás
- Ha $\Delta E < 0$ (javulás): a lépés mindig elfogadásra kerül.
- Ha $\Delta E > 0$: a lépés $P = e^{-\Delta E / T}$ valószínűséggel kerül elfogadásra.

 5. Hűtés és stagnálás kezelése
- Stagnálás számláló — Ha egy bizonyos számú iterációig nem fogadnak el lépést, a stagnation_counter inkrementálódik.
- Újramelegítés — Amikor stagnation_counter >= stagnation_limit, a hőmérsékletet megszorozzák a reheat_factor-ral.
- Konvergencia — Ha az energia delta több iteráción keresztül a convergence_threshold alatt marad, a ciklus korán befejeződik.

 6. Végső kinyerés
1. Az OptimizationState azonosítása a legalacsonyabb best_energy-vel.
2. best_state.cloneGraph() meghívása a hívónak egy tiszta, optimalizált gráfpéldány biztosítása érdekében.
3. deinit() meghívása az összes köztes OptimizationState és UndoLog objektumon.

---

 14. Lépéstípusok és az UndoLog

 Lépéstípusok

Az applyMove függvény hét különböző perturbációs stratégiát (0–6) valósít meg.

| ID | Név | Leírás | Érintett adat |
|---|---|---|---|
| 0 | Élsúly perturbáció | Módosítja egy véletlenszerűen kiválasztott él weight értékét. | Edge.weight |
| 1 | Csomópont fázis perturbáció | Beállítja egy véletlenszerűen kiválasztott csomópont QuantumState-jének phase értékét. | Node.state.phase |
| 2 | Összefonódás létrehozása | Létrehoz egy új EntanglementInfo kapcsolatot két csomópont között. | OptimizationState.entanglement_map |
| 3 | Szimmetria transzformáció | Alkalmaz egy SymmetryTransform-ot egy csomópontra a detektált minták alapján. | Node.state |
| 4 | Amplitúdó perturbáció | Módosítja a qubit amplitúdókat, majd egységvektor normalizálást végez. | Node.state.amplitude_real/imag |
| 5 | Fraktál perturbáció | Véletlenszerűen eltolja egy csomópont fractal_dimension értékét. | Node.fractal_dimension |
| 6 | Él váltás (Toggle) | Hozzáad egy új élt vagy eltávolít egy meglévőt (topológiai változás). | SelfSimilarRelationalGraph |

Implementációs megjegyzések:
- 3-as lépés: Ha rendelkezésre állnak symmetry_patterns, véletlenszerű mintát választ és alkalmazza SymmetryTransform-ját az applyToQuantumState használatával.
- 4-es lépés: A perturbálás után a kvantumállapot normalizálódik 1.0 magnitúdóra.
- 6-os lépés: Ez a legdestruktívabb lépés — teljes gráf pillanatképet igényel az UndoLog-ban.

 Az UndoLog Struct

Az UndoLog egy veremben lefoglalt struktúra az optimize hatókörön belül, amelyet a módosított entitások korábbi állapotának tárolására használnak.

Főbb függvények:
- clear() — Visszaállítja a naplót a következő iterációhoz. Ha old_graph jelen van (6-os típusú lépésből), meghívja a deinit() függvényt a pillanatképen.
- undoMove() — A move_type alapján specifikus helyreállítási logikához irányít.

Visszaállítás típusonként:
- 0, 1, 4, 5 típusok — Végigiterál a node_states vagy edge_weights elemeken és visszaállítja az értékeket.
- 2-es típus — Eltávolítja az entanglement_map-ből a lépés során hozzáadott kulcsokat.
- 6-os típus — Kicseréli az aktuális gráfot a naplóban tárolt old_graph-ra; a sérült gráf de-inicializálódik.

 Memóriabiztonság

1. Tulajdonjog csere — A 6-os típusú lépéseknél az OptimizationState feladja az aktuális gráfját és átveszi az old_graph-ot.
2. errdefer használata — Ha egy allokáció meghiúsul a lépés alkalmazása során, az errdefer biztosítja, hogy minden részlegesen módosított állapotot kezeljék.
3. Pillanatkép kezelés — Az old_graph mező Optional; csak topológiai lépések során töltődik fel, hogy a cloneGraph magas költségét csak szükség esetén fizessék meg.

---

 15. Elfogadási kritérium és hőmérséklet-ütemezés

 Metropolis elfogadási kritérium

Az optimalizáló a Metropolis-Hastings kritériumot alkalmazza az acceptMove függvényen belül.

Implementációs logika:
1. Ha $\Delta E \leq 0$: a lépés mindig elfogadásra kerül (valószínűség = 1.0).
2. Ha $\Delta E > 0$: a lépés $P = \exp(-\Delta E / T)$ valószínűséggel kerül elfogadásra.

A kód egy véletlenszerű lebegőpontos számot generál 0.0–1.0 között, és összehasonlítja a kiszámított valószínűséggel.

 Hőmérséklet-ütemezési stratégiák

 1. Szabványos geometriai hűtés

Amikor adaptive_cooling = false:

$$T_{n+1} = T_n \times \text{cooling\_rate}$$

 2. Adaptív hűtés

Az adaptiveCoolTemperature függvény beállítja a hűtési sebességet a legutóbbi acceptance_rate alapján:

| Elfogadási arány | Művelet | Logika |
|---|---|---|
| Magas (> 0.6) | Hűtés gyorsítása | $T = T \times (\text{cooling\_rate} \times 0.95)$ |
| Alacsony (< 0.2) | Hűtés lassítása | $T = T \times (1.0 - (1.0 - \text{cooling\_rate}) \times 0.5)$ |
| Normál (0.2–0.6) | Szabványos hűtés | $T = T \times \text{cooling\_rate}$ |

 Újramelegítés és stagnálás kezelése

Ha az energia nem javul a stagnation_limit (alapértelmezés: 100) által meghatározott számú iteráción keresztül, egy újramelegítés (reheat) aktiválódik:

- Az aktuális hőmérsékletet megszorozzák a reheat_factor-ral (alapértelmezés: 1.5 vagy 2.0).
- A hőmérséklet soha nem eshet a min_temperature alá.

---

 16. Célfüggvények

Az ESSO optimalizáló egy ObjectiveFunction-t használ egy adott állapot energiájának számszerűsítésére. Az alacsonyabb energiaértékek kívánatosabb állapotokat képviselnek.

 Az ObjectiveFunction típus

Az esso_optimizer.zig-ben az ObjectiveFunction egy függvénymutatóként van definiálva, amely egy csak olvasható mutatót vesz át az aktuális OptimizationState-re, és egy f64 energiaértéket ad vissza.

Az OptimizationState hozzáférést biztosít a teljes gráf topológiához, a csomópontfázisokhoz, a qubit amplitúdókhoz és az aktuális összefonódási térképhez.

 Beépített célfüggvények

| Függvény | Elsődleges cél | Főbb metrikák |
|---|---|---|
| defaultGraphObjective | Általános egyensúly | Élsúlyok, fraktáldimenziók, csomópontfázisok. |
| connectivityObjective | Topológia | Él-csomópont arány és átlagos kapcsolati erősség. |
| quantumCoherenceObjective | Kvantum stabilitás | Qubit amplitúdó magnitúdó és összefonódási korrelációk. |
| fractalDimensionObjective | Önhasonlóság | Eltérés egy cél fraktáldimenziótól (1.5). |

 Egyéni célfüggvények

A felhasználók implementálhatják saját logikájukat. Egy egyéni függvény injektálása az setObjectiveFunction segítségével lehetséges, vagy közvetlenül átadható az optimize metódusnak.

---

 17. Beépített célfüggvények

 1. defaultGraphObjective

Általános célú energiafüggvény, amely kiegyensúlyozza a strukturális tulajdonságokat (élsúlyok) a kvantumtulajdonságokkal (csomópontfázisok) és a geometriai komplexitással (fraktáldimenziók).

$$E = \sum \text{edge\_weights} + \sum \sin(\text{node\_phases}) + \sum |\text{fractal\_dimension} - 1.0|$$

Implementációs részletek:
- Élsúlyok — Végigiterál a gráf összes élén és összegzi a weight értékeket.
- Csomópontfázisok — Hozzáadja a csomópont QuantumState-jének phase attribútumának szinuszát.
- Fraktáldimenzió — Bünteti azokat a csomópontokat, ahol a fractal_dimension eltér az 1.0-s alapvonaltól.

 2. connectivityObjective

A gráf topológiájának optimalizálására tervezve, előnyben részesítve a jól kapcsolódó gráfokat kiváló minőségű kapcsolatokkal.

$$E = \frac{1.0}{1.0 + (\text{edge\_count} / \text{node\_count})} + \frac{1.0}{1.0 + \text{avg\_edge\_weight}}$$

Jellemzők:
- Sűrűség büntetés — Ahogy az élek és csomópontok aránya növekszik, az első tag a nulla felé közelít.
- Súly büntetés — Ahogy az élek átlagos súlya növekszik, a második tag a nulla felé közelít.
- Biztonság — Ellenőrzések a nullával való osztás megakadályozására, ha a gráf üres.

 3. quantumCoherenceObjective

A gráfban lévő kvantumállapotok stabilitására és korrelációjára összpontosít.

$$E = (1.0 - \text{avg\_amplitude}) + (1.0 - \text{entanglement\_percentage}) + \sum \text{phase\_variance}$$

Implementációs komponensek:
- Amplitúdó magnitúdó — Átlagos magnitúdó: $\sqrt{re^2 + im^2}$. A magasabb amplitúdók csökkentik az energiát.
- Globális összefonódás — Az OptimizationState által kiszámított entanglement_percentage-et használja.
- Fázis koherencia — Méri a fázisok varianciáját. Az alacsonyabb variancia alacsonyabb energiát eredményez.

 4. fractalDimensionObjective

Az 1.5-ös fraktáldimenziót tekinti ideális állapotnak (az egyszerű euklideszi geometria és a komplex térkitöltő zaj közötti egyensúly).

$$E = \sum |\text{node.fractal\_dimension} - 1.5|$$

Implementáció:
- Végigiterál minden csomóponton a state.graph.nodes-ban.
- Kiszámítja az abszolút különbséget a csomópont fractal_dimension értéke és az 1.5 konstans között.
- Az összegzés a teljes gráfot egy egységes fraktál komplexitás felé mozdítja.

---

 18. Egyéni célfüggvények

 Áttekintés

Egy egyéni célfüggvény teljes, csak olvasható hozzáféréssel rendelkezik az OptimizationState-hez:

| Adat | Típus | Leírás |
|---|---|---|
| graph | SelfSimilarRelationalGraph | A csomópontokat és éleket tartalmazó alap gráfstruktúra. |
| entanglement_map | AutoHashMap(NodePairKey, EntanglementInfo) | Nyomon követi az aktív kvantumkorrelációkat a csomópontok között. |
| entanglement_percentage | f64 | Az összefonódott párok aránya az összes lehetséges párhoz képest. |
| iteration | usize | Az aktuális lépés az optimalizációs ciklusban. |

 Az egyéni függvény injektálása

1. A setObjectiveFunction használata — A célfüggvényt bármikor megváltoztathatja az optimize() meghívása előtt.

2. Átadás az optimize()-nak — Az optimize függvény elfogad egy opcionális ObjectiveFunction-t. Ha null-t ad át, a defaultGraphObjective-ra alapértelmeződik.

 Bevált gyakorlatok energiafüggvényekhez

1. Numerikus stabilitás — Kerülje az inf vagy nan visszaadását. Érvénytelen állapotra adjon vissza magas véges értéket (pl. 1e10).
2. Simaság — A csomópontfázisok vagy élsúlyok kis változásainak ideális esetben kis energiaváltozásokat kell eredményezniük. A nem folytonos energiatájképek megnehezítik az optimalizáló számára a gradiensek megtalálását.
3. Normalizálás — Az optimalizáló alapértelmezett kezdeti hőmérséklete 100.0. Törekedjen a 0.1 és 10.0 közötti energia deltákra.
4. Hatékonyság — A célfüggvény minden iterációban meghívásra kerül (legfeljebb max_iterations-ig, alapértelmezés: 10 000). Kerülje az $O(N^2)$ műveleteket; használja az előre kiszámított entanglement_percentage-et a térkép újra-iterálása helyett.

---

 19. Memóriakezelés és biztonság

Az ESSO egy explicit memóriakezelési modellt alkalmaz, amely a Zig Allocator interfészén alapul. A rendszer szigorú tulajdonosi mintát használ a memóriaszivárgások és lógó mutatók (dangling pointers) megelőzésére.

 Fő biztonsági mechanizmusok

1. Explicit tulajdonjogi jelzők — Az OptimizationState struct tartalmaz egy owns_graph logikai értéket. Ha true, a deinit() metódus meghívja a graph.deinit() függvényt.
2. Hiba halasztások (errdefer) — Az allokációs logika során az errdefer a részlegesen lefoglalt struktúrák tisztítására szolgál, ha egy al-allokáció meghiúsul.
3. Pillanatkép készítés — Komplex lépések (pl. toggleRandomEdge) során az UndoLog rögzíti a gráf teljes mély másolatát a cloneGraph használatával.

 Kód entitás leképezés

| Fogalom | Kód entitás |
|---|---|
| Mély másolás segédprogram | cloneGraph(allocator, source) |
| Állapot duplikáció | OptimizationState.clone(allocator) |
| Minta perzisztencia | SymmetryPattern.clone(allocator) |
| Visszaállítási puffer | UndoLog |
| Tisztítási logika | deinit() (minden fő struct-on implementálva) |

---

 20. Tulajdonosi modell és mély másolás

 Allocator-Per-Struct minta

Minden dinamikus memóriafoglalást igénylő struct tárol egy hivatkozást egy std.mem.Allocator-ra, és biztosít init és deinit metódusokat.

Az ezt a mintát követő főbb entitások:
- OptimizationState — Kezeli a gráfot és az összefonódási térképeket.
- SymmetryPattern — Kezeli a detektált szimmetriában részt vevő csomópontok listáit.
- EntangledStochasticSymmetryOptimizer — Kezeli a történeti puffereket és a PRNG állapotot.

 Gráf mély másolása a cloneGraph() segítségével

A cloneGraph() függvény a következő lépéseket hajtja végre:

1. Inicializálás — Létrehoz egy új SelfSimilarRelationalGraph-ot a megadott allokátor használatával.
2. Csomópont klónozás — Végigiterál a forrásgráf összes csomópontján és meghívja a node.clone(allocator) függvényt.
3. Él klónozás — Végigiterál az összes éllistán és meghívja az edge.clone(allocator) függvényt.
4. Metaadat átvitel — Átmásolja a topology_hash-t a hash-elési célokra való megkülönböztethetőség biztosítása érdekében.

 OptimizationState tulajdonjog és owns_graph

| Mező | Cél |
|---|---|
| graph | Mutató a SelfSimilarRelationalGraph példányra. |
| owns_graph | Meghatározza, hogy a deinit() meghívja-e a graph.deinit() függvényt. |
| entanglement_map | Egy hash map, amely az EntanglementInfo-t tárolja a csomópontpárokhoz. |

Életciklus logika:
- init() — Jellemzően true-ra állítja az owns_graph értékét, ha az állapot felelős a gráf memóriájáért.
- deinit() — Felszabadítja az entanglement_map-et; ha owns_graph igaz, meghívja a graph.deinit() függvényt is.
- clone() — Létrehoz egy új OptimizationState-et mélyen másolt gráffal és duplikált összefonódási térképpel.

 Biztonsági minták és hibakezelés

| Függvény | Allokációs cél | Biztonsági mechanizmus |
|---|---|---|
| cloneGraph | new_graph | errdefer new_graph.deinit() |
| SymmetryPattern.clone | cloned.nodes | errdefer self.allocator.destroy(cloned) |
| OptimizationState.clone | new_state | errdefer new_state.deinit() |

---

 21. UndoLog memóriabiztonság

Az UndoLog biztosítja a memóriabiztonságot és az állapotkonzisztenciát az iteratív optimalizációs folyamat során, lehetővé téve a SelfSimilarRelationalGraph korábbi állapotának visszaállítását memóriaszivárgás vagy lógó mutatók nélkül.

 Adatfolyam: Lépés alkalmazása és visszaállítása

Az optimalizációs ciklus egy szigorú Alkalmaz–Értékel–Visszaállít mintát követ:

1. Inicializálás — Egy UndoLog inicializálódik, mielőtt egy lépést megkísérelnének.
2. Lépés alkalmazása — Az applyMove feltölti a naplót. Egyszerű perturbációk esetén a korábbi értékeket az edge_weights vagy node_states mezőkben tárolja. Topológiai változások esetén a teljes gráfot az old_graph-ba klónozza.
3. Értékelés — Az acceptMove függvény meghatározza, hogy a lépés megmarad-e.
4. Visszaállítás — Ha az acceptMove false-t ad vissza, az undoMove meghívásra kerül.
5. Tisztítás — A defer log.deinit() biztosítja, hogy a naplón belül lefoglalt összes memória felszabaduljon.

 A 6-os lépéstípus (toggleRandomEdge) kezelése

Mivel a SelfSimilarRelationalGraph komplex belső térképeket használ a szomszédsághoz, egy egyszerű attribútum visszaállítás nem elegendő.

Pillanatkép mechanizmus: Az UndoLog létrehozza a gráf teljes mély másolatát a cloneGraph használatával, amelyet az old_graph mező tárol.

Memóriabiztonság az undoMove-ban:
1. Az aktuális (módosított) gráf de-inicializálódik.
2. Az OptimizationState.graph mutató frissül, hogy az old_graph pillanatképre mutasson.
3. A naplóban lévő old_graph mező null-ra van állítva a dupla felszabadítás megakadályozása érdekében.

 Életciklus és erőforrás-kezelés

| Függvény | Felelősség |
|---|---|
| UndoLog.init | Lefoglalja a HashMap és ArrayList struktúrákat. |
| UndoLog.clear | Felszabadítja az old_graph pillanatképet és törli a térkép bejegyzéseket. |
| UndoLog.undoMove | Visszaállítja az állapotot az OptimizationState-be a move_type alapján. |
| UndoLog.deinit | A napló által birtokolt összes memória végső felszabadítása. |

---

 22. Szójegyzék

 Alapvető tartományi kifejezések

Összefonódás (Entanglement)
Az ESSO kontextusában az összefonódás egy kiszámított korrelációra utal két csomópont között egy SelfSimilarRelationalGraph-ban. A tiszta kvantum-összefonódással ellentétben ez egy szimulált metrika, amelyet az optimalizációs lépések torzítására használnak.
- Korrelációs erősség — A kapcsolat intenzitásának skaláris értéke.
- Fáziskülönbség — A relatív különbség a kvantumfázisok között két összefonódott csomópontnál.
- Bomlási tényező — Felezési idő képlettel kiszámított érték az összefonódás erősségének időbeli csökkentésére.

Szimmetria transzformáció (Symmetry Transformation)
A gráf állapotára alkalmazott geometriai vagy algebrai művelet, amelyet az optimalizáló nagy léptékű lépések végrehajtásához használ.
- Szimmetriacsoport — Támogatott transzformációk: identity, reflection, rotation_90, rotation_180, rotation_270, translation.
- Izometria — Távolságokat megőrző transzformáció.

Szimulált hűtés (Simulated Annealing)
- Hőmérséklet ($T$) — Globális paraméter, amely szabályozza a rossz lépések elfogadásának valószínűségét.
- Hűtési sebesség (Cooling Rate) — Az a tényező, amellyel a hőmérsékletet minden iterációban megszorozzák.
- Újramelegítés (Reheat) — Mechanizmus a lokális minimumokból való kilépésre a $T$ hirtelen növelésével.

 Technikai definíciók

| Kifejezés | Implementációs részlet |
|---|---|
| NodePairKey | Struct, amely biztosítja a csomópont ID-k kanonikus rendezését (kisebb ID először), hogy a párokat irányítatlanként kezelje. |
| UndoLog | Memento struktúra, amely tárolja a módosított csomópontok/élek korábbi állapotát, lehetővé téve az elutasított lépések $O(1)$ vagy $O(N)$ visszaállítását. |
| Metropolis kritérium | Az acceptMove-ban lévő logika: $P(\text{accept}) = \exp(-\Delta E / T)$. |
| Stagnálás | Állapot, ahol a best_energy nem javult stagnation_limit iteráción keresztül. |
| Fraktáldimenzió | A gráf egy tulajdonsága, amelyet a fractalDimensionObjective-ben használnak a nem optimális strukturális komplexitás büntetésére. |

 Zig idiómák a kódbázisban

errdefer
Kiterjedten használják a memóriabiztonság érdekében komplex allokációk során. Ha egy többlépéses inicializálás félúton meghiúsul, az errdefer biztosítja a korábban lefoglalt memória felszabadítását.

Példa: A cloneGraph-ban a new_graph inicializálódik, és az errdefer new_graph.deinit() biztosítja a tisztítást, ha a csomópont/él klónozás meghiúsul.

Payload minták
Az optimalizáló gyakran használja a while (iter.next()) |entry| vagy if (opt) |val| szerkezeteket az opcionális típusok és hash map bejegyzések biztonságos kicsomagolására.

Allokátor átadása
A Zig filozófiájával összhangban nincsenek rejtett allokációk. Minden memóriát igénylő struct elfogad egy Allocator-t az init vagy clone metódusaiban.
