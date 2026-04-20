r_gpu – Teljes dokumentáció (Magyar)

> Forrás: [https://deepwiki.com/kollarsandor/r_gpu](https://deepwiki.com/kollarsandor/r_gpu) > Generálva: **2026**-04-17

---

 Áttekintés

Az r_gpu projekt egy specializált hardver-szoftver co-design szimulációs környezet egy Relational Graph Processing Unit (Relációs Gráf Feldolgozó Egység) számára. Arra tervezték, hogy nagyléptékű gráfelemzési feladatokat – mint például az izomorfizmus-detektálás és a dinamikus él-súlyozás (dynamic edge weighting) – kezeljen a tágabb Jaide ökoszisztémán belül.

A rendszer egy aszinkron Network-on-Chip (NoC) architektúrát szimulál, ahol a gráfpéldányok adatai egy processing core-okból (feldolgozó magokból) álló rácson (grid) oszlanak el. A nagy hatékonyságú végrehajtásra fókuszál, amit az energiagazdálkodásért és a ritka aktivációért (sparse activation) felelős specializált alrendszerek révén ér el.

 Rendszer szerepe és kontextusa

Az r_gpu nagy teljesítményű backendként szolgál az nsir_core függőségben definiált SelfSimilarRelationalGraph struktúrák feldolgozásához. Egy elosztott core grid szimulálásával lehetővé teszi olyan párhuzamos gráfalgoritmusok felfedezését, amelyek az energiahatékonyságot és az alacsony késleltetésű kommunikációt helyezik előtérbe.

 Fő komponensek

A projekt több elkülönülő rétegre tagolódik, amelyek a gráffeldolgozás életciklusát kezelik:

## Orchestration Layer (Hangszerelési réteg): A RelationalGraphProcessingUnit struct az elsődleges belépési pontként működik, koordinálva az adatáramlást a NoC és az analitikai alrendszerek között.

## Communication Layer (Kommunikációs réteg): Az AsynchronousNoC egy 2D mesh hálózatot kezel a ProcessingCore egységekből, XY routing használatával továbbítva a NoCMessage csomagokat. ## Analysis Subsystems (Analitikai alrendszerek): Specializált modulok a GraphIsomorphismProcessor (strukturális hasonlóságok keresése) és a DynamicEdgeWeighting (gráfkapcsolatok visszacsatolás alapján történő módosítása) számára. ## Efficiency Subsystems (Hatékonysági alrendszerek): A SparseActivationManager és a PowerGatingController együttműködve csökkentik az energiafogyasztást az alacsony terhelésű feladatok kihagyásával és az üresjáratban lévő core-ok leállításával.

---

 A projekt célja és tervezési célkitűzései

Az r_gpu projekt egy hardver-szoftver co-design szimuláció egy Relational Graph Processing Unit számára. Egy olyan specializált architektúra szimulálására tervezték, amelyet elosztott gráffeldolgozásra optimalizáltak, és amely aszinkron Network-on-Chip (NoC) hálózattal, valamint fejlett energiagazdálkodási stratégiákkal rendelkezik.

 Cél és hatókör

Az r_gpu elsődleges célja egy nagy teljesítményű szimulációs környezet biztosítása nagyléptékű relációs gráfok feldolgozásához, specializált processing core-ok hálózatának használatával. A sűrű lineáris algebrában jeleskedő hagyományos **GPU**-kkal ellentétben az **RGPU** a relációs gráfelméletben gyakori ritka (sparse), szabálytalan adatstruktúrákra van szabva.

 Szerepe a Jaide ökoszisztémában

Az r_gpu a nagyobb Jaide projekt egyik komponense. Hardver-szimulációs rétegként szolgál, amely az nsir_core könyvtárban definiált gráf-primitíveken operál. Alapvető adatmodelljeihez, beleértve a SelfSimilarRelationalGraph, Node és EdgeQuality típusokat, az nsir_core.zig-re támaszkodik.

 Hardver-szoftver Co-design

A projekt egy szorosan csatolt rendszert szimulál, ahol a szoftveres algoritmusok (mint a gráf izomorfizmus detektálása) tisztában vannak a mögöttes hardveres korlátokkal (mint a NoC routing késleltetése és az energiakeretek). Ez lehetővé teszi a következők felfedezését:
- Spatial Graph Partitioning (Térbeli gráf particionálás): A globális gráfadatok elosztása a ProcessingCore egységek 2D mesh hálózatán.
- Asynchronous Execution (Aszinkron végrehajtás): Node-ok és edge-ek feldolgozása globális szinkronizációs korlátok nélkül.
- Energy-Aware Scheduling (Energia-tudatos ütemezés): A hardveres erőforrások dinamikus kapuzása (gating) a terhelési jellemzők alapján.

 Fő tervezési célkitűzések

Az architektúrát három fő tervezési cél vezérli: energiahatékonyság, sparse activation és aszinkron kommunikáció.

 1. Energiahatékonyság és energiagazdálkodás
A nagyléptékű gráfbejárások magas energiaköltségének minimalizálása érdekében a rendszer egy PowerGatingController-t implementál.
- Power Gating: A core-ok power_gated állapotba kapcsolhatók, ami egy fix egységgel (szimulálva 10.0 egység) csökkenti a rendszer aktuális áramfelvételét.
- Budgeting (Költségvetés): A RelationalGraphProcessingUnit egy globális power_budget-et kezel, biztosítva, hogy a grid teljes fogyasztása ne lépje túl a termikus vagy elektromos korlátokat.

 2. Sparse Activation
A gráf-munkaterhelések gyakran rendkívül szabálytalanok, a gráf jelentős részei statikusak maradnak. A SparseActivationManager a következőképpen optimalizálja a végrehajtást:
- Workload Thresholding (Terhelés küszöbözése): Egy core getWorkload() értékének elemzése egy sparsity_threshold (ritkasági küszöb) alapján.
- Skipping Idle Work (Üresjárati munka kihagyása): Ha egy core terhelése a küszöbérték alatt van, a rendszer kihagyja a feldolgozási ciklusát, és növeli az energy_saved metrikát.

 3. Aszinkron kommunikáció
A rendszer egy AsynchronousNoC-ot használ a core-ok közötti adatmozgatás kezelésére.
- XY Routing: A csomagok determinisztikus útvonalat követnek (először X-tengely, majd Y-tengely), hogy elkerüljék a deadlockokat a mesh topológiában.
- Priority-Based Messaging (Prioritás alapú üzenetküldés): A NoCMessage struct különböző MessageType értékeket támogat, amelyeket egy PriorityQueue priorizál, biztosítva, hogy a kritikus vezérlőjelek (mint a power_control) a tömeges data_transfer előtt kézbesítésre kerüljenek.

 Adatáramlás: Globálistól a lokális feldolgozásig

A RelationalGraphProcessingUnit hangszereli az adatok áramlását egyetlen globális gráfból egy elosztott, energiagazdálkodással rendelkező szimulációba.

 A tervezési implementáció összefoglalása

| Cél | Implementációs stratégia | Főbb kód entitások |
| --- | --- | --- |
| Distributed Graphing | Globális gráfok particionálása local_graph szegmensekre core-onként. | RelationalGraphProcessingUnit.distributeGraph, ProcessingCore.local_graph |
| Scalable Interconnect | 2D Mesh topológia XY-routinggal a kiszámítható késleltetés érdekében. | AsynchronousNoC, computeXYRoute |
| Sparsity Optimization | Számítások kihagyása az alacsony aktivitású core-oknál. | SparseActivationManager, getWorkload |
| Relational Analysis | Kanonikus forma kiszámítása a strukturális azonossághoz. | GraphIsomorphismProcessor, computeCanonicalForm |
| Dynamic Learning | Az él-súlyok megerősítése visszacsatolási hurkok alapján. | DynamicEdgeWeighting, updateWeight |

---

 Első lépések

Az r_gpu projekt egy Zig nyelven implementált hardver-szoftver co-design szimuláció. Egy energiahatékony, elosztott gráffeldolgozásra tervezett Relational Graph Processing Unit-ot (**RGPU**) szimulál. Ez az útmutató bemutatja a fejlesztőknek az r_gpu.zig környezetbe történő integrálásához, a függőségek kezeléséhez és egy alapvető feldolgozási folyamat végrehajtásához szükséges lépéseket.

 Build és függőségek

Az r_gpu rendszer a Zig programozási nyelv használatával épül fel, és a Zig Standard Library-re, valamint egy alapvető relációs gráf könyvtárra támaszkodik.

 Előfeltételek
- Zig Compiler: 0.11.0 vagy újabb verzió ajánlott.
- Standard Library függőségek: A rendszer kiterjedten használja a következő Zig std komponenseket:
    - std.ArrayList és std.AutoHashMap az adattároláshoz.
    - std.PriorityQueue a NoC üzenetek ütemezéséhez.
    - std.mem.Allocator a manuális memóriakezeléshez.

 Külső függőség: nsir_core.zig
Az **RGPU** nem definiál saját gráf-primitíveket. Ehelyett az nsir_core adatmodellt importálja és terjeszti ki. Biztosítani kell, hogy az nsir_core.zig szerepeljen az include útvonalon. A legfontosabb importált típusok:
- SelfSimilarRelationalGraph: Az elsődleges gráftároló.
- Node, Edge és EdgeQuality: A gráf alapvető egységei.
- Qubit: A gráf node-jain belüli szemantikus reprezentációra szolgál.

 Rendszer inicializálási folyamat

Az **RGPU** használatához először inicializálni kell egy RelationalGraphProcessingUnit-ot. Ez magában foglalja a ProcessingCore entitások 2D mesh hálózatának beállítását és a Network-on-Chip (NoC) routing tábláinak előkiszámítását.

 Minimális használati példa

A standard munkafolyamat magában foglalja a RelationalGraphProcessingUnit példányosítását, egy gráf betöltését, és a processGraph() meghívását. Ez a metódus hangszereli a belső folyamatot: a gráf particionálását, az izomorfizmusok detektálását, a súlyok frissítését és az energiagazdálkodást.

 Implementációs példa

zig const std = @import(*std*); const r_gpu = @import(*r_gpu.zig*);

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();

    // 1. Az **RGPU** inicializálása (4x4-es core grid)
    var rgpu = try r_gpu.RelationalGraphProcessingUnit.init(allocator, 4, 4);
    defer rgpu.deinit();

    // 2. Globális gráf beállítása (nsir_core típusok használatával)
    var global_graph = try r_gpu.SelfSimilarRelationalGraph.init(allocator);
    defer global_graph.deinit();
    
    // ... node-ok és edge-ek hozzáadása a global_graph-hoz ...

    // 3. Gráf hozzárendelése az **RGPU**-hoz
    rgpu.global_graph = &global_graph;

    // 4. A feldolgozási folyamat végrehajtása
    // Ez belsőleg meghívja a distributeGraph, processIsomorphismParallel, 
    // updateEdgeWeightsParallel és synchronizeGraphs függvényeket.
    try rgpu.processGraph();

    // 5. Eredmények lekérése
    const stats = rgpu.getStatistics();
    std.debug.print(*Energy Consumed: {d}\n*, .{stats.total_energy_consumed});
}

 A processGraph() folyamat

A processGraph() függvény az elsődleges belépési pont a végrehajtáshoz. Az adatáramlást a következő szakaszokon keresztül kezeli:

1. distributeGraph(): Particionálja a global_graph-ot és részgráfokat rendel a ProcessingCore.local_graph-hoz.
2. processIsomorphismParallel(): Strukturális mintákat azonosít a core-okon keresztül a GraphIsomorphismProcessor segítségével.
3. updateEdgeWeightsParallel(): Beállítja a relációs erősségeket a lokális core aktivitás alapján.
4. propagateWeightsAsync(): Az AsynchronousNoC-ot használja a weight_update üzenetek küldésére a core-ok között.
5. synchronizeGraphs(): A feldolgozott local_graph adatokat visszamergeli a global_graph-ba.

 Memóriakezelés

Az **RGPU** manuális memóriakezelést használ. Amikor a RelationalGraphProcessingUnit.init meghívásra kerül, lefoglalja a core gridet és a routing táblákat.

- Ownership (Tulajdonjog): A ProcessingCore hivatkozhat egy külső gráfra, vagy birtokolhat egyet. A local_graph_owned logikai érték határozza meg, hogy a core meghívja-e a deinit()-et a local_graph-ján a saját deinit() ciklusa során.
- Cleanup (Takarítás): Mindig hívd meg az rgpu.deinit()-et az AsynchronousNoC, az összes ProcessingCore struktúra, és az izomorfizmus kanonikus formáihoz használt belső StringHashMap gyorsítótárak felszabadításához.

---

 Alaparchitektúra

A Relational Graph Processing Unit (**RGPU**) egy hardver-szoftver co-design szimuláció elosztott gráffeldolgozáshoz. Rétegzett architektúrát alkalmaz, ahol egy központi koordinátor egy aszinkron Network-on-Chip (NoC) hálózaton keresztül összekapcsolt processing core-ok mesh-gridjét kezeli. A rendszert a relációs gráfalgoritmusok energiahatékony végrehajtására tervezték, sparse activation és power gating használatával az energiafogyasztás minimalizálása érdekében olyan komplex műveletek során, mint az izomorfizmus-detektálás és a dinamikus él-súlyozás.

 1. Top-Level Coordinator (**RGPU**)

A RelationalGraphProcessingUnit (**RGPU**) a rendszer agyaként szolgál. Hangszereli az adatok áramlását a global_graph-ból az elosztott mesh-be. Magas szintű **API**-t biztosít a gráffeldolgozáshoz, absztrahálva a párhuzamos végrehajtás, az üzenetküldés és az energiagazdálkodás bonyolultságát.

A rendszer elsődleges belépési pontja a processGraph(), amely egy szekvenciális folyamatot hajt végre: ## Graph Distribution: A global_graph particionálása a ProcessingCore példányok között. ## Isomorphism Detection: Strukturálisan hasonló részgráfok párhuzamos keresése. ## Edge Weighting: Megerősítéses tanuláson alapuló frissítések az él-súlyokon. ## Asynchronous Propagation: A súlyfrissítések mozgatása a NoC-on keresztül. ## Synchronization: Az eredmények visszamergelése a globális állapotba.

 2. Communication Fabric (NoC)

A core-ok közötti kommunikációt az AsynchronousNoC kezeli. Ez az alrendszer egy 2D mesh topológiát implementál, ahol minden ProcessingCore-t az (x, y) koordinátái azonosítanak. Egy előre kiszámított routing táblát használ, amely XY-routingon alapul (először vízszintes, majd függőleges haladás), hogy biztosítsa a deadlock-mentes üzenetkézbesítést.

Az üzeneteket a NoCMessage objektumok PriorityQueue-ja priorizálja, öt különböző típust támogatva a weight_update-től a power_control-ig.

 3. Processing Cores and State

A ProcessingCore a számítás alapvető egysége. Minden core fenntartja a saját local_graph-ját (a globális relációs adatok egy részhalmazát), és a CoreState enum által definiált állapotgépként működik:
- idle: Készen áll a munkára.
- processing: Aktívan végez gráfszámításokat.
- communicating: Üzeneteket küld vagy fogad a NoC-on keresztül.
- power_gated: Kikapcsolva az energiatakarékosság érdekében.

 4. Analytical Subsystems

Az **RGPU** specializált logikát ágyaz be a relációs gráfelemzéshez:
- GraphIsomorphismProcessor: Kanonikus formákat használ (a node-ok fokszáma és az edge-ek minősége alapján) a részgráfok közötti strukturális azonosság detektálására.
- DynamicEdgeWeighting: Egy adaptív súlyozási mechanizmust implementál, ahol az Edge fontossága temporális, térbeli és szemantikus visszacsatolás alapján frissül.

 5. Efficiency and Energy Management

A hardveres korlátok szimulálása és a teljesítmény optimalizálása érdekében az architektúra két dedikált vezérlőt tartalmaz:
- SparseActivationManager: Elemzi a core-ok workload-ját. Ha egy core terhelése a sparsity_threshold alá esik, a rendszer megkerüli a ciklusok megtakarítása érdekében.
- PowerGatingController: Egy globális power_budget-et kezel. Dinamikusan kapuzza az alacsony kihasználtságú core-ok áramellátását, és visszakapcsolja őket, amikor a kereslet megnő.

 6. Graph Data Model

A rendszer egy SelfSimilarRelationalGraph-ot dolgoz fel, amely Node és Edge entitásokból áll. Ezek az nsir_core modulból vannak importálva. Az **RGPU** a *Self-Similar* (önhasonló) aspektus kezelésére specializálódott, ezeket a gráfokat lokális kontextusokra particionálva, miközben fenntartja a globális szemantikai integritást.

---

 RelationalGraphProcessingUnit (**RGPU**)

A RelationalGraphProcessingUnit (**RGPU**) a rendszer legfelső szintű koordinátora. Hangszereli a Network-on-Chip (NoC) kommunikációs hálózat, a specializált gráffeldolgozó alrendszerek és az energiagazdálkodási vezérlők közötti interakciót a nagyléptékű relációs gráfok elosztott, energiahatékony módon történő feldolgozása érdekében.

 Áttekintés és mezők

A RelationalGraphProcessingUnit struct a szimuláció központi csomópontjaként működik, hivatkozásokat tartva az összes főbb architekturális komponensre.

| Mező | Típus | Leírás |
| --- | --- | --- |
| noc | AsynchronousNoC | A kommunikációs hálózat, amely összekapcsolja az összes processing core-t. |
| isomorphism_processor | GraphIsomorphismProcessor | Alrendszer a gráfok strukturális hasonlóságainak detektálására. |
| edge_weighting | DynamicEdgeWeighting | Logika a megerősítéses tanuláson alapuló él-súly frissítésekhez. |
| sparse_activation | SparseActivationManager | Vezérlő a végrehajtás kihagyására az alacsony terhelésű core-okon. |
| power_gating | PowerGatingController | Logika az üresjárati core-ok leállítására az energiatakarékosság érdekében. |
| global_graph | SelfSimilarRelationalGraph | Az egység által feldolgozott elsődleges gráf. |

 Életciklus: Init és Deinit

Az **RGPU** inicializálása magában foglalja a NoC grid beállítását és az összes belső menedzser inicializálását a megadott allokátorral.

- init(allocator, width, height): Lefoglalja a global_graph-ot, inicializálja az AsynchronousNoC-ot a megadott grid dimenziókkal, és beállítja a belső processzorokat és vezérlőket. Szintén kiváltja a noc.initializeCores() és a noc.buildRoutingTable() hívásokat a mesh hálózat előkészítéséhez.
- deinit(): Kaszkádolt takarítást hajt végre. Meghívja a deinit()-et a noc, isomorphism_processor, edge_weighting és global_graph objektumokon, biztosítva az üzenetek, routing táblák és gráfstruktúrák számára lefoglalt összes memória felszabadítását.

 Core Orchestration Pipeline

A gráffeldolgozás elsődleges belépési pontja a processGraph(). Ez a metódus egy szekvenciális folyamatot hangszerel, amely egy hardveres végrehajtási ciklust utánoz.

 Publikus metódusok

 Gráf elosztás és szinkronizáció
- distributeGraph(): Particionálja a global_graph-ot kisebb local_graph szegmensekre, és hozzárendeli őket a noc-on belüli ProcessingCore példányokhoz.
- synchronizeGraphs(): Az elosztás inverze. Végigiterál az összes aktív core-on, visszamergelve a local_graph frissítéseiket a global_graph-ba. Ez biztosítja, hogy a párhuzamosan kiszámított eredmények konszolidálódjanak.

 Párhuzamos feldolgozás
- processIsomorphismParallel(): Végigiterál a NoC összes core-ján. Minden core esetében ellenőrzi a sparse_activation.shouldActivateCore()-t. Ha aktív, az isomorphism_processor-t használja az izomorf részgráfok megtalálására az adott core local_graph-jában.
- updateEdgeWeightsParallel(): Párhuzamosítja az él-súly számításokat. Alkalmazza az edge_weighting.updateWeight() logikát minden élre minden core lokális gráfjában, feltéve, hogy a core nincs power-gated állapotban, vagy nem hagyta ki a sparse activation.

 Kommunikáció és energiagazdálkodás
- propagateWeightsAsync(): Elindítja a súlyok propagálását a hálózaton keresztül. weight_update típusú NoCMessage objektumokat generál, és a noc.sendMessage()-et használja az elosztásukhoz. Ezután meghívja a noc.routeMessages()-et, hogy szimulálja az adatok tényleges mozgását a mesh-en keresztül.
- managePower(): Meghívja a power_gating.managePowerBudget() metódust, amely elemzi az összes core kihasználtságát, és a power_budget alapján eldönti, hogy melyeket kapuzza (állítsa le) vagy kapcsolja vissza.

 Statisztikák és monitorozás

A getStatistics() metódus aggregálja a teljesítménymetrikákat az összes alrendszerből egy RGPUStatistics struct-ba.

A visszaadott főbb metrikák a következők:
- Execution Cycles: Az összes core-on összegzett teljes cycles_active.
- Sparsity Ratio: A sparse_activation.computeSparsityRatio() segítségével számítva.
- Power Utilization: A current_power és a power_budget aránya.

---

 ProcessingCore és CoreState

A ProcessingCore a számítás alapvető egysége az r_gpu architektúrán belül. Minden core egy csempét (tile) képvisel egy 2D mesh Network-on-Chip (NoC) hálózatban, amely képes független gráffeldolgozásra, lokális memóriakezelésre és aszinkron kommunikációra. Egy core viselkedését és energiaprofilját a CoreState szabályozza.

 A ProcessingCore Struct

A ProcessingCore struct egységbe foglalja az állapotot, a lokális gráfadatokat és a kommunikációs puffereket a NoC grid egyetlen csomópontja számára.

Core identitás és grid koordináták Minden core-t egy egyedi core_id és a mesh-en belüli térbeli (x, y) koordinátái azonosítanak. Ezek a koordináták elengedhetetlenek a NoC által a csempék közötti üzenetkézbesítéshez használt XY routing algoritmushoz.

 Lokális gráf tulajdonjogi modell
A core-ok a globális gráf egy részét kezelik, amelyet local_graph-ként ismerünk. A tulajdonjogi modell explicit:
- local_graph_owned: Egy logikai flag, amely jelzi, hogy a core felelős-e a gráf memóriájának felszabadításáért.
- setLocalGraph: Lehetővé teszi egy meglévő gráf csatolását a core-hoz, a tulajdonjog átvételének lehetőségével.
- createLocalGraph: Lefoglal egy új SelfSimilarRelationalGraph-ot a core lokális allokátorának használatával, és a tulajdonjogot true-ra állítja.

 Kommunikáció és üzenetküldés
Minden core fenntart egy message_queue-t a NoCMessage objektumok számára.
- enqueueMessage: Hozzáad egy kapott üzenetet a lokális sorhoz.
- processMessages: Törli a sort, szimulálva a bejövő adatok feldolgozását. A jelenlegi implementációban ez a metódus visszaadja a feldolgozott üzenetek számát, és felszabadítja a hozzájuk tartozó memóriát.

 Metrikák és teljesítménykövetés
A core-ok nyomon követik a saját telemetriájukat az energiagazdálkodás és a kihasználtság-elemzés támogatása érdekében:
- energy_consumed: Egy kumulatív f64, amely a csempe által felhasznált teljes energiát képviseli.
- cycles_active / cycles_idle: A kihasználtság kiszámításához használt számlálók.
- getUtilization / getWorkload: Visszaadja az aktív ciklusok és az összes ciklus arányát.

 CoreState Enumeráció

A CoreState enum definiálja egy processing core működési módjait. Ez az állapot határozza meg, hogyan kezeli a core-t a PowerGatingController és a SparseActivationManager.

| Állapot | Leírás |
| --- | --- |
| idle | A core be van kapcsolva, de jelenleg nincsenek hozzárendelt feladatai. |
| processing | A core aktívan hajt végre gráfalgoritmusokat (izomorfizmus, súlyozás). |
| communicating | A core NoC üzenetek továbbításában vagy szinkronizációban vesz részt. |
| power_gated | A core logikailag le van állítva az energiatakarékosság érdekében; nem tud feldolgozni vagy kommunikálni. |

 Életciklus és grid menedzsment

A core-okat az AsynchronousNoC példányosítja és kezeli az **RGPU** inicializálása során.

Grid elhelyezés és szomszédság A core-ok egy 2D mesh-ben vannak elrendezve. Az initializeCores során a NoC megállapítja a kardinális szomszédokat (Fel, Le, Balra, Jobbra) minden core számára.

 Főbb metódusok referenciája

 Inicializálás és memória
- init(allocator, core_id, x, y): Beállítja a core-t egy üres szomszédlistával és üzenetsorral. A kezdeti állapotot .idle-re állítja.
- deinit(): Kitakarítja a szomszédokat, törli az üzenetsort (felszabadítva a payloadokat), és megsemmisíti a local_graph-ot, ha a local_graph_owned értéke true.
- clone(allocator): Létrehozza a core metaadatainak és szomszédainak mély másolatát, bár nem klónozza a gráfadatokat vagy az üzenetsor tartalmát.

 Adatáramlás
- addNeighbor(neighbor_id): Hozzáad egy core ID-t a belső neighbors listához.
- enqueueMessage(message): Elhelyez egy NoCMessage-et a core lokális pufferében.
- processMessages(): Végigiterál a message_queue-n, meghívva a deinit()-et minden üzeneten a payload felszabadításához.

---

 Gráf adatmodell

Az r_gpu rendszer egy specializált gráf adatmodellt használ, amelyet relációs feldolgozásra és elosztott végrehajtásra terveztek. Az alapvető adatstruktúrák az nsir_core.zig-ből vannak importálva, és komplex kapcsolatok reprezentálására vannak optimalizálva magas dimenziójú attribútumokkal (Qubitek) és változó minőségekkel.

 Alapvető adatentitások

A gráf négy elsődleges típusra épül: Node, Edge, EdgeQuality és Qubit. Ezek entitások lehetővé teszik a rendszer számára, hogy ne csak a konnektivitást, hanem a kapcsolatok szemantikai természetét és erősségét is reprezentálja.

| Típus | Definíció | Szerep |
| --- | --- | --- |
| Node | nsir_core.Node | Egy csúcsot képvisel a gráfban egyedi ID-vel és Qubit attribútumok halmazával. |
| Edge | nsir_core.Edge | Egy irányított kapcsolatot képvisel két node között, amely tartalmaz egy súlyt és egy EdgeQuality-t. |
| EdgeQuality | nsir_core.EdgeQuality | Egy enum vagy struct, amely definiálja a kapcsolat *típusát* vagy *természetét* (pl. temporális, térbeli). |
| Qubit | nsir_core.Qubit | Az adat alapvető egysége egy node-on belül, amely kvantum-ihletésű vagy magas dimenziójú állapotot képvisel. |

 SelfSimilarRelationalGraph

A SelfSimilarRelationalGraph a gráfadatok elsődleges tárolója. Kezeli a node-ok és edge-ek életciklusát és tárolását nagy teljesítményű hash map-ek használatával.

 Tárolási implementáció
A node-ok és edge-ek AutoHashMap struktúrákban vannak tárolva, hogy biztosítsák az O(1) keresési teljesítményt az intenzív gráfbejárások, például az izomorfizmus-detektálás vagy a súlypropagálás során.
- Nodes: Egy map-ben tárolva, ahol a kulcs a NodeID.
- Edges: Egy EdgeKey használatával tárolva, amely tipikusan a forrás és a cél ID-ket kombinálja. Az EdgeKeyContext egyedi hashelést biztosít ezekhez a kulcsokhoz.

Lokális vs. Globális gráfok A rendszer két gráf-tulajdonjogi hatókört különböztet meg: ## Globális gráf: A RelationalGraphProcessingUnit által tárolt teljes relációs adatkészlet. ## Lokális gráf: A gráf egy részhalmaza, amely egy adott ProcessingCore-hoz van rendelve. A core-ok vagy *birtokolhatják* a lokális gráfjukat (felelősek a felszabadításért), vagy hivatkozást tarthatnak egy megosztott szegmensre.

 Gráf particionálás és elosztás

A distributeGraph() folyamat felelős a global_graph particionálásáért és a fragmensek hozzárendeléséért a ProcessingCore gridhez.

 Particionálási mechanizmus
Az elosztás során az **RGPU** végigiterál az AsynchronousNoC elérhető core-jain, és feltölti a local_graph mezőiket. Ez a következőkön keresztül valósul meg:
- createLocalGraph(): Lefoglal egy új SelfSimilarRelationalGraph-ot egy core számára.
- setLocalGraph(): Manuálisan hozzárendel egy meglévő gráf mutatót egy core-hoz, megadva, hogy a core átveszi-e a tulajdonjogot.

Adatáramlás: Elosztástól a szinkronizációig A gráfadatok a particionálás, a párhuzamos feldolgozás és a végső visszamergelés életciklusán mennek keresztül.

 Szinkronizáció és konzisztencia

Mivel minden ProcessingCore függetlenül operál a saját local_graph-ján, a rendszernek rendszeresen egyeztetnie kell a változásokat (például a frissített él-súlyokat) a globális állapottal.
- Üzenet alapú szinkronizáció: A core-ok MessageType.graph_sync vagy MessageType.data_transfer címkével ellátott NoCMessage-eket használnak a lokális változások kommunikálására.
- Súlyfrissítések: A DynamicEdgeWeighting alrendszer lokálisan számítja ki az új súlyokat az updateWeight() használatával, amelyeket aztán propagálnak vagy szinkronizálnak a NoC-on keresztül.
- Deduplikáció: A synchronizeGraphs() fázis során az **RGPU** összefésüli az összes local_graph példány hash map-jeit, feloldva a konfliktusokat és frissítve a global_graph struktúrát.

---

 Aszinkron Network-on-Chip (NoC)

Az Aszinkron Network-on-Chip (NoC) az r_gpu architektúra kommunikációs gerince. Egy skálázható, csomagkapcsolt hálózatot biztosít, amely lehetővé teszi a ProcessingCore egységek számára a gráfadatok, szinkronizációs jelek és teljesítményvezérlő parancsok cseréjét globális szinkron órajel nélkül.

A NoC a core-ok 2D mesh hálózatát kezeli, megbirkózva az útvonalkeresés, az üzenetpriorizálás és a kézbesítési metrikák bonyolultságával.

 Mesh topológia és inicializálás

A NoC egy 2D mesh-ként van megszervezve, amelyet a grid_width és grid_height definiál. Az initializeCores() fázis során a rendszer példányosítja a ProcessingCore objektumokat, és létrehozza a kardinális szomszédsági kapcsolatokat (Fel, Le, Balra, Jobbra).

Az alacsony késleltetésű kommunikáció biztosítása érdekében a NoC előre kiszámítja az útvonalakat a core-ok minden lehetséges párja között egy statikus routing tábla használatával. Ez a tábla egy AutoHashMap-ben van tárolva egy RouteKey használatával, hogy lehetővé tegye az O(1) keresést az üzenetküldés során.

 XY Routing és üzenetkézbesítés

A NoC egy determinisztikus XY Routing algoritmust alkalmaz a computeXYRoute()-on keresztül. Az üzenetek először az X-tengelyen haladnak, hogy elérjék a cél oszlopát, majd az Y-tengelyen haladnak, hogy elérjék a cél sorát. Ez a megközelítés megakadályozza a deadlockokat a mesh topológiában.

Az üzeneteket a NoCMessage struct kezeli, és MessageType szerint vannak kategorizálva. A kézbesítést egy PriorityQueue kezeli az AsynchronousNoC-on belül, biztosítva, hogy a kritikus jelek (mint a power_control) a standard adatátvitelek előtt kerüljenek feldolgozásra.

| Üzenettípus | Prioritás (Tipikus) | Cél |
| --- | --- | --- |
| power_control | Magas | Core-ok kapuzása/visszakapcsolása |
| weight_update | Közepes | Megerősítéses tanulás visszacsatolása |
| graph_sync | Közepes-Magas | Lokális gráfadatok szinkronizálása a globálisba |
| data_transfer | Alacsony | Általános tömeges adatmozgatás a core-ok között |

 Kommunikációs folyamat

Egy üzenet életciklusa egy forrás core-tól egy cél core-ig a NoC routing logikáján keresztül: ## A forrás core meghívja a sendMessage()-et. ## A NoC kikeresi az útvonalat a routing táblából, és hozzáadja az üzenetet a prioritási sorhoz. ## A routeMessages() ciklus során a NoC kiveszi a legmagasabb prioritású üzenetet, növeli a total_hops számlálót, és beleteszi a cél core üzenetsorába (enqueueMessage). ## A cél core feldolgozza az üzenetet a processMessages() segítségével.

---

 AsynchronousNoC: Mesh topológia és inicializálás

Az AsynchronousNoC (Network-on-Chip) az **RGPU** kommunikációs gerinceként szolgál. A ProcessingCore egységek halmazát egy 2D mesh topológiába szervezi, lehetővé téve az aszinkron üzenetküldést és a koordinált gráffeldolgozást. Ez az oldal részletezi a mesh felépítését, a kardinális szomszédok kijelölését és a routing útvonalak előkiszámítását a hatékony core-ok közötti kommunikáció érdekében.

 Mesh felépítése és Core inicializálás

A NoC egy specifikus grid_width és grid_height értékkel van inicializálva, amely meghatározza a core-ok teljes számát (W x H). Az initializeCores() függvény kezeli a ProcessingCore struct-ok példányosítását és elhelyezésüket a logikai gridben.

- Core azonosítás: Minden core kap egy egyedi core_id-t a sorfolytonos pozíciója alapján: ID = y  width + x.
- Geometriai leképezés: Minden core tárolja a saját (x, y) koordinátáit, amelyek kritikusak az üzenetkézbesítés során használt XY routing algoritmushoz.
- Szomszédok kijelölése: A példányosítás után a NoC végigiterál a griden, hogy létrehozza a kardinális szomszédokat (Fel, Le, Balra, Jobbra). Egy (x, y) koordinátájú core a (x ± 1, y) és (x, y ± 1) szomszédokhoz van kapcsolva, feltéve, hogy ezek a koordináták a grid határain belül esnek.

 Core inicializálási logika
## AsynchronousNoC.init: Lefoglalja a NoC struktúrát és meghívja a core inicializálást.
2. initializeCores: Végigfut a grid_height és grid_width értékeken a ProcessingCore példányok létrehozásához.
3. addNeighbor: Feltölti a neighbors ArrayList-et minden core-on belül.

 Routing tábla előkiszámítása

A futásidejű O(1) útvonalkeresés elérése érdekében az AsynchronousNoC előre kiszámítja az összes lehetséges pont-pont útvonalat a mesh-en belül a buildRoutingTable() használatával.

 RouteKey és Hash Map
A rendszer egy specializált RouteKey-t használ a forrás és a cél core közötti útvonalak azonosítására.
- RouteKey: Egy struct, amely tartalmazza a source_id-t és a target_id-t.
- RouteKeyContext: Biztosítja a hashelési és egyenlőségi logikát, amely szükséges ahhoz, hogy az std.ArrayHashMap a RouteKey-t kulcsként használja.
- routing_table: Egy map, amely egy RouteKey-t társít egy ArrayList(usize)-hoz, amely a core ID-k sorrendjét képviseli az útvonalon.

Útvonal generálása A buildRoutingTable() függvény végigiterál a NoC-ban lévő core-ok minden lehetséges párján. Minden pár esetében meghívja a computeXYRoute()-ot a hop-szekvencia generálásához, és az eredményt a routing_table-ben tárolja.

 Implementációs részletek

 Szomszédok számítása
A kardinális szomszédok kijelölésének logikája biztosítja, hogy a szélső core-ok ne próbáljanak a mesh-en kívüli koordinátákhoz kapcsolódni:
- Balra: x > 0 -> (x - 1, y)
- Jobbra: x < width - 1 -> (x + 1, y)
- Fel: y > 0 -> (x, y - 1)
- Le: y < height - 1 -> (x, y + 1)

 Memóriakezelés
- Ownership: Az AsynchronousNoC birtokolja a core-ok és a routing tábla létrehozásához használt Allocator-t.
- Cleanup: Az AsynchronousNoC deinit() metódusa felelős azért, hogy végigiteráljon az összes ProcessingCore példányon, meghívja a megfelelő deinit() metódusaikat, törölje a routing_table-t, és felszabadítsa a core listát.

---

 XY Routing és üzenetkézbesítés

Ez az oldal az AsynchronousNoC kommunikációs rétegét részletezi, fókuszálva arra, hogyan történik az üzenetek útválasztása a 2D mesh topológián keresztül, a különböző forgalomtípusok priorizálására, és a ProcessingCore példányok közötti üzenetkézbesítés mechanikájára.

 XY Routing Algoritmus

Az AsynchronousNoC egy determinisztikus XY Routing algoritmust használ, amely a computeXYRoute()-ban van implementálva. Ez az algoritmus minimalizálja a logikai komplexitást a hálózaton belül azáltal, hogy először az X-tengelyen (vízszintesen) halad, hogy egyezzen a cél oszlopával, majd az Y-tengelyen (függőlegesen) halad, hogy elérje a cél sorát.

 Implementációs részletek
A routing útvonal előre ki van számítva és a routing_table-ben van tárolva az inicializálási fázis során, hogy biztosítsa az O(1) keresést az aktív szimulációs ciklusok alatt.
- X-Traversal: Az algoritmus összehasonlítja az aktuális X-koordinátát a cél X-koordinátájával. Ha eltérnek, egy lépést tesz a cél X felé.
- Y-Traversal: Amint az X-koordináták megegyeznek, az algoritmus összehasonlítja az aktuális Y-koordinátát a cél Y-koordinátájával, és egy lépést tesz a cél Y felé.
- Path Storage: Az eredményül kapott core_id értékek sorozata egy ArrayList(usize)-ban van tárolva a routing_table hash map-en belül.

 Üzenet priorizálás

A NoC egy prioritás-alapú kézbesítési rendszert használ. Az üzenetek nem tisztán **FIFO** sorrendben vannak kezelve; ehelyett a MessagePriorityEntry struct-on keresztül vannak menedzselve, amelyet egy PriorityQueue használ a kézbesítési sorrend meghatározására.

 MessageType és prioritás szemantika
A MessageType enum öt különböző forgalmi kategóriát definiál. A NoCMessage.priority magasabb numerikus prioritási értékei korábbi kézbesítést eredményeznek.
- power_control (Magas): Jelek a core-ok kapuzására/visszakapcsolására; kritikus az energiagazdálkodáshoz.
- graph_sync (Közepes-Magas): A lokális gráfadatok szinkronizálása a globális állapotba.
- weight_update (Közepes): Megerősítéses tanulás visszacsatolása az él-súlyokhoz.
- isomorphism_result (Közepes): Eredmények a részgráf-illesztési feladatokból.
- data_transfer (Alacsony): Általános tömeges adatmozgatás a core-ok között.

 Priority Queue mechanika
A MessagePriorityEntry struct becsomagol egy NoCMessage-et, és biztosítja az std.PriorityQueue által megkövetelt compare függvényt.
- Összehasonlítási logika: A sor egy max-heap a priority mező alapján. Ha két üzenetnek azonos a prioritása, a korábbi timestamp-pel rendelkező kap prioritást (**FIFO** fallback).

 Üzenetkézbesítési mechanika

Az üzenetkézbesítés két elsődleges fázisból áll: pufferelés a NoC belső sorában, és a végső kézbesítés a cél core lokális message_queue-jába.

sendMessage() Amikor egy komponens meghívja a sendMessage()-et, a NoC nem kézbesíti azonnal az üzenetet. Ehelyett: ## Kiszámítja az útvonal hosszát (hops) a routing_table használatával. ## Növeli a total_hops számlálót a statisztikai nyomon követéshez. ## Becsomagolja a NoCMessage-et egy MessagePriorityEntry-be, és hozzáadja a NoC priority_queue-jához.

routeMessages() A routeMessages() függvény hajtja végre a tényleges kézbesítést. Kiüríti a NoC priority_queue-ját, és az üzeneteket a cél ProcessingCore-hoz mozgatja. ## Extraction: Az üzenetek prioritási sorrendben kerülnek ki a priority_queue-ból. ## Cloning: A memóriabiztonság biztosítása érdekében az aszinkron határon keresztül az üzenet klónozásra kerül a NoCMessage.clone() használatával. ## Core Ingress: A klónozott üzenet hozzáadódik a target_core.message_queue-hoz. ## State Update: A cél core állapota communicating-re frissülhet ezen folyamat során.

 Statisztikák és nyomon követés

A NoC nyomon követ több, az üzenetkézbesítéssel kapcsolatos metrikát, amelyek az RGPUStatistics-on keresztül érhetők el:
- total_messages: Minden alkalommal növekszik, amikor a sendMessage() meghívásra kerül.
- total_hops: Az összes üzenet által megtett grid lépések kumulatív száma, az average_message_hops kiszámításához használatos.
- Message Latency: Bár nincs explicit módon időtartamként tárolva, a NoCMessage-ben lévő timestamp mező lehetővé teszi a késleltetés elemzését a core-oldali feldolgozás során.

---

 Gráffeldolgozó alrendszerek

A Relational Graph Processing Unit (**RGPU**) a komplex gráfelemzést három specializált alrendszerre delegálja. Ezek az alrendszerek kezelik a strukturális elemzést, a kapcsolati erősségek adaptív tanulását és a befolyás propagálását a gráf topológiáján keresztül. Ezen feladatok tehermentesítésével a fő RelationalGraphProcessingUnit koordinátorról a rendszer egy moduláris architektúrát ér el, ahol az analitikai logika el van választva a hardverszintű szempontoktól, mint a power gating és az üzenet routing.

 Az alrendszerek áttekintése

Az analitikai motor három elsődleges funkcionális területre van osztva: ## Isomorphism Detection (Izomorfizmus detektálás): Strukturális hasonlóságokat azonosít a gráfszegmensek között a minták vagy redundáns információk detektálására. ## Dynamic Edge Weighting (Dinamikus él-súlyozás): Egy megerősítéses tanulás által inspirált mechanizmust implementál a kapcsolatok *erősségének* visszacsatolás alapján történő beállítására. ## Weight Propagation (Súly propagálás): Elosztja a befolyást a gráf mesh-en keresztül, lehetővé téve, hogy a lokális változások hassanak a tágabb szemantikai kontextusra.

 Graph Isomorphism Processor

A GraphIsomorphismProcessor felelős annak meghatározásáért, hogy két gráfstruktúra topológiailag azonos-e. Egy Canonical Form (Kanonikus Forma) algoritmust használ a gráf-összehasonlítás komplexitásának csökkentésére. Ahelyett, hogy drága visszalépéses (backtracking) kereséseket hajtana végre minden összehasonlításhoz, egy egyedi string aláírást generál egy gráfhoz.
- Canonical Form: Egy string reprezentáció, amelynek formátuma: {node_count}_[sorted_degree_pairs]_[sorted_edge_qualities].
- Memoization: A rendszer a cacheCanonicalForm()-ot használja a kiszámított aláírások tárolására egy canonical_cache-ben (StringHashMap), jelentősen felgyorsítva az ismétlődő kereséseket a findIsomorphicSubgraphs() során.
- Search: A findIsomorphicSubgraphs() metódus egy csúszóablakos (sliding-window) stílusú keresést implementál a globális gráfon keresztül, hogy egyezéseket találjon egy célmintára.

 Dynamic Edge Weighting and Propagation

A DynamicEdgeWeighting alrendszer biztosítja az **RGPU** *tanulási* képességét. Az éleket nem statikus kapcsolatokként kezeli, hanem dinamikus relációkként, amelyek a rendszer visszacsatolása és a környezeti tényezők alapján fejlődnek.

Súlyozási logika Az alrendszer az updateWeight() függvényt használja egy megerősítéses tanulási képlet alkalmazására: new_weight = current_weight + (learning_rate  feedback) Az eredményül kapott érték a 0.0 és 1.0 közötti tartományba van szorítva (clamped).

 Adaptív és temporális tényezők
Az egyszerű visszacsatoláson túl a computeAdaptiveWeight() a súlyokat a következők alapján számítja ki:
- Temporális tényezők: Milyen régen fértek hozzá az élhez.
- Térbeli tényezők: A távolság vagy *hop count* a NoC-ban.
- Szemantikus tényezők: Az él nsir_core.zig-ben definiált EdgeQuality attribútumai.

Propagálás A propagateWeights() metódus egy Breadth-First Search (**BFS**) bejárást használ. Ahogy a súlyok távolodnak a forrás node-tól, egy bomlási tényezőnek (decay factor, alapértelmezés szerint 0.9^depth) vannak kitéve, biztosítva, hogy a lokális frissítések ne okozzanak végtelen oszcillációkat a globális gráfban.

---

 Graph Isomorphism Processor

A GraphIsomorphismProcessor egy specializált analitikai alrendszer az **RGPU**-n belül, amely a relációs gráfok közötti strukturális ekvivalencia detektálásáért felelős. Egy kanonikus címkézési megközelítést alkalmaz a komplex gráfstruktúrák determinisztikus string reprezentációkká történő átalakítására, lehetővé téve a hatékony O(1) összehasonlítást a kezdeti számítás után. Ez a komponens kritikus fontosságú az ismétlődő minták azonosításához a globális gráfon és az egyes ProcessingCore egységek által feldolgozott lokális részgráfokon belül.

 Alaplogika és adatáramlás

A processzor úgy működik, hogy egy SelfSimilarRelationalGraph-ot egy *Kanonikus Formára* redukál. Ez a forma egy egyedi string aláírás, amely rögzíti a gráf alapvető topológiáját és metaadatait, biztosítva, hogy két gráf akkor és csak akkor izomorf, ha a kanonikus stringjeik azonosak.

Kanonikus Forma Algoritmus Az algoritmus egy aláírást generál a következő formátumban: {node_count}_[(out_degree,in_degree),...]_[edge_quality,...]. ## Node Count: A gráfban lévő node-ok teljes száma. ## Degree Sequence: A processzor minden node-ra kiszámítja a be-fokot (in-degree) és a ki-fokot (out-degree). Ezek a párok tárolásra kerülnek, majd lexikografikusan rendezve lesznek, hogy a sorrend független legyen a node-ok beszúrási sorrendjétől. ## Edge Quality Sequence: Minden él EdgeQuality-je (amely az nsir_core-ból származik) összegyűjtésre és rendezésre kerül. Ez biztosítja, hogy még ha a topológiák meg is egyeznek, a különböző relációs minőségek különböző aláírásokat eredményezzenek. ## Serialization: Ezek a komponensek egyetlen stringgé vannak összefűzve, amelyet hashelésre és összehasonlításra használnak.

 Főbb függvények és implementáció

 computeCanonicalForm
Ez az elsődleges transzformációs függvény. Végigiterál egy SelfSimilarRelationalGraph nodes és edges HashMap-jein a strukturális invariánsok kinyeréséhez.
- Komplexitás: O(V log V + E log E) a fokszám-szekvenciák és az él-minőségek rendezése miatt.
- Memória: Egy dinamikus string puffert foglal le az aláírás felépítéséhez.

 areIsomorphic
Két gráfot hasonlít össze a kanonikus formáik generálásával és összehasonlításával.
- Implementáció: Meghívja a computeCanonicalForm-ot mindkét bemeneti gráfon, és egy string összehasonlítást hajt végre.

 findIsomorphicSubgraphs
Egy csúszóablakos keresési implementáció, amely megpróbálja megtalálni egy cél részgráf példányait egy nagyobb gráfon belül.
- Logika: Végigiterál a nagy gráf node-jain, mindegyiket egy N méretű részgráf potenciális gyökereként kezelve (ahol N a cél mérete). Ezután kinyeri ezeket az alstruktúrákat, és összehasonlítja őket az areIsomorphic használatával.

cacheCanonicalForm Az ismétlődő összehasonlítások optimalizálása érdekében a processzor fenntart egy canonical_cache-t (egy StringHashMap-et). Ez lehetővé teszi a rendszer számára, hogy a computeCanonicalForm eredményeit egy egyedi gráf azonosítóval indexelve tárolja, a későbbi ellenőrzéseket O(1) keresésekre redukálva.

 Korlátok és komplexitás

Bár a kanonikus formájú megközelítés rendkívül hatékony az **RGPU**-ban használt relációs struktúrákhoz, specifikus korlátai vannak:
- Számítási korlát: Az O(V log V + E log E) komplexitás alkalmatlanná teszi rendkívül sűrű gráfokhoz, amelyek core-onként több millió élt tartalmaznak.
- Precízió: Az aláírás az EdgeQuality-re és a fokszámokra támaszkodik. Ha két különböző topológia ugyanazt a fokszám-szekvenciát és minőségeket hozza létre, ütközés lép fel (bár ez ritka a relációs kontextusokban).
- Részgráf keresés: A findIsomorphicSubgraphs egy naiv csúszóablakot használ, amely számításigényes nagy célminták esetén.

Integráció az **RGPU**-val A RelationalGraphProcessingUnit ezt a processzort a processIsomorphismParallel() fázis során hívja meg. Minden ProcessingCore a processzor lokális példányát használja a local_graph partíciójának elemzésére, majd az eredményeket az AsynchronousNoC-on keresztül sugározza a MessageType.isomorphism_result használatával.

---

 Dinamikus él-súlyozás és propagálás

A Dinamikus él-súlyozás és propagálás alrendszer biztosítja az analitikai mechanizmusokat a kapcsolati erősségek számszerűsítésére és elosztására a gráfon belül. Egy megerősítéses tanuláson alapuló súlyozási képletet, adaptív tényezőszámítást és egy csillapított propagálási algoritmust implementál a core griden keresztül.

 A DynamicEdgeWeighting áttekintése

A DynamicEdgeWeighting struct felelős az él-súlyok életciklusának kezeléséért, beleértve a kezdeti számításukat, a visszacsatolás általi megerősítést és a térbeli propagálást. Fenntart egy weight_history-t a temporális elemzéshez, és egy konfigurálható learning_rate-et használ a súlyfrissítések volatilitásának szabályozására.

 Főbb adatstruktúrák
- learning_rate: f64 - Skálázási tényező a visszacsatolás-vezérelt frissítésekhez.
- weight_history: AutoHashMap(EdgeKey, ArrayList(f64)) - Tárolja a történelmi súlyértékeket a temporális elemzéshez.
- allocator: Allocator - Memóriaallokátor a történet tárolásához.

 Alapvető implementáció és logika

Megerősítéses tanulási képlet Az updateWeight metódus egy standard megerősítéses tanulási frissítési szabályt implementál. Az új súly az aktuális súly módosításával kerül kiszámításra a learning_rate és a kapott feedback szorzata alapján. A gráf stabilitásának fenntartása érdekében az eredményül kapott érték a [0.0, 1.0] tartományba van szorítva.

Adaptív súlyszámítás A computeAdaptiveWeight függvény egy összetett súlyt származtat három különböző tényező szorzásával: ## Temporális: A weight_history-ban tárolt történelmi trendekből származtatva. ## Térbeli: A lokális gráf topológiája vagy a core koordinátái alapján. ## Szemantikus: Az él EdgeQuality vagy Qubit tulajdonságai alapján.

Csillapított súlypropagálás A propagateWeights metódus egy Breadth-First Search (**BFS**) bejárást implementál egy súlyfrissítés elosztására egy forrás node-tól a lokális gráfon keresztül. A lokalizáció biztosítása és a végtelen visszacsatolási hurkok megakadályozása érdekében a bejárás minden lépésénél egy 0.9^depth bomlási tényező (decay factor) kerül alkalmazásra.

 Főbb metódusok és paraméterek

updateEdgeWeightsParallel() Ez a metódus végigiterál az AsynchronousNoC grid összes ProcessingCore példányán. Ha egy core aktív (nem power-gated vagy nem hagyta ki a SparseActivationManager), alkalmazza a DynamicEdgeWeighting logikát a core local_graph-jának minden élére.

propagateWeightsAsync() Elindítja a súlypropagálást a griden keresztül. A NoCMessage rendszert használja weight_update üzenetek küldésére a core-ok között, amikor a propagálás átlépi a partícióhatárokat.

setLearningRate(rate: f64) Lehetővé teszi az η paraméter dinamikus beállítását. A magasabb értékek érzékenyebbé teszik a rendszert a legutóbbi visszacsatolásokra, míg az alacsonyabb értékek a történelmi stabilitást helyezik előtérbe.

 Műszaki specifikációk
- Decay Factor: Konstans 0.9 hop-onként.
- Clamping: Szigorú korlátok[0.0, 1.0].
- History Type: f64 tömb EdgeKey-enként.
- Message Type: MessageType.weight_update (Enum 0).

---

 Energiagazdálkodás

Az r_gpu rendszer egy többrétegű energiagazdálkodási stratégiát implementál, amelyet a gráffeldolgozó grid energiafogyasztásának minimalizálására terveztek. Az energiahatékonyság két elsődleges mechanizmuson keresztül valósul meg: Sparse Activation, amely kihagyja a számítást az alacsony terhelésű core-oknál, és Power Gating, amely fizikailag megszakítja az üresjárati core-ok áramellátását a szivárgás csökkentése érdekében.

Ezeket a mechanizmusokat a RelationalGraphProcessingUnit hangszereli a processGraph() végrehajtási folyamat során.

 Energiagazdálkodás áttekintése

 Sparse Activation Manager
A SparseActivationManager egy szoftverszintű kapuzási mechanizmust biztosít. Kiértékeli minden ProcessingCore terhelését egy sparsity_threshold-dal szemben. Ha egy core terhelése (amelyet a getWorkload() számít ki) ezen küszöb alá esik, a menedzser javasolja a core aktiválásának kihagyását az aktuális ciklusra.
- Fő metrika: sparsity_ratio, amely az alacsony terhelés miatt jelenleg inaktív core-ok arányát képviseli.
- Energiahatás: Minden kihagyott aktiválás növeli az energy_saved számlálót.
- Integráció: A processIsomorphismParallel() és az updateEdgeWeightsParallel() függvényekben használatos annak meghatározására, hogy egy core-nak végre kell-e hajtania a lokális gráf logikáját.

 Power Gating Controller
A PowerGatingController hardverszintű energiagazdálkodást implementál. A sparse activation-nel ellentétben, amely csupán kihagyja a feladatokat, a power gating egy core-t a CoreState.power_gated állapotba léptet át, szimulálva az áramellátás lekapcsolását a statikus áramszivárgás kiküszöbölése érdekében.
- Budget Management: Egy power_budget-en belül működik. Egy zárt hurkú algoritmust használ a managePowerBudget()-ben a core-ok kapuzására, amikor az energiafogyasztás meghaladja a költségvetést, és visszakapcsolására, amikor a kihasználtság megnő.
- Állapotátmenet:
    - gateCore(): Az állapotot power_gated-re állítja, csökkenti a current_power-t 10.0 egységgel.
    - ungateCore(): Visszaállítja az állapotot idle-re, növeli a current_power-t 10.0 egységgel.

Koordinációs logika A RelationalGraphProcessingUnit koordinálja ezt a két rendszert annak biztosítására, hogy a grid teljesítőképes maradjon, miközben az energiakorlátokon belül marad. A managePower() metódus tipikusan a főbb feldolgozási szakaszok után kerül meghívásra a grid energiaállapotának újraértékelésére.

Vezérlő interakciók
- Sparse Activation Manager: Fő célja az alacsony hasznosságú számítások kihagyása. Mechanizmusa a shouldActivateCore() ellenőrzés. Érintett állapot: Ideiglenes végrehajtás kihagyása. Metrika: sparsity_ratio.
- Power Gating Controller: Fő célja a statikus áramszivárgás csökkentése. Mechanizmusa a gateCore() / ungateCore(). Érintett állapot: CoreState.power_gated. Metrika: power_utilization.

---

 Sparse Activation Manager

A Sparse Activation Manager egy energiahatékonysági alrendszer az **RGPU**-n belül, amelyet az energiafogyasztás csökkentésére terveztek azáltal, hogy kihagyja a végrehajtást az alacsony terhelésű processing core-okon. Egy kapuzási mechanizmust implementál, amely megakadályozza a core-ok aktiválását a párhuzamos gráfműveletek során, ha a kiszámított terhelésük egy konfigurálható ritkasági küszöb (sparsity threshold) alá esik.

 Cél és adatáramlás

A menedzser middleware rétegként működik a gráf-intenzív feladatok végrehajtása során. Minden ProcessingCore workload-jának monitorozásával fenntart egy activation_map-et, amely meghatározza, hogy egy core-nak részt kell-e vennie az aktuális feldolgozási ciklusban. Ez az optimalizálás kritikus a relációs gráffeldolgozásnál, ahol az adatsűrűség gyakran nem egyenletes a 2D mesh griden keresztül.

 Konfiguráció és állapot

A SparseActivationManager egy struct-ként van definiálva az r_gpu.zig-ben. Fenntartja a globális ritkasági konfigurációt, és nyomon követi a teljes core grid aktiválási állapotát.
- sparsity_threshold: f64 - A core aktiválásához szükséges minimális terhelési arány (0.0-tól 1.0-ig). Alapértelmezett értéke 0.1.
- activation_map: ArrayList(bool) - Egy core_id által indexelt logikai tömb, amely az aktuális aktiválási állapotot jelzi.
- energy_saved: f64 - A ritka core-ok kihagyásával megtakarított energiaegységek kumulatív számlálója.

 Implementációs részletek

 Core aktiválási logika
Az elsődleges döntéshozó függvény a shouldActivateCore(). Lekéri a core aktuális terhelését – amely az aktív ciklusok és az összes ciklus arányaként van definiálva –, és összehasonlítja a küszöbértékkel.
- Logika: Ha a core.getWorkload() kisebb, mint a sparsity_threshold, a core inaktívként lesz megjelölve.
- Energia elszámolás: Minden alkalommal, amikor egy core-t kihagynak, az energy_saved számláló 1.0 egységgel nő.
- Állapot perzisztencia: Az eredmény az activation_map-ben tárolódik telemetriai és szinkronizációs célokra.

Sparsity metrikák A rendszer biztosítja a computeSparsityRatio() függvényt az aktiválási kapuzás hatékonyságának mérésére. Ez az utolsó ciklusban deaktivált core-ok százalékaként van kiszámítva: Sparsity Ratio = (Inaktív Core-ok) / (Összes Core)

 Integráció a gráf alrendszerekben

A SparseActivationManager kapuőrként (gatekeeper) van használva a RelationalGraphProcessingUnit két fő párhuzamos feldolgozási metódusában.

 1. Graph Isomorphism Gating
A processIsomorphismParallel()-ben az **RGPU** végigiterál az összes core-on az izomorf részgráfok megtalálásához. Mielőtt meghívná a GraphIsomorphismProcessor-t, ellenőrzi a menedzsert:
- Hatás: Megakadályozza a drága kanonikus forma számításokat azokon a core-okon, amelyek történelmileg alulhasznosítottak voltak.

 2. Edge Weighting Gating
Az updateEdgeWeightsParallel()-ben a menedzser kapuzza a megerősítéses tanulási frissítéseket az élekre:
- Hatás: Kihagyja az updateWeight() hívásokat, energiát takarítva meg, amikor a lokális gráf aktivitása alacsony.

---

 Power Gating Controller

A PowerGatingController egy hardverszintű energiagazdálkodási alrendszer, amely felelős az egyes ProcessingCore egységek energiaállapotának dinamikus beállításáért. Egy zárt hurkú vezérlési algoritmust implementál, amely egyensúlyba hozza a számítási áteresztőképességet egy definiált power_budget-tel a core-ok idle és power_gated állapotok közötti átléptetésével.

 Komponens áttekintése

A vezérlő monitorozza a core grid current_power fogyasztását, és beavatkozik, amikor a fogyasztás meghaladja a költségvetést, vagy amikor a core-ok alacsony kihasználtságot mutatnak. Azon az elven működik, hogy egy power_gated core jelentősen kevesebb energiát fogyaszt (10.0 egységnyi csökkenésként szimulálva), de nem tud számítást vagy kommunikációt végezni, amíg vissza nem kapcsolják (ungated).

 Core adatstruktúrák
- power_budget: f64 - A core grid maximálisan megengedett energiafogyasztása.
- current_power: f64 - Az energiafogyasztás valós idejű összege az összes core-on.

 Energiaállapot-átmenetek

A vezérlő kezeli a ProcessingCore példányok CoreState-jét. Az átmeneteket két elsődleges metódus kezeli, amelyek frissítik mind a logikai állapotot, mind a globális energiametrikákat.

gateCore() Ez a metódus egy core letiltására van meghívva. A következő műveleteket hajtja végre: ## A core state-jét CoreState.power_gated-re állítja. ## Csökkenti a globális current_power-t 10.0-val.

ungateCore() Ez a metódus egy core feldolgozásra történő újraengedélyezésére van meghívva. A következő műveleteket hajtja végre: ## A core state-jét CoreState.idle-re állítja. ## Növeli a globális current_power-t 10.0-val.

 Zárt hurkú menedzsment algoritmus

A managePowerBudget() függvény implementálja az elsődleges vezérlési logikát. A core kihasználtsági metrikákat (amelyeket a getUtilization() biztosít) használja fel megalapozott döntések meghozatalára arról, hogy mely core-okat kapuzza vagy kapcsolja vissza.

 Algoritmus logika
## Rendezés: A vezérlő a terhelésük alapján értékeli a core-ok teljesítményét.
## Kapuzási kritériumok: Egy core kapuzásra kerül, ha:
    - A kihasználtsága (aktív ciklusok vs összes ciklus) kevesebb, mint 0.1 (10%).
    - A current_power meghaladja a power_budget 50%-át.
## Visszakapcsolási kritériumok: Egy core visszaáll idle állapotba, ha:
    - A kihasználtsága nagyobb, mint 0.8 (80%).
    - Van elegendő hely a power_budget-ben.

 Metrikák és megfigyelhetőség

A vezérlő metrikákat biztosít a RelationalGraphProcessingUnit számára a rendszerszintű statisztikákhoz.

getPowerUtilization() Ez a metrika kiszámítja a current_power és a power_budget arányát. Az RGPUStatistics riporter használja a power gating stratégia hatékonyságának monitorozására.

 Statisztikai integráció
Az RGPUStatistics következő mezőit közvetlenül befolyásolja a PowerGatingController:
- gated_cores: A jelenleg power_gated állapotban lévő core-ok száma.
- current_power: A vezérlő által nyomon követett érték.
- power_budget: A konfigurált korlát.

---

 Statisztikák és megfigyelhetőség

Az r_gpu rendszer átfogó megfigyelhetőséget biztosít a relációs gráffeldolgozó egység teljesítményébe, energiahatékonyságába és működési állapotába. Ezt elsősorban az RPGUMetrics (más néven RPGUStatistics) struktúra segíti elő, amely aggregálja az adatokat a mögöttes ProcessingCore entitások mesh-éből és a menedzsment alrendszerekből.

A rendszer három elsődleges tartományban követi nyomon a metrikákat: ## Számítási hatékonyság

: Aktív vs. üresjárati ciklusok és core kihasználtság. ## Hálózati teljesítmény: Üzenet áteresztőképesség és routing hatékonyság a NoC-on belül. ## Energia és teljesítmény: Teljes energiafogyasztás, power gating hatékonysága, és a sparse activation-ből származó megtakarítások.

 RPGUStatistics Struktúra

A RelationalGraphProcessingUnit struct getStatistics() metódusa feltölt egy RPGUStatistics objektumot az egyes core-ok és belső menedzserek lekérdezésével.

| Mező | Leírás | Forrás |
| --- | --- | --- |
| total_cores | A NoC gridben lévő core-ok teljes száma. | self.noc.cores.items.len |
| active_cores | A jelenleg .processing vagy .communicating állapotban lévő core-ok száma. | ProcessingCore.state |
| gated_cores | A jelenleg .power_gated állapotban lévő core-ok száma. | PowerGatingController |
| total_energy_consumed | Az összes core által felhasznált összesített energia (Joule). | ProcessingCore.energy_consumed |
| total_active_cycles | A nem üresjárati állapotban töltött összes ciklus összege. | ProcessingCore.cycles_active |
| total_idle_cycles | Az üresjárati állapotban töltött összes ciklus összege. | ProcessingCore.cycles_idle |
| execution_cycles | Az RGPU jelenlegi globális ciklusa. | self.execution_cycles |
| sparsity_ratio | Az alacsony terhelés miatt kihagyott gráfolvasások százaléka. | SparseActivationManager |
| energy_saved | A sparse activation révén megtakarított becsült energiaegységek. | SparseActivationManager |
| total_messages | A NoC által feldolgozott üzenetek teljes száma. | AsynchronousNoC.total_messages |
| average_message_hops | Az üzenetenkénti átlagos ugrások (hops) száma a mesh-en keresztül. | AsynchronousNoC.total_hops / total_messages |
| current_power | Valós idejű áramfelvétel (mW). | PowerGatingController.current_power |
| power_budget | Az egység számára engedélyezett maximális áramfelvétel. | PowerGatingController.power_budget |

 Megfigyelhetőségi adatáramlás

A nyers adatok a hardverszintű szimulációkból (Core-ok és NoC) aggregálódnak a rendszerszintű megfigyelhetőséghez használt magas szintű statisztikákba.

 Főbb megfigyelhetőségi koncepciók

Core kihasználtság és terhelés Minden ProcessingCore nyomon követi a saját teljesítményét a cycles_active és cycles_idle segítségével. Ezek az értékek a getWorkload() és getUtilization() kiszámítására szolgálnak, amelyek egy lebegőpontos értéket adnak vissza, ami az aktív idő és a teljes idő arányát képviseli. Ezek a metrikák kritikusak a PowerGatingController számára annak eldöntéséhez, hogy mely core-okat altassa el.

Hálózati megfigyelhetőség Az AsynchronousNoC nyomon követi a globális üzenetstatisztikákat. Minden alkalommal, amikor egy üzenet sikeresen továbbításra kerül, a total_hops számláló növekszik a megtett távolsággal. Ez lehetővé teszi a fejlesztők számára a computeXYRoute algoritmus hatékonyságának megfigyelését, valamint a potenciális torlódások vagy nem hatékony particionálás detektálását.

Gráf állapot szinkronizáció A megfigyelhetőség az adatállapotra is kiterjed. A synchronizeGraphs() metódus biztosítja, hogy a lokális core gráfokon történő elosztott feldolgozás tükröződjön a global_graph-ban. Ez a folyamat magában foglalja a node-ok és edge-ek összefésülését, miközben deduplikálja a bejegyzéseket a konzisztens globális nézet fenntartása érdekében.

---

 Teljesítménymetrikák referenciája

Ez az oldal technikai referenciát nyújt a Relational Graph Processing Unit (**RGPU**) által közzétett numerikus teljesítmény- és hatékonysági metrikákhoz. Ezek a metrikák a gráf particionálás hatékonyságának, az energiatakarékossági mechanizmusok (Sparse Activation és Power Gating) hatékonyságának, valamint a Network-on-Chip (NoC) kommunikációs hálózat teljesítményének értékelésére szolgálnak.

A metrikák elérésének elsődleges struktúrája az RGPUStatistics, amelyet a RelationalGraphProcessingUnit getStatistics() metódusa tölt fel.

 Metrikák áttekintő táblázata

| Metrika | Kód szimbólum | Egység | Tartomány | Számítási logika |
| --- | --- | --- | --- | --- |
| Terhelés (Workload) | getWorkload() | Arány | 0.0 - 1.0 | Aktív ciklusok / Összes ciklus |
| Kihasználtság (Utilization) | getUtilization() | Arány | 0.0 - 1.0 | Aktív ciklusok / Összes ciklus |
| Ritkasági arány (Sparsity Ratio) | sparsity_ratio | Arány | 0.0 - 1.0 | Kapuzott core-ok / Összes core |
| Megtakarított energia | energy_saved | Egység | 0.0 - $\infty$ | Kihagyott aktiválások összege |
| Átlagos ugrások (Hops) | average_message_hops | Ugrás | 1.0 - $(W+H)$ | Összes ugrás / Összes üzenet |
| Energia kihasználtság | getPowerUtilization() | Arány | 0.0 - 1.0 | Jelenlegi energia / Energiakeret |

Adatáramlás a statisztikák gyűjtéséhez A nyers számlálók a ProcessingCore-on és a specializált vezérlőkön belül aggregálódnak az RGPUStatistics struct-ba.

 Core teljesítménymetrikák

 Terhelés és kihasználtság
A jelenlegi implementációban a getWorkload() és a getUtilization() funkcionálisan azonosak. Egy adott core-ra nehezedő időbeli nyomást képviselik.
- Implementáció: Az aktív ciklusok és az aktív + üresjárati ciklusok összegének arányaként számítva.
- Jelentőség: A magas kihasználtság (> 0.8) kiváltja a PowerGatingController-t, hogy visszakapcsolja a core-okat a terhelés elosztása érdekében.

 Átlagos üzenet ugrások (Average Message Hops)
Ez a metrika az XY routing algoritmus hatékonyságát és a gráf particionálás térbeli lokalitását követi nyomon.
- Implementáció: Az AsynchronousNoC növeli a total_hops számlálót minden alkalommal, amikor egy üzenet szomszédos core-ok között mozog a routeMessages()-ben.
- Számítás: total_hops / total_messages.
- Várható tartomány: Egy $W \times H$ mesh esetén a maximális ugrások száma bármely egyetlen üzenetnél $(W-1) + (H-1)$ az XY routing determinisztikus természete miatt.

 Energiahatékonysági metrikák

Az **RGPU** egy kétrétegű energiagazdálkodási stratégiát alkalmaz: Sparse Activation (finomszemcsés, feladatonkénti) és Power Gating (durvaszemcsés, időbeli).

 Ritkasági arány (Sparsity Ratio)
Azt a százalékos arányt méri, amelyet a SparseActivationManager jelenleg megkerül a hálózatban.
- Implementáció: A computeSparsityRatio()-ban számítva, összehasonlítva azon core-ok számát, amelyek terhelése a sparsity_threshold alatt van, a teljes core számmal.
- Normál működés: A magasabb arányok ritka gráfot jeleznek, ahol a legtöbb relációs feldolgozás kihagyható az energiamegtakarítás érdekében.

 Megtakarított energia (Energy Saved)
Egy kumulatív számláló, amely a core-ok aktiválásának elkerülésével *megtakarított* teljes energiát képviseli.
- Implementáció: Minden alkalommal, amikor a shouldActivateCore() false értéket ad vissza, az energy_saved számláló 1.0-val nő.
- Integráció: Ez a RelationalGraphProcessingUnit párhuzamos végrehajtási fázisaiban történik, mint például a processIsomorphismParallel.

 Energia kihasználtság (Power Utilization)
A jelenlegi áramfelvétel és a definiált hardveres energiakeret aránya.
- Implementáció: A PowerGatingController nyomon követi a current_power-t. Minden aktív core 10.0 egységet fogyaszt, ami levonásra kerül, amikor egy core kapuzva van.
- Számítás: current_power / power_budget.

 Metrika referencia táblázat

| Metrika | Forrás függvény | Adatfüggőségek | Tipikus értékek |
| --- | --- | --- | --- |
| Aktív Core-ok | getStatistics | ProcessingCore.state | 1-től total_cores-ig |
| Kapuzott Core-ok | getStatistics | CoreState.power_gated | 0-tól total_cores-ig |
| Összes Energia | getStatistics | ProcessingCore.energy_consumed | Kumulatív; terheléstől függ |
| Végrehajtási Ciklusok| getStatistics | RGPU.execution_cycles | Növekszik minden processGraph() hívásnál |
| Ritkasági Arány | computeSparsityRatio | sparsity_threshold | 0.2 - 0.9 (Ritka gráfok) |
| Energia Kihasználtság | getPowerUtilization | power_budget | 0.4 - 0.8 (Stabil rendszer) |

 Implementációs megjegyzés: Ciklusszámlálás
A ciklusok minden ProcessingCore-on belül nyomon vannak követve.
- cycles_active: Növekszik, amikor a core .processing vagy .communicating állapotban van.
- cycles_idle: Növekszik, amikor a core .idle állapotban van.
- power_gated állapot: Gyakorlatilag befagyasztja a ciklusszámlálókat, mivel a core logikailag le van állítva.

---

 Gráf szinkronizáció

Az r_gpu architektúrában a gráffeldolgozás elosztott módon történik, ahol minden ProcessingCore egy local_graph-on operál. A synchronizeGraphs() metódus az a kritikus egyeztetési lépés, amely ezeket az elosztott módosításokat visszamergeli a RelationalGraphProcessingUnit global_graph-jába. Ez a folyamat biztosítja, hogy a párhuzamos végrehajtás során felfedezett strukturális változások, súlyfrissítések és új node-ok egy konzisztens globális állapotba egyesüljenek.

 Szinkronizáció célja és időzítése

A szinkronizáció a *Reduce* fázisként működik a rendszer Map-Reduce stílusú feldolgozási folyamatában. Tipikusan egy feldolgozási ciklus végén hívják meg az eredmények konszolidálására a következő iteráció előtt, vagy mielőtt a végső gráfot visszaadnák a felhasználónak.

| Folyamat fázis | A szinkronizáció szerepe |
| --- | --- |
| Előfeldolgozás | A distributeGraph() particionálja a global_graph-ot local_graph példányokra. |
| Végrehajtás | A core-ok módosítják a local_graph-ot (izomorfizmus detektálás, él-súlyozás). |
| Utófeldolgozás | A synchronizeGraphs() visszamergeli a local_graph adatokat a global_graph-ba. |

 Implementációs logika

A synchronizeGraphs() metódus végigiterál az AsynchronousNoC mesh minden ProcessingCore-ján. Ha egy core-nak van aktív local_graph-ja, annak tartalma bemergelésre kerül a global_graph-ba egy deduplikációs stratégia használatával mind a node-okra, mind az edge-ekre.

Adatáramlás: Lokálistól a globálisig Az entitások az elosztott ProcessingCore tárolóból visszamozognak a központi RelationalGraphProcessingUnit-ba.

Node és Edge deduplikáció A szinkronizációs logika a mögöttes nsir_core struktúrákra támaszkodik az identitás kezeléséhez.

## Node-ok: Egy local_graph minden node-ja esetén a rendszer ellenőrzi, hogy a node ID létezik-e már a global_graph-ban. Ha nem, egy új Node jön létre a globális térben.

## Edge-ek: Minden edge esetén a rendszer az EdgeKey-t (amely a forrás ID-ből, cél ID-ből és a reláció típusából áll) használja a global_graph-ban való létezés ellenőrzésére.
    - Ha az edge új, hozzáadódik a saját EdgeQuality-jével és súlyával.
    - Ha az edge létezik, a rendszer egy Súlyfrissítést (Weight Update) hajt végre: a globális él-súly frissül, hogy tükrözze a core-ban talált lokális súlyt.

 Implementációs részletek

Az implementáció a Zig Iterator mintáit használja a SelfSimilarRelationalGraph-on belül tárolt hash map-ek bejárására.

Core ciklus struktúra A függvény először törli a global_graph node-jait és edge-eit (miközben megőrzi a kapacitást), hogy biztosítsa a tiszta merge-et, ha a szinkronizáció egy teljes állapotcserét céloz, vagy egyszerűen iterál és hozzáfűz, ha a globális gráf üres volt.

 Főbb megfontolások
- Memóriakezelés: A synchronizeGraphs metódus nem szabadítja fel a local_graph példányokat. A tulajdonjog a ProcessingCore-nál marad a deinit() vagy egy későbbi distributeGraph() hívásig.
- Állapotátmenet: A szinkronizáció során a core állapotok nem változnak explicit módon communicating-re, mivel ez egy host-szintű menedzsment műveletnek számít, nem pedig core-ok közötti NoC üzenetváltásnak.
- Súly precedencia: A jelenlegi implementációban az utolsóként feldolgozott core, amely tartalmaz egy adott edge-et, *nyeri* a súlyértéket a global_graph-ban.

---

 Szójegyzék

Ez az oldal átfogó referenciát nyújt az r_gpu kódbázisban használt kifejezésekhez, rövidítésekhez és domén koncepciókhoz. Hídként szolgál a magas szintű gráffeldolgozási elmélet és a Zig forráskód specifikus implementációs részletei között.

 1. Rendszerkomponensek és szerepkörök

Az r_gpu egy hardver-szoftver co-design szimulációként van megtervezve. A következő entitások definiálják a rendszer strukturális és funkcionális egységeit.

| Kifejezés | Definíció |
| --- | --- |
| RGPU | A gráffeldolgozási feladatok legfelső szintű koordinátora, amely a NoC-ot, az alrendszereket és az energiát kezeli. (RelationalGraphProcessingUnit) |
| ProcessingCore | Egy szimulált számítási egység a 2D griden belül, amely saját lokális gráf partíciót és üzenetsort tartalmaz. |
| NoC (Network-on-Chip) | Az aszinkron kommunikációs hálózat, amely a core-okat egy mesh topológián keresztül köti össze. (AsynchronousNoC) |
| Isomorphism Processor | A gráfszegmensek közötti strukturális ekvivalencia detektálásáért felelős alrendszer. (GraphIsomorphismProcessor) |
| Edge Weighting | Logika a gráf él-erősségeinek megerősítéses tanuláson alapuló beállításához. (DynamicEdgeWeighting) |

 2. Alapfogalmak és metrikák

 Gráf particionálás és állapot
Az **RGPU** egy global_graph-ot dolgoz fel úgy, hogy elosztja azt a griden.
- Local Graph (Lokális gráf): A globális gráf egy részhalmaza, amelyet egy adott ProcessingCore birtokol vagy dolgoz fel.
- CoreState: Egy enumeráció, amely definiálja a core aktuális működési módját: idle, processing, communicating, vagy power_gated.
- Canonical Form (Kanonikus forma): Egy gráf string reprezentációja, amelyet izomorfizmus tesztelésre használnak, és a node-ok számából, a rendezett fokszámokból és az él-minőségekből származtatnak.

 Energia és hatékonyság
- Sparse Activation: Egy technika, ahol a sparsity_threshold alatti terhelésű core-okat megkerülik az energiamegtakarítás érdekében.
- Power Gating: A core áramellátásának leállítási folyamata. A szimulációban ez csökkenti a current_power-t és az állapotot power_gated-re állítja.
- Workload / Utilization (Terhelés / Kihasználtság): Az aktív ciklusok és az összes ciklus (aktív + üresjárati) aránya egy core esetében.

 3. Kommunikáció és routing

Az AsynchronousNoC kezeli az összes core-ok közötti forgalmat egy csomagkapcsolt modell használatával.
- XY Routing: Egy determinisztikus routing algoritmus, ahol egy üzenet először az X-tengely mentén halad a cél oszlopáig, majd az Y-tengely mentén a cél soráig.
- Priority Queue (Prioritási sor): Az üzenetek egy PriorityQueue-ban vannak tárolva a NoC-on belül, a priority mezőjük alapján rendezve, hogy a kritikus vezérlőjelek (mint a power_control) elsőként kerüljenek kézbesítésre.
- Hop (Ugrás): Egyetlen mozgás egy core-tól egy szomszédos core-ig. A total_hops metrika követi nyomon a routing hatékonyságát.

 4. Analitikai algoritmusok

 Dinamikus súlyozás
A rendszer megerősítéses tanulási elvek használatával alkalmazkodik az adatmintákhoz.
- Learning Rate (Tanulási ráta): Egy tényező (f64), amely meghatározza, hogy az új visszacsatolás mennyire befolyásolja a meglévő él-súlyt.
- Weight Propagation (Súly propagálás): Egy **BFS**-alapú bejárás, amely a súlyfrissítéseket a szomszédos node-okra terjeszti egy bomlási tényezővel (alapértelmezés szerint 0.9).
- Adaptive Weight (Adaptív súly): Egy összetett érték, amelyet temporális, térbeli és szemantikus tényezőkből számítanak ki.

 Izomorfizmus detektálás
- Sliding Window (Csúszóablak): A findIsomorphicSubgraphs-ban használt módszer egy gráf alszegmenseinek kinyerésére egy célmintával való összehasonlításhoz.

 5. Főbb struct-ok összefoglaló táblázata

| Struct | Cél |
| --- | --- |
| RelationalGraphProcessingUnit | A szimuláció fő hangszerelője. |
| ProcessingCore | Egyetlen csempét (tile) képvisel a NoC gridben. |
| AsynchronousNoC | Kezeli a mesh topológiát és az üzenet routingot. |
| NoCMessage | Adatcsomag a core-ok közötti kommunikációhoz. |
| GraphIsomorphismProcessor | Logika a kanonikus formához és a gráf összehasonlításhoz. |
| DynamicEdgeWeighting | Logika a súlyfrissítésekhez és a propagáláshoz. |
| SparseActivationManager | Logika a terhelésalapú core kihagyáshoz. |
| PowerGatingController | Logika az energiakeret kezeléséhez. |
| RGPUStatistics | Tároló a teljesítmény- és energiametrikákhoz. |
