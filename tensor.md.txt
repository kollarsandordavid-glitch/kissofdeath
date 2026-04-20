# kollarsandor/tensor – Teljes dokumentáció (Magyar)

> Forrás: https://deepwiki.com/kollarsandor/tensor  
> Generálva: 2026-04-12

---

## Áttekintés

A `tensor` könyvtár egy nagy teljesítményű numerikus számítási keretrendszer, amely egyedülálló módon ötvözi a formális verifikációt a rendszerszintű hatékonysággal. Kétnyelvű architektúrát alkalmaz: a **Lean 4** matematikailag igazolt specifikációt biztosít a tensor-műveletek és invariánsok számára, míg a **Zig** egy hatékony, memóriagazdálkodás szempontjából optimalizált futtatókörnyezetet valósít meg.

### Kétnyelvű architektúra

A könyvtár két elsődleges komponensből áll, amelyek tükrözik egymás logikáját:

**Formális specifikáció (`tensor.lean`):** Meghatározza a tensorok, alakzatok és referenciaszámlálás alapvető tulajdonságait. Bizonyítékokat tartalmaz kritikus invariánsokra, például arra, hogy a referenciaszámok soha nem mehetnek nulla alá, és az indexszámítások határon belül maradnak.

**Nagy teljesítményű futtatókörnyezet (`tensor.zig`):** Ugyanazt a logikát valósítja meg Zigben a gyors végrehajtás érdekében. Kézi memóriakezelést, hardverszintű optimalizálásokat és különféle allokációs stratégiákat (Arena, Pool, Slab, Buddy) kezel.

### Tervezési filozofia

A tervezés középpontjában a **Biztonság**, a **Hatékonyság** és a **Helyesség** áll:

- **Változatlanság és CoW:** A tensorok Copy-on-Write (másolás íráskor) mechanizmust használnak. Az adatok megosztottak a nézetek és szeletek között, egészen addig, amíg módosítás nem szükséges, ekkor jön létre a privát másolat.
- **Igazolt indexelés:** A logikai többdimenziós indexelést ellenőrzött stride-számítással képezi le lapos memóriaeltolásokra, ami specifikációs szinten megakadályozza a határon kívüli hozzáférést.
- **Memória rugalmasság:** A könyvtár több allokációs stratégiát támogat, különböző munkaterhelési profilokhoz igazítva.

---

## Projektstruktúra és tervezési filozofia

### Kétnyelvű architektúra részletesen

A kódbázis két elsődleges fájl köré szerveződik, amelyek tükrözik egymás logikáját, de különböző célokat szolgálnak:

**`tensor.lean` (Formális specifikáció):** A Lean 4 függő típusrendszerét használja az invariánsok bizonyítására (például az indexelés biztonsága és az alakzat-kompatibilitás), és gondoskodik arról, hogy a műveletek matematikailag jól definiáltak legyenek.

**`tensor.zig` (Futtatókörnyezet implementáció):** Nagy teljesítményű implementációt biztosít az igazolt logika számára. Kézi memóriakezelést, hardverspeficikus optimalizálásokat (például SIMD-barát hurkok) és többszálú biztonságot kezel atomi műveletek és mutexek segítségével.

| Jellemző | Lean 4 implementáció | Zig implementáció |
|---|---|---|
| **Elsődleges cél** | Formális helyesség és bizonyítékok | Végrehajtási sebesség és hatékonyság |
| **Memória** | Funkcionális (változtathatatlan/kezelt) | Kézi (allokátorok/mutatók) |
| **Biztonság** | Fordítási idejű matematikai bizonyítékok | Futásidejű ellenőrzések és mutexek |
| **Hibakezelés** | `TResult` (Except monad) | Hibaunionok (`!`) |

### Kulcsfontosságú implementációs részletek

**Shape és stride-ok:** Mindkét implementáció sor-főrendű stride-okat számít ki, hogy a többdimenziós indexeket lapos memóriapufferre képezze le. A Lean a `computeStrides` függvényt használja, a Zig a `Shape.init` függvényt, ahol `@mulWithOverflow` gondoskodik az egészszám-túlcsordulás elkapásáról.

**Copy-on-Write logika:** A `cow` mező (Zigben `bool`, Leanben `CowState` struktúra) határozza meg, hogy egy tensor puffere helyben módosítható-e. Minden módosító műveletnek előbb meg kell hívnia az `ensureWritable` függvényt. Ha `cow` igaz, új puffer kerül allokálásra, az adat átmásolásra kerül, és a tensor az új puffer egyedüli tulajdonosává válik.

**Formális invariánsok:** A Lean implementáció olyan bizonyítékokat nyújt, amelyekre a Zig futtatókörnyezet a stabilitása érdekében támaszkodik:
- `h_len`: Biztosítja, hogy a dimenziók száma mindig egyezzen a stride-ok számával.
- `h_pos`: Bizonyítja, hogy a referenciaszám soha nem lehet nulla, amíg egy tensor objektum létezik.
- `listProduct_pos`: Garantálja, hogy a pozitív dimenziójú tensorok teljes mérete nagyobb nullánál.

---

## Első lépések

### Előfeltételek

A teljes kódbázissal való munkához a következő eszközök szükségesek:

1. **Lean 4 eszközlánc:** A formális verifikációhoz és a magas szintű specifikációhoz szükséges. Az `elan` eszközzel ajánlott telepíteni.
2. **Zig fordító (0.11.0 vagy újabb):** A teljesítményorientált futtatókörnyezet és a memóriakezelő rendszerek fordításához szükséges.
3. **Standard build eszközök:** `make` vagy hasonló segédprogramok a két nyelv közötti build-folyamat koordinálásához.

### Build folyamat

A könyvtár két elsődleges komponensből áll: `tensor.lean` és `tensor.zig`. A Lean formális ellenőrzi a logikát (például `reshape`), a Zig pedig pointer-manipulációra és szálbiztonságra fókuszálva implementálja azt.

### Minimális használati példák

**Tensorok létrehozása Zigben:**

Zigben a tensorokat egy `Allocator` segítségével hozzák létre. A könyvtár támogatja a standard allokátorokat, valamint a specializált allokátorokat, mint az `ArenaAllocator` vagy `PoolAllocator`.

**Igazolt tensorok Leanben:**

Leanben a tensorok változtathatatlan struktúrákként kezelendők, explicit referenciaszámlálással és Copy-on-Write szemantikával, amelyet a `Tensor` struktúra definiál.

### Kulcsfontosságú implementációs fogalmak

**Memóriakezelés:** A könyvtár `RefCount` rendszert használ a tulajdonjog követésére. Amikor egy tensor megosztásra kerül (például `retain` hívással), a `CowState` megosztottként jelölődik. Bármely azt követő módosítás meghívja az `ensureWritable` függvényt, amely mély másolatot készít, ha a referenciaszám egynél nagyobb.

**Hibakezelés:** Minden hibás művelet `TResult`-et ad vissza Leanben, illetve `Error` uniont Zigben. Általános hibák: `shapeMismatch`, `outOfBounds`, `overflow`.

---

## Alapvető adatstruktúrák

A könyvtár négy elsődleges entitás köré szerveződik: `Shape`, `Tensor`, `RefCount` és `CowState`.

### Shape és Stride-ok

A `Shape` struktúra definiálja a tensor geometriáját. Két elsődleges tömböt tartalmaz:
- `dims`: Az egyes dimenziók mérete (például `[3, 224, 224]` egy CHW képhez).
- `strides`: Az a lépésszám a lapos pufferben, amellyel egy egységet lépünk egy adott dimenzióban.

Leanben a `Shape` struktúra tartalmaz egy formális `h_len` bizonyítékot is, amely garantálja, hogy a dimenziók és stride-ok listájának hossza azonos.

### Tensor struktúra és memória-elrendezés

A `Tensor` struktúra az numerikus adatok elsődleges tárolója. Leanben a `Tensor` egy tisztán funkcionális struktúra, ahol a `data` egy `Array Float`. Zigben a `Tensor` struktúra összetettebb: elkülöníti a `data`-t (az aktuális nézetet) és a `base_data`-t (az eredeti allokációt), hogy zéró-másolatú szeletelést és ablakozást támogasson.

### Referenciaszámlálás és Copy-on-Write

A teljesítmény és biztonság egyensúlyának megtartásához a könyvtár referenciaszámlálási (RC) rendszert alkalmaz, kombinálva Copy-on-Write (CoW) mechanizmussal:

1. **RefCount:** Nyomon követi, hogy hány `Tensor` handle mutat ugyanarra az adatpufferre. Zigben ezt atomi műveletek (`@atomicRmw`) kezelik a szálbiztonság érdekében.
2. **CowState:** Boolean jelző (`isShared`), amely jelzi, hogy a puffert jelenleg több tensor osztja-e meg.
3. **ensureWritable:** Minden módosító művelet előtt a rendszer ellenőrzi a CoW állapotot. Ha a tensor megosztott, mély másolatot készít egy új privát pufferbe, mielőtt folytatná.

**Összefoglaló táblázat az alapvető entitásokról:**

| Entitás | Lean szimbólum | Zig szimbólum | Felelősség |
|---|---|---|---|
| **Shape** | `Shape` | `Shape` | Metaadatok a dimenziókhoz és memória stride-okhoz |
| **Tensor** | `Tensor` | `Tensor` | Fő objektum, amely tárolja az adatokat, az alakzatot és a szinkronizációs primitíveket |
| **Ref Count** | `RefCount` | `refcount` | Életciklus-kezelés és megosztott memória követése |
| **CoW State** | `CowState` | `cow` | Nyomon követi, hogy a puffert klónozni kell-e módosítás előtt |

---

## Shape és Stride-ok (részletes)

### A Shape struktúra

A `Shape` struktúra egy tensor geometriáját foglalja magában. Alapértelmezett sor-főrendű (C-stílusú) elrendezést alkalmaz. Mindkét implementációban a `Shape` két elsődleges tömbből áll: `dims` és `strides`.

| Mező | Lean típus | Zig típus | Leírás |
|---|---|---|---|
| `dims` | `List Nat` | `[]usize` | Az egyes tengelyek méretei |
| `strides` | `List Nat` | `[]usize` | Memóriaeltolások az egyes tengelyekhez |
| `h_len` | `dims.length = strides.length` | N/A | Lean invariáns: a dims és strides hossza egyenlő kell legyen |

### Stride-számítás (sor-főrend)

A könyvtár alapértelmezésben sor-főrendű (C-stílusú) elrendezést alkalmaz. Ebben az elrendezésben az utolsó dimenzió stride-ja 1, és minden megelőző dimenzió stride-ja az összes rákövetkező dimenzióméret szorzata.

Zigben a `Shape.init` visszafelé iterál a dimenziókon:
1. Az utolsó stride-ot 1-re állítja.
2. Minden `i`-re fentről lefelé: `strides[i-1] = strides[i] * dims[i]`.

### Folytonossági predikátum (`isContiguous`)

Egy alakzat folytonosnak tekinthető, ha a memória-elrendezése megfelel a standard sor-főrendű bejárásnak, hézagok vagy permutációk nélkül. Az ellenőrzés azt vizsgálja, hogy `strides[i] == dims[i+1] * strides[i+1]`.

### Broadcasting logika (`broadcastCompatible`)

A broadcasting lehetővé teszi a különböző alakzatú tensorok közötti műveleteket, ha a dimenziók kompatibilisek. A könyvtár NumPy-stílusú szabályokat követ:
1. A célobjektum-alakzatnak legalább annyi dimenziója kell legyen, mint a forrásnak.
2. A záró dimenzióktól kezdve a méretek vagy egyeznek, vagy a forrás dimenziója 1.

### Indexelési képletek

A lapos index (flat index) az indextömb és a stride-ok skaláris szorzata:

$$\text{flatIndex} = \sum_{i=0}^{n-1} \text{indices}_i \times \text{strides}_i$$

A Lean a `multiToFlatIndex` függvényt, a Zig a `computeIndex` függvényt használja erre a célra. A `flatToMultiIndex` az inverz irányú leképezést végzi, amelyet például redukciós műveleteknél alkalmaznak.

---

## Tensor struktúra és memória-elrendezés (részletes)

### Lean 4 reprezentáció

Leanben a `Tensor` egy induktív struktúra, ahol az adatok mérete és az alakzat teljes mérete közötti kapcsolatot a `h_data_size` formális bizonyíték érvényesíti.

| Mező | Típus | Leírás |
|---|---|---|
| `data` | `Array Float` | A tensor elemek alapjául szolgáló lapos tár |
| `shape` | `Shape` | Tartalmazza a dimenziókat és az előre kiszámított stride-okat |
| `h_data_size` | `data.size = shape.totalSize` | Bizonyíték, hogy a tömb hossza megegyezik a logikai térfogattal |
| `refcount` | `RefCount` | Objektum élettartamának nyomon követése a funkcionális modellhez |
| `cow` | `CowState` | Nyomon követi, hogy a tensor megosztott állapotban van-e |

### Zig reprezentáció

A Zig `Tensor` struktúra kézi memóriakezelésre és FFI-kompatibilitásra tervezték. Bevezeti a `data`/`base_data` felosztást a hatékony szeletelés támogatásához, az alapul szolgáló puffer újraallokálása nélkül.

| Mező | Típus | Leírás |
|---|---|---|
| `data` | `[]f32` | Aktív nézet a tensor memóriájába |
| `base_data` | `[]f32` | Az eredeti allokált memóriablokk (deallokációhoz) |
| `shape` | `Shape` | `dims` és `strides` szeleteket tartalmazó struktúra |
| `allocator` | `Allocator` | A tensor létrehozásához használt allokátor |
| `refcount` | `*usize` | Mutató az atomi referenciaszámlálóhoz |
| `cow` | `*bool` | Mutató a Copy-on-Write állapotjelzőhöz |
| `mutex` | `*std.Thread.Mutex` | Mutex a megosztott és privát állapot közötti átmenetek védelmére |

---

## Referenciaszámlálás és Copy-on-Write (részletes)

### RefCount és CowState alrendszerek

A könyvtár két elsődleges struktúrán keresztül kezeli a tensor memóriát: `RefCount` és `CowState`. Ezek biztosítják, hogy több tensor-nézet mutasson ugyanarra az adatpufferre felesleges másolás nélkül, miközben automatikusan másolatot indítanak, ha egy megosztott puffert módosítani kell.

**Referenciaszámlálási logika:**
- Inicializáláskor az új tensor 1-es számlálóval kezd.
- `Retain`: A számláló növelése mindig megőrzi a pozitivitást.
- `Release`: A számláló csökkentése `Option RefCount`-ot ad vissza. Ha a szám eléri a nullát (amit `none` jelöl), az erőforrások biztonságosan felszabadíthatók.

**Copy-on-Write állapot:**
Ha `isShared` igaz, bármely módosító műveletnek először privát másolatot kell készítenie az adatokból.

### Szálbiztonság és Mutex integráció

A Zig implementációban a szálbiztonságot egy `std.Thread.Mutex` biztosítja, amelyet minden tensor tárol. Ez a mutex védi az átmenetet megosztott állapotból privát állapotba egy CoW művelet során.

**`markShared()` és `ensureWritable()`:**
1. A `markShared()` a `retain()` művelet során hívódik meg. A `cow` jelzőt `true`-ra állítja.
2. Az `ensureWritable()` minden módosítás előtt meghívódik. Ha a `cow` jelző be van állítva, lezárja a mutexet, allokál egy új puffert, átmásolja a meglévő adatokat, és `false`-ra állítja a `cow` jelzőt.

**Invariáns bizonyítékok (Lean 4):**
- `RefCount.no_underflow`: Bizonyítja, hogy `rc.count > 0` mindig teljesül.
- `RefCount.release_last`: Bizonyítja, hogy ha `count = 1`, a `release` `none`-t ad vissza.
- `CowState.makeWritable_not_shared`: Bizonyítja, hogy a CoW átmenet helyesen visszaállítja a megosztott állapotot.

---

## Tensor műveletek – Áttekintés

A tensor könyvtár API-ja a többdimenziós adatokat specializált alrendszereken keresztül kezeli. Minden művelet alakzat-ellenőrzési és memóriabiztonsági ellenőrzésnek van alávetve.

### 3.1 Tensor létrehozás és inicializálás

A tensorok standard factory metódusokkal vagy specializált memória-alapú allokátorokkal inicializálhatók: konstansok (`zeros`, `ones`, `full`), sorozatok (`arange`, `linspace`) és véletlen eloszlások (`randomUniform`, `randomNormal`).

### 3.2 Alakzat-transzformációk és nézetek

A strukturális műveletek lehetővé teszik a tensor adatok újraértelmezését az alapul szolgáló memóriapuffer szükségtelen másolása nélkül: `reshape`, `view`, `transpose`, valamint NumPy-stílusú broadcasting.

### 3.3 Elemenkénti és redukciós műveletek

A matematikai műveletek elemenkénti transzformációkra és redukciókra oszthatók. Elemenkénti műveletek: `add`, `mul`, `exp`, `relu`. Redukciók: `sum`, `mean`, `argmax`.

### 3.4 Lineáris algebra műveletek

A könyvtár átfogó lineáris algebra rutinokat tartalmaz: `matmul`, `conv2d`, mátrixinverzió (Gauss-Jordan eliminálással), `QR` dekompozíció (Householder reflexiókkal) és `SVD` (Jacobi rotációkkal).

---

## Tensor létrehozás és inicializálás (részletes)

### Alap factory metódusok

A tensor létrehozásának elsődleges belépési pontja az `init` metódus, amely nulla-inicializált puffert allokál.

| Függvény | Leírás |
|---|---|
| `init` | Adott alakzatú, nulla-inicializált tensor |
| `zeros` | Az `init` aliasa |
| `ones` | `1.0`-val kitöltött tensor |
| `full` | Megadott skalárral kitöltött tensor |

**Hibaállapotok inicializáláskor:**
- `invalidShape`: Ha az alakzat lista üres vagy nulla méretű dimenziót tartalmaz.
- `overflow`: Ha a dimenziók szorzata meghaladja a `usize` maximumát.
- `allocFailed`: Ha az allokátor nem tudja teljesíteni a memóriakérést.

### Specializált allokátor-alapú inicializálók

A Zig implementáció lehetővé teszi a tensorok számára, hogy specializált memóriakezelési stratégiák legyenek mögöttük:

- `initWithArena`: `memory.ArenaAllocator`-t használ gyors, ideiglenes allokációkhoz.
- `initWithPool`: `memory.PoolAllocator`-t használ rögzített méretű memóriablokkok hatékony kezeléséhez.
- `initWithSlab`: `memory.SlabAllocator`-t használ a töredezettség csökkentéséhez.
- `initWithBuddy`: `memory.BuddyAllocator`-t használ kettő hatványain alapuló memóriaosztáshoz.

### Sorozat- és véletlen inicializálás

- `arange`: 1D tensor generálása `start`-tól `stop`-ig adott `step`-pel.
- `linspace`: 1D tensor adott számú lépéssel `start` és `stop` között.
- `randomUniform`: $U(min, max)$ egyenletes eloszlásból mintavételezett tensor.
- `randomNormal`: $N(\mu, \sigma)$ normális eloszlásból mintavételezett tensor (Box-Muller transzformációval).

### Stride-számítás inicializáláskor

A `Shape.init` során a könyvtár sor-főrendű stride-okat számít ki a hatékony lapos indexeléshez. Az `i` dimenzió stride-ja az összes következő dimenzióméret szorzata:

$$stride_i = \prod_{j=i+1}^{n-1} dim_j$$

---

## Alakzat-transzformációk és nézetek (részletes)

### Strukturális műveletek típusai

1. **Csak metaadat (nézetek):** `reshape` és `view` – csak a `Shape`-et módosítják, ha az adat folytonos marad.
2. **Index-alapú (szeletek):** `slice` – új `Tensor` objektumot hoz létre, amely a `base_data` egy részterületére mutat.
3. **Bővítés/transzformáció:** `broadcast`, `transpose`, `pad`, `tile` – új stride-okat számít ki vagy új puffert allokál.

### Reshape és View

A `reshape` művelet megváltoztatja a tensor logikai dimenzióit, miközben megköveteli, hogy az elemek teljes száma (`totalSize`) konstans maradjon. Ha a tensor folytonos, nulla másolatú frissítést hajt végre.

### Szeletelés és részterületek

A szeletelés hatékonyan kivonja a tensor egy részterületét. A Zig implementációban a `Tensor` struktúra mindkét mutatót tárolja (`data` és `base_data`), az új szelet megosztja az eredeti `base_data`-t, a `refcount`-ot növeli a `retain()` hívással, és mindkét tensort megosztottként jelöli.

### Transzponálás és tengely-permutáció

A transzponálás általában **nézet** művelet: nem mozgatja az adatokat a memóriában, csupán felcseréli a `Shape.strides` és `Shape.dims` tömb értékeit. Az eredmény nem folytonos tensor lesz.

### Broadcasting

A broadcasting lehetővé teszi az eltérő alakzatú tensorok közötti elemenkénti műveleteket a méret 1-es dimenziók virtuális bővítésével. Az 1 méretű dimenzióra a stride **0**-ra van állítva, így az adott tengely mentén bármely indexnövelés mindig ugyanarra a memóriahelyre mutat.

### Pad, Tile és Repeat

Ezek a műveletek általában új puffer allokálását igénylik:
- **Pad:** Nagyobb tensort hoz létre, és az eredetit egy eltolással másolja be, a maradékot egy értékkel töltve.
- **Tile:** Megismétli a teljes tensort megadott dimenzió mentén.
- **Repeat:** Elemeket ismétel egy adott tengely mentén.

---

## Elemenkénti és redukciós műveletek (részletes)

### Elemenkénti műveletek

**Unáris műveletek (Map):** Egy $f: \mathbb{R} \to \mathbb{R}$ függvényt alkalmaznak a tensor minden elemére.

| Művelet | Leírás |
|---|---|
| `exp` | $e^x$ kiszámítása minden elemre |
| `log` | Természetes logaritmus |
| `sqrt` | Elemenkénti $\sqrt{x}$ |
| `abs` | Abszolút érték |
| `relu` | Korrigált lineáris egység: $\max(0, x)$ |
| `sin`, `cos` | Szinusz és koszinusz |

**Bináris műveletek (Zip):** Két tensort kombinálnak. Ha az alakzatok különböznek, a könyvtár megpróbálja broadcasting-gal a kisebb tensort a nagyobb alakzatra igazítani. Ide tartoznak: `add`, `sub`, `mul`, `div`, `pow`, valamint skalárvariánsok (`addScalar`).

### Redukciós műveletek

A redukciók a tensor egy vagy több dimenzióját kisebb alakzatra (gyakran skalárra vagy alacsonyabb rangú tensorra) redukálják.

**Magasabb rendű redukciók:** A `reduceAxis` alap építőelemet használ, amely egy tensort, egy tengelyindexet, egy kezdeti értéket és egy kombináló függvényt kap. Ide tartoznak: `sum`, `mean`, `max`, `min`, `variance`, `stddev`.

**Index-alapú redukciók:** `argmax` és `argmin` – az érték helyett a pozíciót adják vissza.

**Kumulatív műveletek:** `cumSum` – kumulatív összeget számít egy tengely mentén; a kimenet alakzata megegyezik a bemenetével.

### Specializált matematikai műveletek

**Softmax:** Numerikusan stabil megközelítéssel implementálva: (1) max kiszámítása, (2) max kivonása az elemekből, (3) `exp` kiszámítása, (4) osztás az exponenciálisok összegével.

**Mátrix-specifikus redukciók:** `trace` (átló elemeinek összege), `spectralNorm` (hatványiterációval).

### Implementációs részletek: `mapData` és `zipData`

A Lean implementáció ezekre a belső függvényekre támaszkodik a `h_data_size` invariáns megőrzéséhez. A `mapData` esetén az `Array.map` megőrzi a hosszt, így az invariáns érvényes marad. A `zipData` a művelet előtt explicit `Shape.equals` ellenőrzést végez.

---

## Lineáris algebra műveletek (részletes)

### Alap mátrixműveletek

**Mátrixszorzás (`matmul`):** Standard 2D mátrixszorzást valósít meg. Ellenőrzi, hogy a belső dimenziók egyeznek-e (az A oszlopainak száma egyezik a B sorainak számával), majd kiszámítja a sorok és oszlopok skaláris szorzatát.

**Dot, Outer, Trace:**
- `dot`: 1D tensorok elemszorzatainak összege.
- `outer product`: A $uv^T$ mátrixot számítja ki vektorokra.
- `trace`: Négyzetes mátrixok átlóelemei összegét adja; `mustBeSquare` hibát ad, ha a bemenet nem megfelelő.

### Lineáris egyenletrendszer-megoldók és inverzió

**LU dekompozíció és `solve`:** Az $Ax = B$ egyenletrendszert LU dekompozícióval, majd előre- és visszahelyettesítéssel oldja meg.

**Mátrixinverzió és determinált:** Az inverzió Gauss-Jordan eliminálással van implementálva. Ha a mátrix szinguláris (a pivot nulla), `TensorError.singularMatrix` hibát ad. A determinánst részleges pivotálású Gauss-eliminálással számítják ki.

### Mátrix-dekompozíciók

- **QR dekompozíció:** Householder reflexiókkal van implementálva. A $Q$ ortogonális mátrixra és az $R$ felső háromszögmátrixra bontja a $A$ mátrixot.
- **Szinguláris értékek dekompozíciója (SVD):** Jacobi rotációkkal implementálva.
- **Sajátérték-dekompozíció:** Szimmetrikus mátrixokhoz számítja a sajátértékeket.
- **Cholesky:** Pozitív definit mátrixot $LL^T$-re bont; `notPositiveDefinite` hibát ad, ha a dekompozíció nem sikerül.
- **Spektrális norma:** Hatványiteráció segítségével találja meg a mátrix legnagyobb szinguláris értékét.

### Konvolúciós műveletek

**2D konvolúció (`conv2d`):** Stride-ot és paddingot is támogat. A 4D bemenetet (N, C, H, W) és a 4D kernelt (O, C, KH, KW) leképezi egy kimeneti tensorra. A folyamat: (1) padding alkalmazása, (2) iterálás a kimeneti magasságon és szélességen a stride szerint, (3) 3D skaláris szorzat kiszámítása (csatorna, kernel magasság, kernel szélesség) minden ablakhoz.

---

## Memóriakezelés

### Architektúra áttekintése

A memóriakezelés a Zig `Tensor` struktúrája és a Lean megfelelő `Tensor` struktúrája köré összpontosul. Míg a Lean formális bizonyítékokat biztosít a referenciaszám pozitivitásáról és az alakzat-konzisztenciáról, a Zig implementáció kezeli a fizikai allokációt, szálbiztos referenciaszámlálást és CoW-szemantikát.

### 4.1 Allokátor stratégiák

A könyvtár négy specializált allokátor hátteret biztosít a `memory.zig` modóulon keresztül:

- **ArenaAllocator:** Tömeges allokációkhoz, ahol az összes tensor egyszerre szabadul fel.
- **PoolAllocator:** Rögzített méretű blokkok hatékony kezeléséhez.
- **SlabAllocator:** Méretosztály-gyorsítótárazással csökkenti a töredezettséget.
- **BuddyAllocator:** Kettő-hatványon alapuló memóriaosztás rugalmas, hatékony allokációhoz.

Zigben ezek specializált inicializálókon (`initWithArena`, `initWithPool`, `initWithSlab`, `initWithBuddy`) keresztül érhetők el.

### 4.2 Tensor életciklus: retain, release és deinit

**Életciklus-állapotok:**
1. **Allokáció:** Új puffer kerül allokálásra egy adott allokátoron keresztül.
2. **Retain:** A referenciaszámláló növekszik tensor megosztásakor vagy nézet létrehozásakor.
3. **CoW átmenet:** Ha egy megosztott tensort módosítanak, az `ensureWritable` privát másolatot hoz létre.
4. **Release:** A referenciaszám csökken. Ha nullára ér, a puffer és a metaadatok megsemmisülnek.

**Retain és MarkShared:**
- `retain()` híváskor az atomi `@atomicRmw` növeli a `refcount`-ot.
- `markShared()` azonnal meghívódik, a `cow` jelzőt `true`-ra állítja.

**Release és Deallocate:**
- Ha a referenciaszám egynél nagyobb volt, csak az adott handle `Shape` metaadatai szabadulnak fel.
- Ha a referenciaszám 1 volt, a `deallocate()` felszabadítja a `base_data` puffert, a `refcount` cellát, a `cow` cellát és a mutexet.

**`ensureWritable` – a CoW materializáció útja:**
1. A mutex lezárása (race condition megelőzéséhez).
2. Ha `self.cow.*` `false`, azonnal visszatér.
3. Új puffer allokálása a tensor eredeti allokátorával.
4. Az adatok másolása a megosztott pufferből az új privát pufferbe (a stride-okat figyelembe véve).
5. A `base_data` és `data` mutatók frissítése, `self.cow.*` visszaállítása `false`-ra.

---

## Lean 4 Formális Verifikációs Réteg

### A verifikációs réteg áttekintése

A Lean 4 réteg az igazság forrása (Source of Truth). Minden Zigben implementált műveletnek van egy megfelelő igazolt modellje Leanben. A két oldal egy külföldi funkció-interfészen (FFI) keresztül kommunikál, ahol a Lean struktúrák C-kompatibilis modellekben tükröződnek Zigben.

| Komponens | Lean 4 szerep | Zig szerep |
|---|---|---|
| **Adatstruktúrák** | Funkcionális definíciók (`Structure`) | Memóriahatékony `struct` |
| **Biztonság** | Formális invariáns-bizonyítékok | Futásidejű ellenőrzések és mutexek |
| **Hibakezelés** | `Except` monad (erősen típusos) | Hibaunionok és `TResult` |
| **Logika** | Specifikáció és rekurzió | Hurkok és SIMD-optimalizálás |

---

## Hibakezelés és TResult

### A TResult monad

A könyvtár a `TResult`-et a standard Lean `Except` monad típusaliaszaként definiálja. Ez a tervezési döntés biztosítja, hogy minden hibás művelet explicit módon jelezze a hibalehetőségeit a típusakaláírásában, kényszerítve a hívót a lehetséges hibák kezelésére.

Az `Except` monad használatával a műveletek `do` jelöléssel vagy pipeline operátorokkal (`>>=`) kombinálhatók, lehetővé téve a hibák automatikus propagálását.

### TensorError változatok

A `TensorError` induktív típus 19 változatot tartalmaz, amelyek strukturális, matematikai és rendszerszintű hibákat fednek le:

| Változat | Leírás |
|---|---|
| `shapeMismatch` | Az operandusok dimenziói nem egyeznek |
| `invalidShape` | Az alakzatnak nulla vagy negatív dimenziói vannak |
| `outOfBounds` | Az index meghaladja a dimenzió méretét |
| `overflow` | A számítás eredménye meghaladja az ábrázolható határokat |
| `divideByZero` | Nullát tartalmazó tensorral való osztás |
| `invalidAxis` | A tengelyindex nagyobb vagy egyenlő `ndim`-mel |
| `emptyInput` | Nulla `totalSize`-ú tensoron végzett művelet |
| `mustBeSquare` | A mátrixművelet `rows == cols`-t igényel |
| `singularMatrix` | A mátrix nem invertálható |
| `notConverged` | Az iteratív algoritmus nem érte el a tűréshatárt |
| `allocFailed` | A rendszer memória-allokálása sikertelen |
| `notPositiveDefinite` | A mátrix nem teljesíti a Cholesky-dekompozíció feltételeit |

### Hibás műveletek mintája

Minden hibás műveletnél a `tensor.lean`-ban konzisztens implementációs mintát alkalmaznak: `Tensor` helyett `TResult Tensor`-t adnak vissza.

---

## Formális bizonyítékok és invariánsok

### A formális bizonyítékok áttekintése

A formális verifikációs réteg három elsődleges területre koncentrál:
1. **Alakzat-aritmetika:** Biztosítja, hogy a dimenziók és stride-ok konzisztensek legyenek.
2. **Memória-biztonsági invariánsok:** Bizonyítja, hogy a referenciaszámok nem csúszhatnak nulla alá.
3. **Index-leképezés:** Ellenőrzi a többdimenziós indexek és lapos memóriaeltolások közötti kapcsolatot.

### Shape és szorzattételek

A `listProduct` függvény kiszámítja a tensor elemeinek teljes számát. Kapcsolódó tételek:

- **`listProduct_pos`**: Ha egy lista összes eleme pozitív, a szorzatuk is pozitív. Ez megakadályozza nullás méretű allokációkat.
- **`listProduct_append`**: `listProduct (l1 ++ l2) = listProduct l1 * listProduct l2`. Ez kritikus a `reshape` és `flatten` műveletek ellenőrzéséhez.

**Shape-invariánsok:**

| Tétel | Formális definíció | Cél |
|---|---|---|
| `listProduct_pos` | `allPositive l → listProduct l > 0` | Garantálja a nem-nulla allokációs méretet |
| `computeStrides_length` | `(computeStrides dims).length = dims.length` | Megakadályozza a stride-tömbökön kívüli hozzáférést |
| `Shape.copy_totalSize` | `s.copy.totalSize = s.totalSize` | Garantálja, hogy az alakzat másolata nem változtatja meg a pufferkövetelményeket |

### Referenciaszámlálás és CoW invariánsok

**RefCount invariáns (`h_pos`):**
A `RefCount` struktúra tartalmaz egy `h_pos` invariánst, ami fordítási idejű garancia Leanben, hogy a `RefCount` objektum nem létezhet nulla számlálóval.

- `RefCount.retain`: Bizonyítja, hogy a szám növelése megőrzi a `h_pos`-t.
- `RefCount.release`: Ha `count > 1`, visszaad egy új `RefCount`-ot (csökkentett számlálóval). Ha `count == 1`, `none`-t ad vissza, jelezve a Zig futtatókörnyezetnek a `deinit` aktiválását.

**Copy-on-Write (CoW) átmenetek:**
- `markShared`: `isShared`-t `true`-ra állítja.
- `makeWritable`: `isShared`-t `false`-ra állítja.
- `CowState.makeWritable_not_shared`: Bizonyítja a CoW átmenet helyességét.

### Indexelés és stride-ok

Az ellenőrzött lapos index-képlet: `multiToFlatIndex (strides, indices) = Σ (indices[i] * strides[i])`.

**Zig biztonsági tulajdonságainak összefoglalója:**
1. **Puffer határai:** `t.data.size = t.shape.totalSize` – megakadályozza a puffer-túlcsordulást.
2. **Nincs alulcsordulás:** `RefCount.no_underflow` – biztosítja, hogy a `release` soha nem csökkent nulla alá.
3. **Egyenlőség szimmetriája:** `Shape.equals_symm` – biztosítja a broadcasting-ban és összefűzésben használt alakzat-összehasonlítás kommutativitását.

---

## ZigTensorModel és FFI Bridge

### Adatstruktúrák áttekintése

**ZigShapeModel:** Tükrözi a Lean `Shape` struktúrát, tartalmazza a dimenziókat, stride-okat és az allokációs stratégiára vonatkozó metaadatokat.

| Mező | Típus | Leírás |
|---|---|---|
| `dims` | `[]usize` | A tensor logikai dimenziói |
| `strides` | `[]usize` | Előre kiszámított stride-ok az indexeléshez |
| `totalSize` | `usize` | Az összes dimenzió szorzata |
| `allocatorTag` | `u8` | A memória háttér azonosítója (Arena, Pool, Slab, Buddy) |
| `ownsBuffer` | `bool` | Jelző, hogy a tensor felelős-e az adatok felszabadításáért |

**ZigTensorModel és SharedState:** A `ZigTensorModel` az elsődleges FFI bridge struktúra. A `SharedState` rekord kezeli az alapul szolgáló `f32` puffer életciklusát több nézeten vagy referenciaszámon keresztül.

**SharedState komponensek:**
- `baseData`: Nyers mutató a memóriablokkra.
- `refcountCell`: Atomi számláló az aktív referenciák nyomon követésére.
- `cowCell`: Boolean jelző, ha igaz, bármely módosító műveletet CoW-nak kell előznie.
- `releasedFlag`: Biztonsági mechanizmus a dupla felszabadítás vagy felszabadítás utáni hozzáférés megelőzésére FFI átmenetekkor.

### Az FFI Bridge mechanizmus

**`zigApiBindings` regiszter:** 90 string-függvény leképezést tartalmazó statikus regiszter. Ez lehetővé teszi a Lean környezetnek, hogy névvel hívjon meg specifikus Zig függvényeket, átadva a `ZigTensorModel`-t opak mutatóként.

**Főbb regisztrált kötések:**
- Létrehozás: `zeros`, `ones`, `arange`, `randomNormal`.
- Matematika: `matmul`, `conv2d`, `spectralNorm`.
- Dekompozíciók: `lu`, `qr`, `svd`, `cholesky`.
- Redukciók: `sum`, `mean`, `argmax`.

**Adatfolyam: Leantől Zigig:**
1. A Lean oldal biztosítja az összes előfeltétel (például alakzat-kompatibilitás) teljesítését igazolt logikával.
2. A Lean átadja a `Tensor` objektumot (`ZigTensorModel` mutatóként) a Zig háttérnek.
3. A Zig háttér fogadja a modellt, lezárja a `SharedState.mutex`-et, és végrehajtja az algoritmust a nyers `baseData` felhasználásával.
4. A Zig visszaad egy új `ZigTensorModel`-t vagy egy `TensorError`-ra leképezett hibakódot.

---

## Zig implementációs részletek

### Külső függőségek és típusok

A Zig implementáció két belső modulra támaszkodik:

- **`types.zig`**: Az `Error` uniont és a `Fixed32_32` típust biztosítja.
- **`memory.zig`**: Specializált allokátor implementációkat biztosít.

### Numerikus típus-támogatás

A könyvtár elsősorban `f32`-t céloz standard tensor-műveletek esetén, de infrastruktúrát biztosít a fixpontos típusokra való kiterjesztéshez is a `types.zig` dependencián keresztül. Ez lehetővé teszi a könyvtár használatát lebegőpontos egység (FPU) nélküli környezetekben is.

| Típus | Cél |
|---|---|
| `f32` | Standard lebegőpontos adattárolás |
| `usize` | Dimenziók, stride-ok és referenciaszámok |
| `Fixed32_32` | Fixpontos aritmetika támogatás |
| `bool` | Copy-on-Write (CoW) állapot |

---

## Külső függőségek: types.zig és memory.zig

### types.zig: Hibakezelés és fixpontos aritmetika

A `types.zig` a közös típusdefiníciós réteg:

**Hibaunion:** Átfogó hibauniont biztosít:
- `InvalidShape`: Nulla dimenziókat vagy nullás méretű dimenziót tartalmazó alakzat esetén.
- `IncompatibleShapes`: Elemenkénti műveletek nem egyező dimenziójú tensorokon.
- `IndexOutOfBounds`: Ha az indextömb meghaladja a `Shape` által definiált határokat.
- `Overflow`: Stride-számítás vagy teljes méret számítása során.
- `NonInvertible`: Szinguláris mátrix esetén.

**Fixed32_32 fixpontos típus:** 64 bites fixpontos szám, 32 bit az egész rész és 32 bit a törtész számára. A `toFixed()` metódussal konvertálható `f32`-ről.

### memory.zig: Specializált allokátorok

A négy elsődleges allokátor típus:
1. **ArenaAllocator:** Tömeges allokáció, egyszerre szabadítja fel az összes memóriát.
2. **PoolAllocator:** Azonos méretű tensorok hatékony kezelése, töredezettség csökkentése.
3. **SlabAllocator:** Rögzített méretű szeletekben kezeli a memóriát, nagyon gyors allokáció.
4. **BuddyAllocator:** Kettő-hatványon alapuló memóriaosztás, változatos méretek kezelése.

**Integráció a tensor életciklussal:** Amikor egy `Tensor` inicializálódik specializált allokátorral, a `Tensor` struktúra `allocator` mezője az adott allokátor interfészére kerül beállítva. Ez biztosítja, hogy a végül meghívott `deallocate()` a memóriát a helyes háttérnek adja vissza.

---

## Szálbiztonság és párhuzamosság

### Per-tensor zárolás és a Mutex mező

Minden `Tensor` példány a Zig implementációban tartalmaz egy mutatót egy `std.Thread.Mutex`-re. Ez a mutex heap-allokált az inicializálás során, és megosztott az összes tensor-nézet között, amelyek ugyanarra az adatpufferre mutatnak.

A design per-tensor zárolást alkalmaz (nem globális zárat), hogy maximalizálja az áteresztőképességet a független tensor-műveletek esetén. A mutex specifikusan védi a `cow` (Copy-on-Write) jelzőt és a megosztott, csak-olvasható állapotból a privát, írható állapotba való átmenetet.

### Atomi referenciaszámlálás

A könyvtár atomi referenciaszámlálási mintát alkalmaz a memória életciklusának kezeléséhez:

**Retain és megosztás:**
1. Atomi növelés: `@atomicRmw`-t használ `.Add` és `acq_rel` sorrenddel.
2. Megosztottá jelölés: azonnal meghívja a `markShared()`-t.

**Release és deallokálás:**
1. Atomi csökkentés: `@atomicRmw`-t használ `.Sub` és `acq_rel` sorrenddel.
2. Feltételes takarítás: Ha az előző szám 1 volt, `deallocate()` hívódik meg. Egyébként csak a helyi `Shape` metaadatok takarítódnak.

### CoW átmenetek

**`markShared()`:** A `cow` jelzőt `true`-ra állítja. Ezután bármely módosítási kísérletnek előbb privát másolatot kell létrehoznia.

**`ensureWritable()`:** Minden módosítás előtt meghívódik:
- Lezárja a mutexet.
- Ellenőrzi a `cow` jelzőt.
- Ha `cow` igaz: új puffert allokál, átmásolja az adatokat, `cow`-t `false`-ra állítja.
- Ez biztosítja, hogy a módosítás csak az aktuális tensor példányt érintse.

### Párhuzamossági garanciák

| Művelet típusa | Szálbiztonsági garancia | Implementációs mechanizmus |
|---|---|---|
| **Párhuzamos olvasások** | Biztonságos | Több szál egyszerre olvashat ugyanabból a `base_data`-ból, amíg `cow` igaz |
| **Olvasás írás közben** | Biztonságos | Az író szál `ensureWritable`-t hív, ami új pufferbe mozgatja az írót |
| **Párhuzamos írások** | Biztonságos | A mutex sorba rendezi az `ensureWritable` ellenőrzést |
| **Metaadat-változások** | Lokális | Az olyan műveletek, mint `reshape` vagy `view`, új `Tensor` struktúrákat hoznak létre |

### Tervezési kompromisszumok

1. **Per-tensor mutex overheadje:** Minden tensor egy mutexre mutató pointert hordoz (kb. 8-16 bájt per handle), de megakadályozza a globális zárolási versenyhelyzetet.
2. **Heap-allokáció szinkronizációs primitívekhez:** A `refcount`, `cow` jelző és `mutex` mind heap-allokáltak, hogy a "nézetek" (szeletelés útján létrehozott tensorok) a szinkronizációs állapotra mutathassanak, még akkor is, ha az eredeti `Tensor` struktúra mozgatódott vagy megsemmisült.
3. **Acquire/Release szemantika:** Az atomi műveletek `.acq_rel` sorrendjének használata biztosítja, hogy az egyik szál által végzett memóriaírások (például adatok inicializálása) láthatóak legyenek egy másik szál számára, amely az aktualizált referenciaszámot észleli.

---

## Szójegyzék

### Alapfogalmak

**Shape és Stride-ok:** A tensor alapvető geometriája. A `Shape` meghatározza, hogyan képezhető le egy többdimenziós tömb egy lineáris memóriablokkra.
- **Dimenziók (dims):** Az egyes tengelyek méretét reprezentáló egészek listája.
- **Stride-ok:** Egészek listája, amely az adott tengely mentén egy egységnyi lépéshez szükséges lineáris adattömbben megtett lépések számát jelöli.
- **Sor-főrend (Row-Major):** Az alapértelmezett elrendezés, ahol az utolsó dimenzió folytonos a memóriában.

**Referenciaszámlálás (RefCount):** Számláló, amely nyomon követi, hogy hány `Tensor` objektum hivatkozik ugyanarra az adatpufferre.

**CowState / cow:** Boolean jelző, amely jelzi, hogy a tensor adatai megosztottak-e. Ha igaz, bármely módosító műveletnek előbb materializálnia kell egy privát másolatot.

**ensureWritable:** A belső mechanizmus, amely ellenőrzi a `cow` jelzőt, és mély másolatot végez, ha a puffer megosztott.

### Technikai fogalmak

**TResult:** Specializált `Except` monad a Lean implementációban, amelyet hibák kezelésére használnak kivételek dobása nélkül.

**Broadcasting:** Az a folyamat, amellyel eltérő alakzatú tensorok kompatibilissé válnak elemenkénti műveletekhez. A könyvtár NumPy-stílusú broadcasting-szabályokat követ: a dimenziók jobbról balra hasonlítódnak össze.

**Flat Index (lapos index):** A többdimenziós koordináták lineáris `flatIndex`-re való leképezése az indexek és stride-ok skaláris szorzatával: $\sum (indices_i \times strides_i)$.

**FFI (Foreign Function Interface):** Külföldi funkció-interfész – a mechanizmus, amelyen keresztül a Lean és Zig kód kommunikál egymással, C-kompatibilis struktúrákon keresztül.

**LCG (Linear Congruential Generator):** A könyvtár által a véletlen inicializáláshoz (`randomUniform`, `randomNormal`) használt determinisztikus pszeudo-véletlen számmgenerátor.

### Hibatípusok összefoglalója

| Hiba | Leírás |
|---|---|
| `shapeMismatch` | Két tensor inkompatibilis alakzata egy műveletben (például `add`) |
| `invalidShape` | Nulla dimenziójú vagy túlcsorduló alakzat |
| `outOfBounds` | Index meghaladja az alakzat dimenzióját `get` vagy `set` esetén |
| `notConverged` | Iteratív algoritmus (SVD, spectralNorm) nem érte el a tűréshatárt |
| `singularMatrix` | Mátrixinverzió során, ha a determináns nulla |
| `notPositiveDefinite` | Cholesky-dekompozíció feltétele nem teljesül |
| `allocFailed` | Memória-allokálás sikertelen |

### Memória-allokátorok összefoglalója

| Allokátor | Stratégia | Elsődleges felhasználási eset |
|---|---|---|
| **ArenaAllocator** | Tömeges felszabadítás | Ideiglenes tensorok egyetlen hatókörben |
| **PoolAllocator** | Rögzített méretű blokkok | Egységes méretű tensorok (pl. rögzített kötegű következtetés) |
| **SlabAllocator** | Méretosztály-gyorsítótárazás | Töredezettség csökkentése sűrű allokáció/felszabadítás ciklusokban |
| **BuddyAllocator** | Kettő-hatványon alapuló osztás | Változatos tensor-méretek hatékony kezelése |
