surprisememory – Teljes dokumentáció (Magyar)

> Forrás: [https://deepwiki.com/kollarsandor/surprisememory](https://deepwiki.com/kollarsandor/surprisememory) > Generálva: **2026**-04-03

---

 Áttekintés

 Cél és hatókör

A SurpriseMemory repository egy intelligens memóriakezelő rendszert biztosít, amely a megtartási döntéseket az adatok újdonsága alapján hozza meg, nem csupán a hagyományos metrikák, például a hozzáférési sorrendek vagy a gyakoriság alapján. A rendszer több dimenziós „meglepetési" pontszámokat számít az eltárolt adatblokkokhoz, és ezeket a pontszámokat használja annak meghatározásához, hogy melyik blokkot tartsa meg, és melyiket távolítsa el, ha a kapacitáskorlátot elérték.

 Kettős implementációs stratégia

A SurpriseMemory egy egyedi kettős implementációs megközelítést alkalmaz: egy gyakorlati, éles üzemeltetésre szánt implementáció Zig-ben, párhuzamosan egy formális matematikai specifikációval Lean 4-ben. Ez az architektúra egyszerre biztosít valós felhasználhatóságot és matematikai korrektség-garanciákat.

 Az alapvető probléma és megoldás

A hagyományos gyorsítótár-kizárási szabályzatok (**LRU**, **LFU**, **FIFO**) kizárólag a hozzáférési minták alapján döntenek. A SurpriseMemory bevezeti a újdonságtudatos gyorsítótárazást: a meglepő vagy újszerű adatokat tartalmazó blokkok – amelyeket tartalmi hasonlóság, hash-eltérés és időbeli egyediség alapján mérnek – magasabb megtartási prioritást kapnak.

| Hagyományos gyorsítótárazás | SurpriseMemory |
|---|---|
| A legrégebben használt blokkokat ejti | A legalacsonyabb kombinált megtartási pontszámú blokkokat ejti |
| Nincs tartalomelemzés | Több dimenziós meglepetési számítás |
| Csak hozzáférési gyakoriság | Meglepetési pontszám + hozzáférési frekvencia + kor |
| Nincs deduplikáció-tudatosság | Integrálódik a tartalom-alapú tárolással |
| Nincs formális ellenőrzés | 271+ bizonyított invariáns és korrektségi tétel |

 Kulcsfontosságú adatstruktúrák

| Struktúra | Cél | Kulcsmezők |
|---|---|---|
| SurpriseMemoryManager | Központi vezérlő | storage, surprise_records, surprise_threshold, statistics, mutex |
| SurpriseMetrics | Több dimenziós újdonsági pontszám | jaccard_dissimilarity, content_hash_distance, temporal_novelty, combined_surprise |
| SurpriseRecord | Blokkonkénti metaadat | block_id, surprise_score, retention_priority, access_frequency, last_access_time, creation_time |
| SurpriseMemoryStatistics | Összesített metrikák | total_blocks, high_surprise_blocks, low_surprise_blocks, average_surprise, eviction_count |
| ContentAddressableStorage | Blokkperzisztencia réteg | Automatikus deduplikáció tartalmi hash alapján |

 A meglepetési számítási folyamat

A rendszer alapvető újítása a meglepetési számítás, amely három független metrikát kombinál az adatok újdonságának meghatározásához.

 A megtartási prioritás képlete

Amikor a kapacitás megtelik, a blokkokat egy megtartási prioritás pontszám alapján rangsorolják, amely kombinálja a meglepetést a hozzáférési mintákkal:

retention_priority = surprise_score × (
    RETENTION_BASE_WEIGHT × 1.0 +
    RETENTION_AGE_WEIGHT × (1 / (1 + age_milliseconds)) +
    RETENTION_FREQUENCY_WEIGHT × log(access_frequency)
)

ahol:
    RETENTION_BASE_WEIGHT = 0.5
    RETENTION_AGE_WEIGHT = 0.3
    RETENTION_FREQUENCY_WEIGHT = 0.2

Ez a képlet biztosítja:
- Alap prioritás (50%): A meglepő adatok eredendően magasabb értékkel bírnak
- Frissességi bónusz (30%): A nemrég elért blokkok ideiglenes védelmet kapnak
- Frekvencia bónusz (20%): A sűrűn elért blokkok idővel értéket halmoznak fel

 Menetbiztonság és párhuzamosság

A Zig implementáció szálbiztos egyidejű hozzáférést biztosít mutex-védett műveletekkel. Minden publikus metódus belépéskor megszerzi a mutexet, és defer segítségével felszabadítja azt.

 Formális ellenőrzési architektúra

A Lean implementáció matematikai garanciákat biztosít bizonyított invariánsok hierarchiáján keresztül, beleértve **271**+ tételt, amelyek garantálják a rendszer helyes működését minden lehetséges műveleten át.

 Rendszerhatárok és függőségek

A Zig implementációnak két külső függősége van: a Zig Standard Library és a chaos_core.zig (amely biztosítja a ContentAddressableStorage-t és a DataFlowAnalyzer-t). A Lean specifikáció függőségmentes és egy tiszta funkcionális modellt valósít meg.

 Teljesítményjellemzők

| Művelet | Időbeli bonyolultság | Megjegyzések |
|---|---|---|
| computeSurprise | O(1) | Legfeljebb 1000 blokkot mintavételez |
| storeWithSurprise | O(1) amortizálva | Meglepetési számítás + hash map insert |
| evictLowSurpriseBlocks(k) | O(k × n) | Részleges rendezés k legalacsonyabb prioritású blokkhoz |
| getSurpriseRecord | O(1) átlagos | HashMap keresés |
| organizeByEntanglement | O(p²) ahol p ≤ 100 | Korlátozott pár-generálás |

---

 Alapfogalmak

 Meglepetés mint újdonság

A surprise memory rendszer az adatot értékesebbnek tekinti, ha újszerű (különbözik a meglévő adatoktól), nem redundáns. A „meglepetés" az új adat számszerűsített mértéke – azt mutatja, mennyire váratlan az adat ahhoz képest, amit a rendszer már látott. A magas meglepetési értékű adatot tovább tartja meg; az alacsony meglepetési értékűt ejti ki először.

 Több dimenziós meglepetési számítás

A meglepetés nem egyetlen metrika, hanem három független dimenzió összetétele, amelyek mindegyike az újdonság egy-egy aspektusát méri:

| Dimenzió | Cél | Számítás | Tartomány |
|---|---|---|---|
| Jaccard-eltávolítás | Tartalom szintű hasonlóság | 1 - (metszet/unió) bájt-készletek | 0.0 - 1.0 |
| Tartalmi hash-távolság | Kriptográfiai eltérés | Hamming-távolság SHA256 hash-en (128 bit) | 0.0 - 1.0 |
| Időbeli újdonság | Történelmi kontextus | 1 / √(1 + blokk_szám) | 0.0 - 1.0 |
| Kombinált meglepetés | Végső pontszám | A fenti három átlaga | 0.0 - 1.0 |

 Tartalmalapú tárolás integrációja

A rendszer integrálódik a ContentAddressableStorage-zal az automatikus deduplikáláshoz. Amikor storeWithSurprise() kerül hívásra, a rendszer ellenőrzi, hogy az adat létezik-e már, és frissíti a hozzáférési számlálót ahelyett, hogy duplán tárolná.

 Kapacitáskezelés és kizárás

Amikor a tárolókapacitás megtelik, a rendszer a legalacsonyabb megtartási prioritású blokkokat ejti ki. A kizárási folyamat egy részleges rendezési algoritmust használ a jelöltek hatékony azonosításához.

 A meglepetési küszöb és osztályozás

A rendszer egy konfigurálható surprise_threshold értéket (alapértelmezett 0.3) használ a blokkok osztályozásához:

| Osztályozás | Feltétel | Hatás |
|---|---|---|
| Magas meglepetés | combined_surprise > küszöb | Növeli a high_surprise_blocks számlálót |
| Alacsony meglepetés | combined_surprise ≤ küszöb | Növeli a low_surprise_blocks számlálót, elsők a kizárásra |

Invariáns: high_surprise_blocks + low_surprise_blocks ≤ total_blocks (mindig fennáll)

---

 Meglepetési metrikák

 Áttekintés

A meglepetési metrikák három független, egyenlően súlyozott dimenziót tartalmaznak, amelyek az újdonság különböző aspektusait ragadják meg: Jaccard-eltávolítás, tartalmi hash-távolság és időbeli újdonság.

 A SurpriseMetrics struktúra

| Mező | Típus | Tartomány | Leírás |
|---|---|---|---|
| jaccard_dissimilarity | f64/Rational | [0.0, 1.0] | Bájt-szintű tartalmi hasonlóság (1.0 = teljesen különböző) |
| content_hash_distance | f64/Rational | [0.0, 1.0] | Normalizált Hamming-távolság a tartalmi hash-ek között |
| temporal_novelty | f64/Rational | [0.0, 1.0] | A teljes blokk-szám inverze (csökken ahogy nő a tároló) |
| combined_surprise | f64/Rational | [0.0, 1.0] | A három metrika átlaga |

 1. dimenzió: Jaccard-eltávolítás

Cél: A Jaccard-eltávolítás bájt-szinten méri a tartalmi hasonlóságot. Két, hasonló bájt-eloszlású adatblokk alacsony eltávolítási pontszámot kap, jelezve a redundanciát. Ez a metrika a bájtok jelenlétére működik, nem a sorrendükre.

Algoritmus: ## Legfeljebb JACCARD_SAMPLE_SIZE (1000) meglévő blokkot mintavételez ## Minden blokkhoz 256 elemű boolean tömböt készít ## Kiszámolja a metszetet és az uniót ## Visszaadja: 1 - (metszet_szám / unió_szám) minimumát

| Tulajdonság | Érték |
|---|---|
| Tartomány | [0.0, 1.0] |
| Mintaméret | 1000 bájt |
| Összehasonlítási tér | 256 dimenzió |

 2. dimenzió: Tartalmi hash-távolság

Cél: Kriptográfiai eltérések detektálása. A **SHA256** hash-eken számított Hamming-távolság segítségével méri az eltérést.

Algoritmus: ## SHA256 hash számítása az új adatból, az első HASH_SIZE (16) bájt kivétele ## Legfeljebb 1000 meglévő hash mintavételezése ## XOR minden egyes bájtpáron, majd set-bitek számlálása (popCount) ## Normalizálás: hamming_távolság / HASH_BITS (128)

Matematikai tulajdonságok (Lean-ben bizonyítva):

| Tulajdonság | Tétel |
|---|---|
| Szimmetria | computeHashDistance_symmetric |
| Azonosság | computeHashDistance_self_zero |
| Háromszög-egyenlőtlenség | computeHashDistance_triangle_rational |
| Nem-negativitás | computeHashDistance_nonneg |
| Korlátosság | computeHashDistance_bounded_num |

 3. dimenzió: Időbeli újdonság

Cél: Az időbeli kontextus figyelembevétele – a rendszer „fiatalkorában" (kevés blokk) érkező adatok eleve újszerűbbek.

Képlet:

temporal_novelty = 1 / (1 + sqrt(block_count))

| Blokk-szám | Időbeli újdonság |
|---|---|
| 0 | 1.000 |
| 1 | 0.707 |
| 9 | 0.500 |
| 99 | 0.091 |
| 999 | 0.031 |

 Kombinált meglepetési pontszám

combined_surprise = (jaccard_dissimilarity + content_hash_distance + temporal_novelty) / 3.0

Az egyenlő súlyozás biztosítja, hogy egyik dimenzió se domináljon.

 Számítási bonyolultság

| Metrika | Időbeli bonyolultság | Térbeli bonyolultság |
|---|---|---|
| Jaccard | O(1000 × 256) = O(1) | O(256) |
| Hash-távolság | O(1000 × 16) = O(1) | O(16) |
| Időbeli | O(1) | O(1) |
| Összesen | O(1) | O(1000) |

 Állandók referenciája

| Állandó | Érték | Cél |
|---|---|---|
| JACCARD_SAMPLE_SIZE | 1000 | Maximum mintavételezett blokkok száma |
| HASH_SIZE | 16 | Hash mérete bájtban (128 bit) |
| HASH_BITS | 128 | Hash-távolság normalizáláshoz |
| MAX_INPUT_SIZE | 100 MB | Maximum elfogadott adatméret |
| DEFAULT_SURPRISE_THRESHOLD | 0.3 | Alapértelmezett küszöb |

---

 Megtartási prioritás

 Képlet és összetevők

A megtartási prioritás három tényező súlyozott kombinációja:

retention_priority = surprise_score × (base_weight + age_component + frequency_component)

ahol:
    base_weight         = 0.5
    age_component       = 0.3 × age_factor
    frequency_component = 0.2 × log(access_frequency)
    age_factor          = 1.0 / (1.0 + time_since_last_access_ms)

 Súlyelosztás

| Állandó | Érték | Arány | Cél |
|---|---|---|---|
| RETENTION_BASE_WEIGHT | 0.5 | 50% | Biztosítja a meglepetési pontszám dominanciáját |
| RETENTION_AGE_WEIGHT | 0.3 | 30% | Jutalmazza a nemrég elért blokkokat |
| RETENTION_FREQUENCY_WEIGHT | 0.2 | 20% | Jutalmazza a sűrűn elért blokkokat |

 Kor-tényező: Frissességi számítás

age_factor = 1.0 / (1.0 + age_ms)

- Azonnali hozzáférés (age_ms = 0): age_factor = 1.0
- 1 másodperces kor: age_factor ≈ 0.5
- Nagyon régi blokkok: age_factor közelít a nullához

 Frekvencia-tényező: logaritmikus skálázás

| Hozzáférési frekvencia | log(frekvencia) | Frekvencia-hozzájárulás (0.2 × log) |
|---|---|---|
| 1 (kezdeti) | 0.0 | 0.0 |
| 2 | 0.693 | 0.139 |
| 10 | 2.303 | 0.461 |
| 100 | 4.605 | 0.921 |

 Dinamikus prioritás-frissítések

A megtartási prioritás nem statikus – változik a blokkok elérésekor és az idő múlásával.

- Hozzáférésen frissítve: Az access_frequency nő, a last_access_time az aktuális időre frissül
- Kizárás előtt frissítve: Minden rekord prioritása frissítésre kerül az igazságos összehasonlításhoz

 Formális tulajdonságok (Lean-ben bizonyítva)

- access_frequency szigorúan monoton növekvő
- surprise_score és creation_time nem változik inicializálás után
- Az invariáns garantálja: access_frequency ≥ 1 és creation_time ≤ last_access_time

 Példák a prioritás alakulására

Inicializáláskor (t=0, surprise=0.8):

age_factor = 1.0 frequency_factor = log(1) = 0.0 weight_sum = 0.5 + 0.3×1.0 + 0.2×0.0 = 0.8 retention_priority = 0.8 × 0.8 = 0.64

10 hozzáférés után, azonnali eléréskor:

frequency_factor = log(10) ≈ 2.**303** weight_sum = 0.5 + 0.3×1.0 + 0.2×2.**303** = 1.**261** retention_priority = 0.8 × 1.**261** ≈ 1.**009**

1 perccel az utolsó hozzáférés után:

age_ms = **55000** age_factor = 1 / (1 + **55000**) ≈ 0.**0000182** retention_priority ≈ 0.**769** (lecsökkent 1.**009**-ről)

---

 Tartalomalapú tárolás

 Alaparchitektúra

A tartalomalapú tárolás (**CAS**) az a perzisztencia réteg, amely blokktárolást, automatikus deduplikálást és tartalom-alapú azonosítást biztosít. Az adatblokkok tartalmukhoz kapcsolódó kriptográfiai hash-szel kerülnek azonosításra, így az azonos tartalom mindig ugyanahhoz az azonosítóhoz vezet.

 Tartalomalapú azonosítás

| Implementáció | Hash-algoritmus | Kimeneti méret | BlockId kinyerés |
|---|---|---|---|
| Zig | SHA-256 | 32 bájt | Első 16 bájt |
| Lean | FNV-szerű hash | Levezetett | 16 bájton elosztva |

 Tárolási műveletek

| Művelet | Zig szignatúra | Lean szignatúra | Cél |
|---|---|---|---|
| store | store(data, core) → !BlockId | store(data) → (StorageState, BlockId) | Adat tárolása, tartalom-hash visszaadása |
| retrieveByContent | retrieveByContent(data) → ?BlockId | findByContent(data) → Option BlockId | BlockId keresése tartalom alapján |
| containsBlock | containsBlock(bid) → bool | containsBlock(bid) → Bool | Blokk létezésének ellenőrzése |
| removeBlock | removeBlock(bid) | removeBlock(bid) → StorageState | Blokk törlése |

 Automatikus deduplikálás

A tartalomalapú tárolás garantálja, hogy az azonos adat csak egyszer kerül tárolásra. Ha a store() hívásra kerül már létező tartalommal, a meglévő BlockId-t adja vissza.

 Lean: Lista-alapú tárolás

structure StorageState where
    blocks : List StorageBlock
    capacity : Nat

A műveletek új StorageState értékeket adnak vissza ahelyett, hogy helyben módosítanák az állapotot – ez megőrzi az immutabilitást a formális ellenőrzés érdekében.

 Formális tulajdonságok (Lean-ben bizonyítva)

| Tétel | Állítás |
|---|---|
| storageState_empty_count | Üres tárolóban nulla blokk |
| storageState_store_count | A tárolás növeli a számlálót 1-gyel |
| computeContentHash_deterministic | A hash determinisztikus |
| storage_remove_decreases_count | Eltávolítás nem növeli a számlálót |

 Összefonódás (Entanglement)

A tartalomalapú tárolás támogat entangleBlocks() műveletet, amely kapcsolatokat hoz létre a magas meglepetési értékű blokkok között. Ez az összefonódás a tároló háttérrendszer általi optimalizáláshoz használható.

---

 Kizárási stratégia

 Áttekintés

A kizárás egy kapacitáskezelő mechanizmus, amely eltávolítja a legalacsonyabb megtartási prioritású blokkokat, amikor az aktuális tárolási szám meghaladja a célkapacitást. A rendszer részleges rendezési algoritmust használ a k legalacsonyabb prioritású blokk hatékony azonosításához.

 A kizárási folyamat

## Kapacitás-ellenőrzés: Ha jelenlegi_méret ≤ célkapacitás, azonnal visszatér 0 kizárással

## Jelöltlista összeállítása: CandidateItem lista készítése az összes rekord aktuális prioritásával ## Részleges rendezés: partialSort(jelöltek, k) hívása a k legalacsonyabb prioritású blokk megtalálásához ## Eltávolítási ciklus: Minden jelölt eltávolítása a tárolóból és a rekordokból ## Szám visszaadása: A ténylegesen kizárt blokkok számának visszaadása

 A részleges rendezési algoritmus

Kiválasztás-rendezés k iterációra:

Kezdeti állapot:    [5.0, 1.0, 3.0, 2.0, 4.0] i=0 után:           [1.0, 5.0, 3.0, 2.0, 4.0]  ← minimum helyre kerül i=1 után:           [1.0, 2.0, 3.0, 5.0, 4.0]  ← második minimum i=2 után:           [1.0, 2.0, 3.0, 5.0, 4.0]  ← harmadik minimum Kizárt: indexek [0, 1, 2] → prioritások [1.0, 2.0, 3.0]

| Tulajdonság | Érték |
|---|---|
| Időbeli bonyolultság | O(k×n) |
| Térbeli bonyolultság | O(1) |
| Stabilitás | Nem stabil |

 Kizárás biztonsági garanciák (Lean-ben bizonyítva)

| Tétel | Garancia |
|---|---|
| evictLowSurprise_noop_under_capacity | Kapacitás alatt nincs kizárás |
| eviction_never_removes_max_priority | A maximális prioritású blokk sosem kerül kizárásra |
| evictLowSurprise_zero_evictions_under_capacity | Kapacitás alatt 0 kizárás |

 Statisztikák frissítése kizáráskor

| Mező | Módosítás |
|---|---|
| total_blocks | 1-gyel csökkentve |
| high_surprise_blocks | Csökkentve (ha pontszám > küszöb) |
| low_surprise_blocks | Csökkentve (ha pontszám ≤ küszöb) |
| total_surprise_sum | surprise_score-szal csökkentve |
| evictions_due_to_low_surprise | 1-gyel növelve |

 Teljesítményelemzés

| Művelet | Bonyolultság |
|---|---|
| Teljes kizárás | O(k×n + n) |
| Jelöltek összeállítása | O(n) |
| Prioritások frissítése | O(n) |
| Részleges rendezés | O(k×n) |
| Blokkok eltávolítása | O(k×log n) |

Részleges rendezés előnye: n=10 **000**, k=1 **000** esetén ~ **10M** vs. teljes rendezésnél ~**130K** - a részleges rendezés hatékonyabb, ha k << n.

---

 Rendszerarchitektúra

 Kettős implementációs architektúra

A SurpriseMemory kettős implementációs stratégiát alkalmaz: a Zig implementáció (SurpriseMemoryManager) mutálható állapotot biztosít hash map-ekkel és mutex-szinkronizációval, a Lean implementáció (ManagerState) pedig tiszta funkcionális adatstruktúrákat immutábilis listákkal.

 Komponens-architektúra

Az öt fő komponens-réteg:

- Manager Core (SurpriseMemoryManager/ManagerState): Koordinálja az összes műveletet
- Metaadat-réteg: Párhuzamos adatstruktúrák – surprise_records és statistics
- Meglepetési motor: Több dimenziós újdonság számítása
- Irányvonal-motor: Küszöb-konfiguráció, megtartási prioritás, kizárási jelölt-kiválasztás
- Tárolási háttérrendszer: ContentAddressableStorage és DataFlowAnalyzer integrációja

 Adatfolyam-architektúra

Tárolási műveleti folyamat (storeWithSurprise):
## Mutex megszerzése
## Tartalom ellenőrzése: storage.retrieveByContent(data)
## Meglévő blokk esetén: hozzáférés frissítése
4. Új blokk esetén: computeSurprise(data) → tárolás → SurpriseRecord.init → statisztika frissítése
## Mutex felszabadítása

Kizárási műveleti folyamat (evictLowSurpriseBlocks): ## Kapacitás-ellenőrzés ## Jelöltlista összeállítása ## Részleges rendezés k legalacsonyabb prioritású blokkra ## Eltávolítási ciklus (storage + records + statistics) ## Kizárt darabszám visszaadása

 Menetbiztonság és párhuzamossági modell

A Zig implementáció szálbiztos, míg a Lean egyetlen szálú tiszta funkcionális modellt alkalmaz. Minden publikus metódus követi a mintát: zig self.mutex.lock(); defer self.mutex.unlock(); // ... kritikus szekció ...

 Konfiguráció és állandók

| Állandó | Érték | Cél |
|---|---|---|
| HASH_SIZE | 16 bájt | BlockId mérete |
| HASH_BITS | 128 bit | Hash-távolság normalizálása |
| MAX_INPUT_SIZE | 100 MB | Maximum blokk-adatméret |
| JACCARD_SAMPLE_SIZE | 1000 blokk | Maximum mintavételezés hasonlósághoz |
| MAX_ENTANGLEMENT_PAIRS | 100 blokk | Maximális összefonodási párok |
| DEFAULT_SURPRISE_THRESHOLD | 0.3 | Alapértelmezett küszöb |
| RETENTION_BASE_WEIGHT | 0.5 | Meglepetési pontszám súlya |
| RETENTION_AGE_WEIGHT | 0.3 | Frissességi súly |
| RETENTION_FREQUENCY_WEIGHT | 0.2 | Frekvencia-súly |

---

 Komponens-áttekintés

 SurpriseMemoryManager (Zig) / ManagerState (Lean)

Zig mezők:

| Mező | Típus | Felelősség |
|---|---|---|
| storage | ContentAddressableStorage | Tartalomalapú blokkfárolás mutatója |
| flow_analyzer | DataFlowAnalyzer | Adatfolyam-elemző mutatója |
| surprise_records | HashMap(...) | Blokk ID-k leképezése SurpriseRecord-okra |
| surprise_threshold | f64 | Osztályozási határérték (0.0-1.0) |
| statistics | SurpriseMemoryStatistics | Összesített metrikák nyomkövetője |
| allocator | Allocator | Memória-foglaló |
| mutex | Mutex | Szál-szinkronizáló |
| owns_storage | bool | Jelzőbit a tárolótulajdonláshoz |
| owns_analyzer | bool | Jelzőbit az elemzőtulajdonláshoz |

Lean mezők:

| Mező | Típus | Felelősség |
|---|---|---|
| storage | StorageState | Tiszta funkcionális tárolóstruktúra |
| surprise_records | List (BlockId × SurpriseRecord) | Párosítási lista |
| surprise_threshold | Rational | Osztályozási határérték racionális számként |
| statistics | SurpriseMemoryStatistics | Összesített metrikák |

 SurpriseRecord

| Mező | Frissítési viselkedés |
|---|---|
| block_id | Immutábilis inicializálás után |
| surprise_score | Immutábilis – egyszer kerül beállításra tároláskor |
| creation_time | Immutábilis – soha nem változik |
| last_access_time | Mutábilis – hozzáférésenként frissítve |
| retention_priority | Mutábilis – hozzáféréskor és frissítéskor újraszámított |
| access_frequency | Mutábilis – hozzáférésenként növekvő |

 SurpriseMemoryStatistics

| Mező | Típus | Cél | Invariáns |
|---|---|---|---|
| total_blocks | usize | Összes tárolt blokk | = high + low |
| high_surprise_blocks | usize | Küszöb feletti blokkok | ≤ total_blocks |
| low_surprise_blocks | usize | Küszöb alatti blokkok | ≤ total_blocks |
| average_surprise | f64 | Átlagos meglepetés | total_sum / total |
| evictions_due_to_low_surprise | usize | Kumulatív kizárások | Monoton növő |

---

 Meglepetési számítási folyamat

 A folyamat architektúrája

A meglepetési számítási folyamat átalakítja a nyers bemeneti adatot egy több dimenziós újdonsági pontszámmá (SurpriseMetrics).

 Bemeneti érvényesítés

| Ellenőrzés | Küszöb | Hiba |
|---|---|---|
| Méretkorlát | MAX_INPUT_SIZE (100 MB) | error.InputTooLarge |
| NaN ellenőrzés | Float konverzió érvényessége | error.InvalidInput |
| Üres tároló | block_count == 0 | Korai visszatérés max. meglepetéssel |

 Blokkfájl mintavételezési stratégia

A számítási bonyolultság O(1)-en tartásához a folyamat legfeljebb JACCARD_SAMPLE_SIZE (**1000**) blokkot mintavételez összehasonlításra.

 A folyamat végrehajtási lépései

| Lépés | Művelet |
|---|---|
| 1 | Bemeneti méret érvényesítése |
| 2 | Üres tároló ellenőrzése |
| 3 | Tartalmi hash számítása |
| 4 | Minimális távolságok inicializálása |
| 5 | Blokk ID-k összegyűjtése és rendezése |
| 6 | Mintavételezett blokkok iterálása |
| 7 | Jaccard-távolság számítása |
| 8 | Hash-távolság számítása |
| 9 | Minimumok nyomkövetése |
| 10 | Időbeli újdonság számítása |
| 11 | Metrikák kombinálása |
| 12 | SurpriseMetrics visszaadása |

 Zig vs. Lean különbségek

| Szempont | Zig implementáció | Lean implementáció |
|---|---|---|
| Hash-funkció | SHA-256 (kriptográfiai) | FNV-szerű (egyszerű) |
| Numerikus típus | f64 (lebegőpontos) | Rational (pontos) |
| Cél | Éles teljesítmény | Formális ellenőrzés |

---

 Az adatok életciklusa

 Állapotgép-áttekintés

Minden adatblokk a rendszerben meghatározott állapotsorozaton halad át: Tárolt → Aktív → Kizárásra Jelölt / Összefonódott → Kizárt

 Kezdeti tárolás és értékelés

A storeWithSurprise() az összes adat belépési pontja, mind az új blokkok, mind a meglévő blokkok eléréséhez. Három eset lehetséges: ## Azonos tartalom + meglévő rekord: hozzáférés frissítése ## Azonos tartalom + nincs rekord: új rekord létrehozása számított meglepetéssel ## Teljesen új tartalom: meglepetés számítása, tárolás, rekord és statisztika frissítése

 Aktív állapot kezelése

A tárolt blokkok aktív állapotba kerülnek, ahol a megtartási prioritásuk dinamikusan frissül a hozzáférési minták alapján.

Hozzáférési minta bizonyítékok:

| Tétel | Garancia |
|---|---|
| surpriseRecord_recordAccess_frequency | access_frequency pontosan 1-gyel nő hozzáférésenként |
| surpriseRecord_recordAccess_preserves_score | surprise_score nem változik |
| surpriseRecord_recordAccess_preserves_block_id | block_id immutábilis |

 Az összefonódott állapot

A magas meglepetési értékű blokkok Összefonódott állapotba kerülhetnek, ahol párosítják őket más magas meglepetési értékű blokkokkal a tárolási háttérrendszer általi optimalizáláshoz. Az összefonódás nem befolyásolja a megtartási prioritás számítást; az összefonódott blokkok is kizárhatók, ha alacsony a prioritásuk.

 A terminális Kizárt állapot

Miután egy blokk Kizárt állapotba kerül, ez terminális – a blokk nem állítható vissza, és nem mehet át más állapotba.

Kizárás utáni műveletek: ## Tároló eltávolítás: storage.removeBlock(block_id) ## Rekord eltávolítás: surprise_records.remove(block_id) ## Statisztika frissítés: statistics.removeBlock() és evictions_due_to_low_surprise++

 Életciklus statisztika nyomkövetés

| Mező | Mikor frissül | Cél |
|---|---|---|
| total_blocks | Tároláskor, kizáráskor | Aktuális összblokk-szám |
| novel_block_allocations | Tároláskor (új + magas meglepetés) | Újszerű blokkok száma |
| evictions_due_to_low_surprise | Kizáráskor | Összes kizárás |

---

 Tárolás-integráció

 Integrációs architektúra

A SurpriseMemoryManager nem valósítja meg a saját tárolási rétegét. Ehelyett két külső komponenssel integrálódik a chaos_core modulból:
- ContentAddressableStorage: Alapvető blokkfárolási képességek
- DataFlowAnalyzer: Adatfolyam-elemzési képességek

 Hozzáférési minták

| Hozzáférési minta | Metódus | Cél |
|---|---|---|
| Közvetlen mező-hozzáférés | self.storage.storage | Iterátor-hozzáférés, számlálás |
| Metódus-delegálás | self.storage.store(), stb. | Tárolási műveletek |

 Tulajdonlási minták

| Minta | Függvény | owns_storage | owns_analyzer | Takarítási felelősség |
|---|---|---|---|---|
| Külső tulajdon | init() | false | false | Hívó köteles |
| Belső tulajdon | initWithOwnership() | Konfigurálható | Konfigurálható | Manager hívja deinit()-et |

---

 Zig implementáció

 Implementációs áttekintés

A Zig implementáció a surprise_memory.zig fájlban található, és egy szálbiztos, éles üzemeltetésre alkalmas memóriakezelő rendszert biztosít, amely a SurpriseMemoryManager struct köré épül.

 Kulcsállandók

| Állandó | Érték | Cél |
|---|---|---|
| RETENTION_AGE_WEIGHT | 0.3 | Frissességi súly |
| RETENTION_FREQUENCY_WEIGHT | 0.2 | Hozzáférési frekvencia súlya |
| RETENTION_BASE_WEIGHT | 0.5 | Meglepetési pontszám alapsúlya |
| HASH_SIZE | 16 | Blokkazonosítók mérete (128 bit) |
| MAX_INPUT_SIZE | 100 MB | Maximum megengedett adatblokk-méret |
| JACCARD_SAMPLE_SIZE | 1000 | Maximum mintavételezett blokkok száma |
| MAX_ENTANGLEMENT_PAIRS | 100 | Maximum magas-meglepetési blokkok az összefonódáshoz |
| DEFAULT_SURPRISE_THRESHOLD | 0.3 | Alapértelmezett küszöb |

 A meglepetési számítási folyamat

A computeSurprise metódus a mag újdonság-detektálási algoritmust valósítja meg. Legfeljebb **1000** meglévő blokkot mintavételez a számítási bonyolultság O(**1000**)-en tartásához.

Jaccard-távolság számítás: Bájt-jelenlét készleteket használ, amelyek egyensúlyt teremtenek a tartalmi különbségekre való érzékenység és a számítási hatékonyság között.

 Tesztelési infrastruktúra

| Teszt neve | Lefedettség |
|---|---|
| surprise_memory_basic | Végponttól végpontig terjedő manager-használat |
| surprise_metrics_validation | Metrika-korlátolási viselkedés |
| surprise_record_retention | Megtartási prioritás-frissítések |
| statistics_incremental_update | Statisztika-nyomkövetés helyessége |
| hash_distance_calculation | Hash-távolság metrikai tulajdonságai |
| partial_sort_correctness | Részleges rendezési algoritmus validációja |

---

 SurpriseMemoryManager

 Cél és felelősségek

A SurpriseMemoryManager struct a Zig implementáció central koordinátora, amely kezeli az integrációt a tartalomalapú tárolás, a meglepetési számítás, a rekord-nyomkövetés és a kapacitáskezelés között.

 Inicializálás

init(allocator, storage, analyzer): Nem-tulajdonló hivatkozásokkal inicializál. A hívó felelős a storage és analyzer deiniializálásáért.

initWithOwnership(allocator, storage, analyzer, owns_storage, owns_analyzer): Konfigurálható tulajdonlással inicializál. Ha owns_storage = true, a manager meghívja a storage.deinit()-et a saját takarításakor.

 Tulajdonlási forgatókönyvek

| Forgatókönyv | owns_storage | owns_analyzer | Felhasználási eset |
|---|---|---|---|
| Nem-tulajdonló | false | false | Megosztott komponensek |
| Tároló-tulajdonló | true | false | Manager vezérli a tároló életciklusát |
| Teljesen-tulajdonló | true | true | Manager minden komponensét tisztítja |

 Kapcsolat a Lean specifikációval

| Szempont | Zig implementáció | Lean specifikáció |
|---|---|---|
| Név | SurpriseMemoryManager | ManagerState |
| Mutáció | Mutábilis struct metódusokkal | Tiszta funkcionális műveletek |
| Menetbiztonság | Mutex-védett | Nem alkalmazható |
| HashMap | std.HashMap egyedi kontextussal | List (BlockId × SurpriseRecord) |

---

 Menetbiztonság és párhuzamosság

 Mutex-alapú szinkronizáció

A SurpriseMemoryManager egyetlen std.Thread.Mutex-et használ az összes mutábilis állapothoz. Ez a durva szemcsézettségű zárolási stratégia biztosítja, hogy a megosztott adatokon végzett összes művelet szerializált legyen.

 Zárolás-megszerzési minta

zig self.mutex.lock(); defer self.mutex.unlock(); // ... kritikus szekció ...

Ez a minta biztosítja, hogy a mutex mindig felszabadul a függvény kilépésekor, függetlenül a kilépési útvonaltól.

 Párhuzamos hozzáférési minták

| Művelet 1 | Művelet 2 | Párhuzamos? |
|---|---|---|
| storeWithSurprise | storeWithSurprise | ❌ Szerializált |
| storeWithSurprise | evictLowSurpriseBlocks | ❌ Szerializált |
| getSurpriseRecord | getSurpriseRecord | ❌ Szerializált |
| getStatistics | getStatistics | ❌ Szerializált |

 Zárolási versengési forgatókönyvek

A leghosszabb kritikus szekciók:
1. evictLowSurpriseBlocks: O(k×n) részleges rendezés
2. organizeByEntanglement: O(n²) páros összehasonlítás
3. storeWithSurprise: O(**1000**) mintaalapú meglepetési számítás

 Nem-újrabelépős dizájn

Az std.Thread.Mutex nem újrabelépős. A jelenlegi dizájn elkerüli ezt azzal, hogy:
- A privát metódusok nem zárolnak; feltételezik, hogy a hívó tartja a zárat
- Nincsenek visszahívási mechanizmusok
- Nincsenek külső hívások, amelyek visszahívhatnák a managert

---

 Publikus **API** referencia

 Inicializálás és életciklus

| Függvény | Visszatérési értéke | Leírás |
|---|---|---|
| init(allocator, storage, analyzer) | SurpriseMemoryManager | Inicializálás tulajdon nélkül |
| initWithOwnership(...) | SurpriseMemoryManager | Konfigurálható tulajdonlású inicializálás |
| deinit() | void | Manager és opcionálisan a függőségek deiniializálása |

 Fő műveletek

storeWithSurprise(data, preferred_core) → ![HASH_SIZE]u8
- Adatblokkot tárol automatikus meglepetési számítással és deduplikálással
- Hibák: error.InputTooLarge (>**100MB**), tárolási hibák

computeSurprise(new_data) → !SurpriseMetrics
- Meglepetési metrikákat számít anélkül, hogy tárolná az adatot
- Hibák: error.InputTooLarge, error.InvalidInput

evictLowSurpriseBlocks(target_capacity) → !usize
- Kizárja a legalacsonyabb megtartási prioritású blokkokat a célkapacitás eléréséig
- Visszatér a ténylegesen kizárt blokkok számával

 Lekérdezési műveletek

| Függvény | Visszatérési értéke | Leírás |
|---|---|---|
| getStatistics() | SurpriseMemoryStatistics | Aktuális rendszerstatisztikák |
| getSurpriseRecord(block_id) | ?SurpriseRecord | Blokk metaadat-rekordja |
| containsRecord(block_id) | bool | Rekord létezésének ellenőrzése |
| getRecordCount() | usize | Nyomkövetett rekordok száma |

 Konfigurációs műveletek

| Függvény | Leírás |
|---|---|
| setSurpriseThreshold(threshold) | Küszöb frissítése és meglévő blokkok újraosztályozása |
| getSurpriseThreshold() | Aktuális küszöb lekérdezése |

 Karbantartási műveletek

organizeByEntanglement() → !usize
- Összefonódott párokat hoz létre a magas meglepetési értékű blokkokból
- Visszaadja a létrehozott párok számát

 Hibaesetek

| Függvény | Hiba | Feltétel |
|---|---|---|
| storeWithSurprise | error.InputTooLarge | data.len > 100MB |
| computeSurprise | error.InvalidInput | NaN detektálva |
| evictLowSurpriseBlocks | error.OutOfMemory | Allokációs hiba |

---

 Integrációs útmutató

 Előfeltételek

A SurpriseMemoryManager integrálása előtt az alkalmazásnak hozzáféréssel kell rendelkeznie a következő függőségekhez a chaos_core.zig-ből:
- ContentAddressableStorage: Blokkperzisztencia és deduplikáció
- DataFlowAnalyzer: Adatfolyam-elemzési képességek
- MemoryBlock: Blokkadatstruktúra
- BlockIdContext: Hash map kontextus a blokk ID-khez

 Tulajdonlási döntési útmutató

## Manager mindkettőt tulajdonolja (true, true): A manager az egyetlen felhasználó mindkét függőségből

## Alkalmazás mindkettőt tulajdonolja (false, false): A tároló vagy elemző több manager vagy más alrendszer között oszlik meg
## Vegyes tulajdonlás: Ritka, de lehetséges
4. Életciklus szabály: A tulajdonosnak tovább kell élnie, mint az összes felhasználónak

 Menetbiztonság szempontjai

| Garancia | Mechanizmus | Hatókör |
|---|---|---|
| Kizárás | std.Thread.Mutex | Minden publikus metódus |
| Rekord-konzisztencia | Zárolt olvasás/írás | Műveleti atomitás |
| Statisztika-konzisztencia | Zárolt frissítések | Összesített metrikák |

 Integrációs ellenőrzőlista

- Függőségek megfelelően inicializálva
- Tulajdonlási modell egyértelműen meghatározva
- Hibakezelés lefedi az összes esetett
- Kapacitáskezelési stratégia implementálva
- Statisztika-monitorozás helyen van
- Takarítási sorrend helyes
- Bemenet-validálás megakadályozza a >**100MB** adatokat

---

 Adatstruktúrák

 SurpriseMetrics

| Mező | Típus | Tartomány | Leírás |
|---|---|---|---|
| jaccard_dissimilarity | f64 | [0.0, 1.0] | Bájt-szintű tartalmi hasonlóság |
| content_hash_distance | f64 | [0.0, 1.0] | Normalizált Hamming-távolság |
| temporal_novelty | f64 | [0.0, 1.0] | Időbeli frissességi metrika |
| combined_surprise | f64 | [0.0, 1.0] | A három metrika átlaga |

Metódusok:
- init(jaccard, hash_dist, temporal): Konstruktor, amely [0.0, 1.0]-ra korlátoz és számítja a kombinált pontszámot
- exceedsThreshold(threshold): true, ha combined_surprise > threshold

 SurpriseRecord

| Mező | Típus | Leírás |
|---|---|---|
| block_id | [HASH_SIZE]u8 | Tartalom-hash azonosító (16 bájt) |
| surprise_score | f64 | Immutábilis kezdeti meglepetési pontszám |
| creation_time | i128 | Nanomásodperces timestamp |
| last_access_time | i128 | Legutóbbi hozzáférés timestampje |
| retention_priority | f64 | Dinamikusan számított kizárási prioritás |
| access_frequency | usize | Összes hozzáférés száma |

 CandidateItem

Belső struktúra a kizárási folyamat során:

| Mező | Típus | Leírás |
|---|---|---|
| block_id | [HASH_SIZE]u8 | Potenciálisan kizárandó blokk azonosítója |
| priority | f64 | Gyorsítótárazott megtartási prioritás |

 Memóriakiosztás blokkonként

SurpriseRecord = {
    block_id: [16]u8        = 16 bájt
    surprise_score: f64     =  8 bájt
    creation_time: i128     = 16 bájt
    last_access_time: i128  = 16 bájt
    retention_priority: f64 =  8 bájt
    access_frequency: usize =  8 bájt
    ──────────────────────────────────
    Összesen/rekord         = 72 bájt
}
HashMap overhead-del:    ~**144** bájt/blokk

---

 Lean specifikáció

 Cél és hatókör

A Lean 4 specifikáció matematikailag ellenőrzi a surprise memory rendszer helyességét. Ez egy tiszta funkcionális implementáció, amelynek középpontjában a matematikai korrektség és bizonyítható tulajdonságok állnak. A specifikáció tartalmaz **271**+ bizonyított tételt.

 Áttekintés

| Szempont | Részletek |
|---|---|
| Nyelv | Lean 4 tételbizonyító |
| Méret | 2374 sornyi kód |
| Tételek száma | 271+ |
| Megközelítés | Tiszta funkcionális, mellékhatások nélkül |
| Ellenőrzési cél | Zig implementáció |
| Függőségek | Nincs (önállóan zárt) |

 Kulcsstruktúrák leképezése

| Lean struktúra | Zig megfelelője | Cél |
|---|---|---|
| SurpriseMetrics | SurpriseMetrics | Több dimenziós újdonsági pontszámok |
| SurpriseRecord | SurpriseRecord | Blokkonkénti metaadat |
| StorageState | ContentAddressableStorage | Blokkfárolási réteg |
| ManagerState | SurpriseMemoryManager | Legfelső szintű rendszerállapot |
| SurpriseMemoryStatistics | SurpriseMemoryStatistics | Összesített metrikák |

 A racionális számrendszer

A Rational típus számlálóból és nevezőből áll, ahol bizonyíték garantálja a nevező pozitivitását. Ez típusszinten zárja ki a nullával való osztást.

 Implementációs különbségek

| Szempont | Lean modell | Zig implementáció |
|---|---|---|
| Adatstruktúrák | List a rekordokhoz és tárolóhoz | HashMap a rekordokhoz |
| Számok | Rational (pontos) | f64 (lebegőpontos) |
| Tisztaság | Tiszta funkciók, immutábilis állapot | Mutábilis állapot mutex-szal |
| Fókusz | Bizonyítható korrektség | Teljesítmény és menetbiztonság |

 Az ellenőrzési munkafolyamat

## Definiálás Lean-ben: Funkcionális megvalósítás ManagerState-ben

## Invariánsok megadása: Definiálni, milyen tulajdonságok kell teljesüljenek ## Megőrzés bizonyítása: A művelet megőrzi az invariánsokat ## Zig implementálása: Teljesítménycentrikus verzió ugyanolyan szemantikával ## Kézi ellenőrzés: Zig megfelel a Lean specifikációnak

 Lean hatáskörön kívüli területek

A Lean specifikáció nem modellez:
- Párhuzamosságot, versenyhelyzet-feltételeket
- Memória-allokációt
- Külső rendszereket (ContentAddressableStorage, DataFlowAnalyzer)
- Valós teljesítmény-jellemzőket

---

 Formális modell

 Racionális számrendszer

A formális modell Rational típust használ lebegőpontos aritmetika helyett a pontos számítások és a formális bizonyítások érdekében.

 Blokkidentifikátorok

Rögzített méretű bájt-tömbökként definiálva a Zig implementáció hash-alapú azonosítójának tükrözéseként. Rendelkezik BEq, DecidableEq és Hashable instance-okkal.

 StorageState struktúra

structure StorageState where
    blocks : List StorageBlock
    capacity : Nat

A tároló blokklistáként modellezett hash map helyett, egyszerűsítve a bizonyításokat.

 ManagerState struktúra

structure ManagerState where
    storage         : StorageState
    surprise_records : List (BlockId × SurpriseRecord)
    surprise_threshold : Rational
    statistics      : SurpriseMemoryStatistics

A rekordok asszociációs listaként tárolódnak. A putRecord szűri az azonos blokk ID-vel rendelkező meglévő rekordot, mielőtt hozzáadná az újat.

 Funkcionális műveleti modell

Az összes művelet tiszta függvényként kerül definiálva, amelyek átalakítják a rendszerállapotot. A hibakezelés Except StoreError segítségével valósul meg.

 Kizárási algoritmus Lean-ben

A Lean implementáció teljes mergeSort-ot és take k-t használ egyszerűség kedvéért a bizonyításokban:

def partialSortCandidates (items : List CandidateItem) (k : Nat) : List CandidateItem :=
    let sorted := items.mergeSort (...)
    sorted.take k

---

 Invariáns-rendszer

 Invariáns-hierarchia

A rendszer négy szintű invariáns-hierarchiát alkalmaz:

StatisticsInvariant
       ↓
RetentionInvariant
       ↓
ManagerInvariant
       ↓
TraceInvariant

 StatisticsInvariant

Tulajdonságok:

| Tulajdonság | Garantálja |
|---|---|
| partition_le | high_surprise_blocks + low_surprise_blocks ≤ total_blocks |
| blocks_consistent | Ha total_blocks = 0, akkor high = 0 és low = 0 |

Megőrzési tételek:

| Művelet | Megőrzési tétel |
|---|---|
| Blokk hozzáadása | statistics_invariant_addBlock |
| Kötegelt hozzáadás | statistics_invariant_preserved_by_addBlock_sequence |

 RetentionInvariant

Tulajdonságok:

| Tulajdonság | Garancia | Indok |
|---|---|---|
| access_positive | Hozzáférési frekvencia ≥ 1 | A rekord csak tárolás után létezik |
| creation_before_access | Létrehozási idő nem lehet a hozzáférési idő után | Az idő előre halad |

 ManagerInvariant

| Összetevő | Tulajdonság | Garancia |
|---|---|---|
| stats_inv | Tartalmaz StatisticsInvariant-ot | Statisztikák konzisztensek |
| threshold_valid | Küszöb korlátai | 0 ≤ surprise_threshold ≤ 1 |

 TraceInvariant

A legfelső szintű invariáns, amely biztosítja a rendszer szintű korrektséget a műveletek sorozatán át.

 Helyességi garanciák az invariánsokból

## Statisztikai konzisztencia: High + Low soha nem haladja meg az összes blokkot

## Nincs negatív szám: Lean Nat típusa garantálja
3. Üres állapot konzisztencia: Üres esetén minden kategória nulla
## Időbeli monotonitás: access_frequency mindig ≥ 1 és sosem csökken
## Időrendi sorrend: creation_time ≤ last_access_time
## Küszöb érvényessége: Mindig [0, 1]-ben van

---

 Metrikus tér bizonyítások

 A metrikus tér axiómái

Egy metrikus tér d: X × X → ℝ távolságfüggvényt igényel, amely kielégíti a négy axiómát. A Lean specifikáció mindet bizonyítja a computeHashDistance függvényre BlockId értékeken.

 Hash-távolság implementáció

| Összetevő | Típus | Leírás |
|---|---|---|
| BlockId | Array UInt8 | 16 bájtos tartalom-hash |
| hammingDistNat | BlockId → BlockId → Nat | Nyers Hamming-távolság |
| computeHashDistance | BlockId → BlockId → Rational | Normalizált távolság: hamming / HASH_BITS |

 Szimmetria bizonyítás

Tétel: computeHashDistance a b = computeHashDistance b a

Strukturális indukcióval a bájt pozíciókon; minden pozícióban az xor_comm_uint8 tétel garantálja a bájtok **XOR**-jainak felcserélhetőségét.

 Azonosság bizonyítás

Tétel: computeHashDistance h h = 0

Alapja: x ^^^ x = 0 minden UInt8 értékre, ahol a Lean **XOR** önkioltó tulajdonsága (xor_self_zero) és a nulla popCount (popCount8_zero_is_zero) biztosítja a nullát.

 Háromszög-egyenlőtlenség bizonyítás

Tétel: d(a,c) ≤ d(a,b) + d(b,c)

| Szint | Összetevő | Cél |
|---|---|---|
| Bájt | popCount8_triangle_single | Egyetlen bájt XOR-jának egyenlőtlensége |
| Természetes | hammingDistNat_triangle | Teljes Hamming-távolság egyenlőtlensége |
| Racionális | computeHashDistance_triangle_rational | Teljes racionális egyenlőtlenség |

 Bizonyított tételek összefoglalója

| Tétel | Sor | Állítás |
|---|---|---|
| computeHashDistance_symmetric | 1693 | d(a,b) = d(b,a) |
| computeHashDistance_self_zero | 1700 | d(h,h) = 0 |
| computeHashDistance_triangle_rational | 1827 | d(a,c) ≤ d(a,b) + d(b,c) |
| computeHashDistance_nonneg | 1764 | d(a,b) ≥ 0 |
| computeHashDistance_bounded_num | 1769 | d(a,b).num ≤ HASH_BITS |

 Metrikus tér következményei

| Tulajdonság | Rendszer következménye |
|---|---|
| Szimmetria | A blokk-összehasonlítás sorrendtől független |
| Azonosság | Egy blokk maximálisan hasonlít önmagához |
| Háromszög-egyenlőtlenség | A távolságok tranzitívan konzisztensek |
| Korlátosság | Összes távolság normalizálva [0, 1]-be |

---

 Műveleti korrektség

 Cél és hatókör

A műveleti korrektségi tételek bizonyítják, hogy az egyes műveletek megőrzik a rendszer invariánsait. A tételek garantálják, hogy az egész végrehajtási nyomok megőrzik a rendszer invariánsait.

 Statisztikai műveletek korrektségi tételei

| Tétel | Tulajdonság |
|---|---|
| statistics_addBlock_total | Az összes blokk száma 1-gyel nő |
| statistics_addBlock_high | High szám nő, ha pontszám > küszöb |
| statistics_addBlock_low | Low szám nő, ha pontszám ≤ küszöb |
| statistics_invariant_addBlock | Megőrzi a StatisticsInvariant-ot |
| statistics_removeBlock_when_empty | Üres esetén nincs hatás |
| statistics_removeBlock_total | Az összes blokk 1-gyel csökken, ha > 0 |

 Hozzáférési rekord megőrzési táblázat

| Tulajdonság | Megőrzött? | Tétel |
|---|---|---|
| block_id | ✓ Igen | surpriseRecord_recordAccess_preserves_block_id |
| surprise_score | ✓ Igen | surpriseRecord_recordAccess_preserves_score |
| creation_time | ✓ Igen | surpriseRecord_recordAccess_preserves_creation |
| access_frequency | ✗ Nem (nő 1-gyel) | surpriseRecord_recordAccess_frequency |
| last_access_time | ✗ Nem (frissül) | surpriseRecord_recordAccess_time |

 Küszöb-frissítési helyesség

| Tétel | Tulajdonság |
|---|---|
| managerState_setSurpriseThreshold_threshold | Küszöb korlátolt értékre van állítva |
| managerState_setSurpriseThreshold_preserves_storage | Tároló változatlan |
| managerState_setSurpriseThreshold_preserves_records | Rekordok változatlanok |
| setThreshold_preserves_statistics_invariant | StatisticsInvariant megőrzött |

 Összefoglalás

| Művelet | Megőrzött invariánsok | Kulcs tulajdonságok |
|---|---|---|
| storeWithSurprise | ManagerInvariant, StatisticsInvariant | Növeli a blokk-számot, helyesen frissíti a statisztikákat |
| evictLowSurpriseBlocks | ManagerInvariant, StatisticsInvariant | Csökkenti a blokk-számot, nem távolítja el a max. prioritású blokkot |
| recordAccess | RetentionInvariant | Megőrzi az azonosítómezőket, növeli a frekvenciát 1-gyel |
| setSurpriseThreshold | ManagerInvariant | Megőrzi a tárolót és a rekordokat, [0,1]-re korlátoz |

---

 Nyomkövetés-végrehajtás

 Áttekintés

A nyomkövetés-végrehajtás formális keretrendszert biztosít a műveletek sorozatainak ellenőrzéséhez. A SystemTrace algebrai adatstruktúrák segítségével modellez műveleti sorozatokat.

 A SystemTrace struktúra

| Konstruktor | Paraméterek | Cél |
|---|---|---|
| SystemTrace.empty | Nincs | Alap eset |
| SystemTrace.storeOp | prev, data | Adattárolás meglepetési számítással |
| SystemTrace.evictOp | prev, target | Blokkok kizárása a célkapacitásig |
| SystemTrace.setThresholdOp | prev, threshold | Meglepetési küszöb módosítása |
| SystemTrace.accessOp | prev, blockId | Hozzáférés rögzítése meglévő blokkhoz |

 Nyomkövetés-alkalmazás főbb jellemzői

## Rekurzív alkalmazás: Minden művelet először rekurzívan alkalmazza az előző nyomkövetést

## Hibapropagáció: A korai műveletek hibái megakadályozzák a későbbiek végrehajtását
3. Állapot-szálak: Egy művelet állapota a következő inputja lesz

 Invariáns-megőrzési tételek

| Tétel | Cél |
|---|---|
| trace_invariant_init | A kezdeti állapot kielégíti az invariánst |
| applyTrace_empty_preserves_invariant | Az üres nyomkövetés megőrzi az invariánst |
| trace_setThreshold_preserves_invariant | A küszöb-beállítás megőrzi az invariánst |
| applyTrace_preserves_invariant_structural | Az összes nyomkövetés megőrzi az invariánst |

 Nyomkövetés hossza és műveletek számlálása

Az applyTrace_ok_implies_op_count_ge tétel bizonyítja, hogy a sikeres nyomkövetés-alkalmazás növeli a műveletek számát. Ez garantálja: a szám sosem csökken, és minden sikeres művelet pontosan 1-gyel növeli.

---

 Haladó témák

 Összefonódás-szervezés

Az összefonódás egy mechanizmus a magas meglepetési értékű blokkok párokba rendezésére, lehetővé téve a tároló háttérrendszer számára a fizikai elrendezés optimalizálását.

Korlátozások:
- Maximum MAX_ENTANGLEMENT_PAIRS = **100** magas meglepetési értékű blokk figyelembe vétele
- Maximum lehetséges párok: C(**100**, 2) = 4 **950**
- Az összefonódás nem befolyásolja a megtartási prioritás számítást
- Az összefonódott blokkok is kizárhatók, ha alacsony a prioritásuk

 Részleges rendezési algoritmus

Bonyolultság-összehasonlítás:

| Forgatókönyv | Teljes rendezés (MergeSort) | Részleges rendezés (Selection) |
|---|---|---|
| k=10, n=10 000 | ~133k művelet | ~100k művelet |
| k=100, n=10 000 | ~133k | ~1M (teljes rendezés jobb) |

Lean megközelítés: Teljes mergeSort + take k – egyszerűbb a bizonyítás. A Zig teljesítményért vált.

 Teljesítmény-jellemzők

Meglepetési számítás – O(1) amortizálva:

| Művelet | Bonyolultság |
|---|---|
| Mintaválasztás | O(n) |
| Jaccard-számítás | O(1000 × min(1000, data_len)) |
| Hash-távolság | O(1000 × 16) |
| Időbeli újdonság | O(1) |
| Összesen | O(n + 1M) |

Kizárási teljesítmény:

| Forgatókönyv | Idő |
|---|---|
| 10% kizárása 10 000 blokkból | 1 000 × 10 000 = 10M összehasonlítás |
| 50% kizárása 10 000 blokkból | 5 000 × 10 000 = 50M összehasonlítás |

Memóriaterhelés blokkszámtól függően:

| Rendszer mérete | Rekordmemória |
|---|---|
| 1 000 blokk | ~144 KB |
| 10 000 blokk | ~1,44 MB |
| 100 000 blokk | ~14,4 MB |
| 1 000 000 blokk | ~144 MB |

 Konfiguráció és hangolás

Meglepetési küszöb kiválasztása:

| Küszöb | Értelmezés | Felhasználási eset |
|---|---|---|
| 0.1 – 0.2 | Nagyon megengedő | Általános célú gyorsítótárazás |
| 0.3 – 0.4 | Közepes (alapértelmezett) | Kiegyensúlyozott redundancia és újdonság |
| 0.5 – 0.7 | Szigorú | Tudományos adatok elemzése |
| 0.8 – 1.0 | Nagyon szigorú | Extrém deduplikáció |

Megtartási prioritás súlyok hangolása:
- Alapsúly növelése (0.5 → 0.7): Újdonság prioritizálása a hozzáférési minták felett
- Kor-súly növelése (0.3 → 0.5): Nemrég elért adatok prioritizálása (**LRU**-szerű)
- Frekvencia-súly növelése (0.2 → 0.4): Sűrűn elért adatok prioritizálása (**LFU**-szerű)

Mintavételezési paraméterek:

| Mintaméret | Pontosság | Teljesítmény |
|---|---|---|
| 100 | Alacsony (~90%) | Nagyon gyors |
| 1000 (alapértelmezett) | Magas (~99%) | Gyors |
| 5000 | Nagyon magas (~99.9%) | Közepes |

Kapacitástervezési stratégia:

max_kapacitás = **100** **000** blokk magas vízjel  = 90 **000** blokk  ← kizárás indítása alacsony vízjel = 70 **000** blokk ← kizárás célértéke

Amikor a tároló eléri a 90 **000**-et:
    → 20 **000** legalacsonyabb prioritású blokk kizárása
    → Eredő szám: 70 **000**

Teljesítmény-monitorozás:

| Metrika | Optimális tartomány | Teendő, ha kívüle van |
|---|---|---|
| high_surprise_blocks / total_blocks | 0.2 – 0.4 | surprise_threshold beállítása |
| average_surprise | 0.3 – 0.6 | Adatok diverzitásának vizsgálata |
| novel_block_allocations / total_blocks | 0.3 – 0.5 | Az adatok újdonsági arányának mutatója |

Menetbiztonsági optimalizációs lehetőségek (jelenlegi implementációban nem valósítva meg):

## Olvasó-írói zár: Egyidejű olvasások engedélyezése

## Atomi számlálók: Statisztikai frissítések zár nélkül ## Előzetes meglepetési számítás: Meglepetés kiszámítása zár megszerzése előtt ## Zárfelosztás: Külön zárak a surprise_records-hoz és a statistics-hoz
