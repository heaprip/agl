# Критический аудит академического основания

Дата среза: 2026-10-25. Аудит начат независимым `gpt-6.1-sol`; после
зависания оркестрации его найденные кандидаты и замечания к коду проверены
отдельно по первичным публикациям и текущему рабочему дереву.

## Вердикт

**Частично велосипед; уверенность 0,85.** Почти каждый отдельный механизм уже
имеет более строгую теорию и часто готовую реализацию. Особенно близки:

- regular logic / relational calculus для запросов-склеек;
- conjunctive queries и гомоморфизмы для положительного фрагмента;
- F-logic + HiLog + well-founded semantics для отношений/формул как данных,
  метапрограммирования и defeasible knowledge representation;
- provenance semirings и ATMS для оснований и альтернативных контекстов;
- open hypergraphs/cospans и adhesive graph rewriting для интерфейсов и
  структурной композиции;
- e-graphs для равенств, конгруэнции и сокращения повторного поиска.

Один найденный формализм не закрывает весь заявленный контракт. Возможная
собственная часть agl — **не новый вариант λ-исчисления и не новый гиперграф**,
а композиция четырёх различений:

1. first-class identity конкретного отношения;
2. его intension/путь построения;
3. context-indexed extension как проекция, а не identity;
4. provenance и пересмотр этой проекции.

Пока это только проект контракта. Код ещё нарушает главное различение
`identity != extent`, поэтому утверждать новый метод вычислений рано.

## Ближайшие академические основания

| Наш объект или операция | Ближайший аналог | Совпадение и граница |
| --- | --- | --- |
| запрос как склейка отношений с забыванием внутренних концов | regular logic, cartesian bicategories, graphical regular logic | Почти точное основание положительного existential/conjunctive фрагмента. Не даёт автоматически defeasibility, occurrence identity и историю. |
| проверка и минимизация запроса гомоморфизмами | conjunctive queries, containment mappings, cores | Точное основание `concept`/положительной части `layer`. Эквивалентность запросов по core намеренно забывает разные представления; для agl это допустимо только как индекс, не identity. |
| порты, boundary и композиция открытых структур | decorated/structured cospans, hypergraph categories | Точное основание структурной композиции по интерфейсу. Само по себе не означает, что связь может быть endpoint другой связи, и не задаёт truth/provenance. |
| локальная структурная перепись | DPO/SPO graph rewriting в adhesive categories | Даёт условия существования переписи, concurrency и critical pairs. Сильнее текущих неформальных «склеек», но требует выбрать тип графа и правила. |
| отношение, predicate или формула как аргумент | HiLog; reification; F-logic | Уже известный способ получить higher-order syntax с first-order semantics. Reification не даёт λ-abstraction или β-reduction автоматически. |
| object/frame knowledge, inheritance и rules | F-logic | Покрывает значительную часть relation-first KR и структурированных объектов; не сохраняет автоматически отдельную occurrence identity каждого одинакового факта. |
| default negation, defeasibility, динамические модули и updates | well-founded logic programming, Transaction Logic, ErgoAI/Flora-2 | Готовый обязательный baseline для текущего ядра. Не является открытым гиперграфовым IR или бивременным журналом. |
| provenance положительных запросов и Datalog | semiring-annotated relations | Точная композиционная семантика why/how provenance. Отрицание и defeasible revision требуют расширения, а не прямого переноса базового semiring. |
| несколько несовместимых наборов оснований | assumption-based truth maintenance system | ATMS уже хранит assumption sets, inconsistent environments и переключение контекстов без переписывания всей базы. Это близко к fork/основаниям, но не к геометрии плоскостей. |
| снятие убеждения и пересмотр теории | AGM belief revision | Даёт постулаты contraction/revision. Не выбирает предметную политику и не хранит сам по себе provenance DAG. |
| законы, нормальные формы и повторное использование эквивалентностей | term rewriting, congruence closure, e-graphs/equality saturation | Готовая теория и быстрые структуры вместо собственного полного перебора. E-graph сливает только доказанное равенство термов; его e-class не должен становиться agl identity. |
| группировка объектов и атрибутов по замыканию | formal concept analysis | Точное основание уже используемой H52/H68 части. Это аналитическая проекция, не общий carrier. |
| разные логики и перевод между ними | institutions / indexed model theory | Подходит для инвариантности satisfaction при смене сигнатуры. Не доказывает, что текущие `Plane` образуют institution или presheaf. |
| данные, меняющиеся с контекстом | presheaves/indexed categories/fibrations | Возможный язык для restriction/reindexing. Нужны явно заданные context category и functor laws; одного поля `Plane` недостаточно. |

Ключевые источники:

- Fong, Spivak, [Graphical Regular Logic](https://arxiv.org/abs/1812.05765).
- Carboni, Walters, [Cartesian Bicategories I](https://doi.org/10.1016/0022-4049(87)90121-6).
- Fong, [Decorated Cospans](https://arxiv.org/abs/1502.00872) и
  [The Algebra of Open and Interconnected Systems](https://arxiv.org/abs/1609.05382).
- Lack, Sobociński, [Adhesive and Quasiadhesive Categories](https://doi.org/10.1051/ita:2005028).
- Goguen, Burstall, [Institutions: Abstract Model Theory for Specification and Programming](https://doi.org/10.1145/147508.147524).
- Chen, Kifer, Warren, [HiLog: A Foundation for Higher-Order Logic Programming](https://doi.org/10.1016/0743-1066(93)90039-J).
- Kifer, Lausen, Wu, [Logical Foundations of Object-Oriented and Frame-Based Languages](https://doi.org/10.1145/210332.210335).
- Kifer, Swift, [Multi-paradigm Logic Programming in the ErgoAI System](https://arxiv.org/abs/2603.29819).
- Green, Karvounarakis, Tannen, [Provenance Semirings](https://doi.org/10.1145/1265530.1265535).
- de Kleer, [An Assumption-Based TMS](https://doi.org/10.1016/0004-3702(86)90080-9).
- Alchourrón, Gärdenfors, Makinson, [On the Logic of Theory Change](https://doi.org/10.2307/2274239).
- Ganter, Wille, [Formal Concept Analysis: Mathematical Foundations](https://doi.org/10.1007/978-3-642-59830-2).

## Что нельзя пока называть предпучком или новым calculus

Принятые результаты defeasible-вывода не образуют restriction maps
автоматически. При уточнении контекста вывод может исчезнуть из-за нового
исключения или появиться из-за новых premises. Чтобы говорить о presheaf,
нужно задать:

- категорию контекстов и направление морфизмов;
- отображение данных и выводов вдоль каждого морфизма;
- сохранение identity и provenance;
- законы identity и composition для restriction;
- политику противоречий, при которой эти отображения вообще функциональны.

Аналогично, relation reification позволяет передать predicate/formula как
данные, но не вводит application/abstraction и не доказывает β/η-законы.
Проверка K/S/β остаётся сравнительной звездой, а не семантикой agl.

## Готовый конкурент, который нельзя игнорировать

Hyperon/MeTTa разобран отдельно по текущему Rust-коду, а не только по статьям:
[`2026-10-25-hyperon-code-audit.md`](2026-10-25-hyperon-code-audit.md). Он
подтверждает общий путь «programs/relations as data + matching + rewriting»,
но не предоставляет нативного контракта occurrence identity, context-indexed
extent и evidence.

[ErgoAI](https://github.com/ergoAI) / Flora-2 объединяет F-logic, HiLog,
well-founded semantics, defeasible reasoning и Transaction Logic. В нём уже
есть higher-order-looking syntax с first-order semantics, динамические модули,
updates, explanations и bounded reasoning.

ErgoAI не заменяет весь agl: у него нет заявленного контракта открытого
метаграфового IR, context-indexed extents как отдельных проекций и
бивременного lockfile. Но он закрывает достаточно много KR-слоя, чтобы быть
обязательным baseline. Если agl не может выразить и воспроизвести выбранные
ErgoAI-сценарии с более строгим сохранением identity/provenance, собственное
ядро не оправдано.

Для отдельных подсистем также обязательны baseline:

| Подсистема | С чем сравнивать | Что не переносить слепо |
| --- | --- | --- |
| equational search | `egg`/e-graphs и Knuth–Bendix | слияние e-class не равно слиянию исторических сущностей |
| positive relational inference | Datalog/CQ engine | closed-world negation и потерю occurrence identity |
| provenance | K-relations/ProvSQL | предположение о commutative positive algebra для defeasible negation |
| forks и contradictions | ATMS | экспоненциальный рост environments без политики отсечения |
| structural rewrite | DPO в adhesive category | категориальную терминологию без проверяемых pushout conditions |

Решение «не встраивать готовый solver» может оставаться инженерной границей,
но не освобождает от differential testing с готовыми движками и от переноса
доказанной семантики. Иначе проект повторяет их ошибки и алгоритмы без
свойств, ради которых они создавались.

## Конкретные противоречия в текущем коде

1. **`layer::table` отождествляет по extent.** В `src/layer.rs:417–428`
   строится `BTreeMap<&Ext, u32>`, поэтому одинаковый extent выбирает один
   номер. По новому контракту разные intensions могут иметь одинаковую
   проекцию. Тогда `g(r,s,t)` на quotient по extent и `g` над сущностями —
   разные операции; во втором случае допустимо несколько `t`.
2. **Identity факта пока не identity отношения.** `model::Fact` имеет
   `id` (`src/model.rs:323–328`), но closure в `eval::Db` индексирует атом по
   его печатному имени и хранит один atom с набором derivations
   (`src/eval.rs:47–54`). Несколько occurrences уже схлопнуты до proposition.
3. **Приближённое число названо логическим равенством.** `term_eq` и `CmpOp::Eq`
   используют относительный допуск `1e-12` (`src/eval.rs:1861–1865`,
   `1957–1958`). Такое отношение в общем случае нетранзитивно и не может быть
   equality/congruence. Это должен быть отдельный typed predicate `close` с
   явным tolerance/context.
4. **Held-out используется для выбора.** `learn.rs:115` считает heldout, а
   `:119` сортирует кандидаты по нему. После этого набор является validation,
   не независимым финальным test; отчёт не должен называть его слепой
   проверкой обобщения.
5. **Документ и исполнитель расходятся в главном месте.** `relations.md`
   §§231–240 говорит, что склейка получает identity, а extent — только её
   проекция. Реализованный `layer::table` ищет identity именно по extent.

Дополнительный риск: homomorphic CQ equivalence и cores правильно удаляют
избыточное для ответа на запрос, но тем самым могут стереть occurrence,
историю построения и provenance. Их следует использовать для индекса и
планирования, а не как критерий тождества agl-сущности.

## Три честные архитектурные сборки

### A. Консервативная: KR прежде нового calculus

- семантический baseline: F-logic/HiLog + well-founded/defeasible rules;
- positive query layer: regular logic / CQ;
- provenance: semiring annotations плюс явный derivation DAG;
- forks: ATMS environments; revision policy отдельно;
- relation occurrence — собственный immutable ID поверх proposition layer.

Плюс: минимум новой математики, быстрое differential testing с ErgoAI.
Минус: открытая структурная композиция не является центром системы.

### B. Категориальный IR

- carrier: typed open hypergraphs/structured cospans;
- query semantics: graphical regular logic/cartesian bicategory;
- rewrite: DPO в выбранной adhesive category;
- context: indexed category только после доказательства reindexing laws;
- provenance: annotation/derivation layer, не спутанная с equality.

Плюс: строгая композиция и ясные законы. Минус: высокая цена формализации;
defeasibility и revision всё равно добавляются отдельно.

### C. Собственный agl-контракт

Оставить публичный словарь `EntityId + Intension + Ports + ContextualExtent +
Provenance`, но каждую операцию дать как адаптер к проверенному фрагменту A/B.
Новизной считать только закон их совместимости, если он сформулирован и
проверен. Это наиболее близко к текущему замыслу, но также наиболее легко
превращается в набор красивых названий без семантики.

Рекомендация: начать с C как формата данных, но семантику и эталоны брать из
A; B вводить только для тех операций, где cospan/DPO действительно дают
проверяемый закон. Не объявлять систему предпучком или новым calculus заранее.

## Killer experiment до дальнейшей реструктуризации

Один малый мир должен одновременно проверить всё специфическое для agl:

1. две разные intensions `a` и `b` имеют разные immutable IDs и разные пути;
2. в контексте `p` их extents равны;
3. `a` и `b` независимо становятся endpoints двух метаотношений;
4. в контексте `q` extents расходятся, ID не меняются;
5. у равенства проекций есть два разных provenance expressions;
6. снятие одной assumption отменяет только зависимые результаты и не
   переписывает историю;
7. canonicalization/CQ core/e-graph ускоряют поиск, но не сливают `a` и `b`;
8. один и тот же результат воспроизводится собственным ядром и независимыми
   baseline-проверками соответствующих фрагментов.

До прохождения этого теста оптимизация A3/universe и дальнейшее расширение
атласа не проверяют центральную ставку проекта.

## Эффект Джанибекова

Текущей формализации недостаточно, чтобы честно прийти к эффекту без отдельного
физического калькулятора. Сначала нужен killer experiment выше. Затем:

- внутреннее ядро может хранить качественные отношения, симметрии,
  инварианты, контексты и основания;
- численная интеграция уравнений Эйлера должна быть внешним oracle/world с
  явным provenance, а не скрытым Rust-алгоритмом, объявленным выводом agl;
- специфическая проверка вехи — перенос одного и того же relation identity
  между качественной, геометрической и численной проекциями без их слияния.

Если это не удаётся, веха проверит только физическую модель, но не agl.

## Практическое решение

1. Остановить развитие `universe` как основного пути.
2. Исправить терминологические утверждения в документах: «кандидат на indexed
   semantics», а не готовый presheaf; «reified relation», а не λ-abstraction.
3. Сделать killer experiment на текущих `Plane`, `Derivation` и `Bank`.
4. Параллельно построить два маленьких baseline: CQ/regular-logic для
   положительной склейки и ErgoAI/Flora-2 для reification + defeasibility.
5. После результатов выбрать A, B или C. Только тогда проводить большую
   реструктуризацию и возвращаться к вехе Джанибекова.

Главный итог: проект не надо выбрасывать, но его нельзя защищать новизной
отдельных деталей. Его право на собственное ядро должно быть доказано ровно
там, где готовые системы обычно теряют различие между relation occurrence,
intension, context-dependent extension и provenance.
