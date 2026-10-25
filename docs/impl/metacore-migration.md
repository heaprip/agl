# Миграция общего metacore

Статус: выполняется в ветке `refactor/metacore-migration`. Это замена
представлений рабочего кода, а не второй калькулятор рядом с agl.

## Уже перенесено

- `meta::{EntityId, ClaimId, EvidenceId, Intension, Entity, Evidence,
  Projection, Metaedge}` — общий carrier.
- `eval::Derivation` непосредственно хранит `Entity + Evidence`; альтернативы
  одного atom сходятся в общий claim как OR, premises одного derivation
  образуют AND.
- `bank::Entry` хранит отдельно неизменяемую конструкцию, её construction
  evidence и context-indexed projection. `EntityId` не зависит от extent,
  evidence или контекста.
- `meta::Metagraph` индексирует записи обоих исполнителей, поддерживает
  relation-as-endpoint, локальное `EqualAt` и вычисляемые состояния
  active/retracted/unsupported без удаления истории.
- `tests/metacore.rs` проверяет общий carrier на evaluator и Bank;
  `tests/identity_extent.rs` строит killer witnesses настоящим Bank.
- `layer::Query` экспортирует общий glue-intension, а таблица слоя возвращает
  все relation occurrences с подходящим extent. Для обычного уникального
  мира сохранён allocation-free singleton fast path.
- `bank::ExactRelation` имеет dense и sparse storage с одной семантической
  equality; storage не попадает в identity или canonical report.
- `meta_journal` пишет типизированные evidence/entity/projection/metaedge/
  equality/retraction events в существующий append-only `Journal`. Replay
  заново собирает работающий граф, включая propagation отзыва.
- Обычный rule head `metaedge(relation: ..., role: ...)` создаёт
  `Intension::Metaedge`, а не безымянный atom. Ядро добавляет роль
  `occurrence: &derived-ID`; следующее правило может связать её переменной и
  использовать построенное ребро как relation или endpoint нового ребра.
- `Intension::Glue` хранит связанные `EntityId` и незаполненные `Hole` в одном
  `parts`. `Metagraph::expand_open_frontier` подставляет активные закрытые
  occurrences без выбора доменного solver; порядок заполнения меняет evidence,
  но не итоговый `EntityId`.

## Почему это не прежний prototype

Проекции killer test не задаются руками. Две glue-intension ищутся среди
`Bank::Entry`; их extent вычисляет прежний векторный executor `bank::Ext`.
Те же `Entity/Evidence/Projection`, а не адаптер-копия, находятся внутри
`Derivation` и `Entry`. Общий слой не выполняет свой relational search — он
хранит identity, контекст и proof state результатов существующих алгоритмов.

## Следующие границы

1. Научить обычные relation/rule mismatches оставлять открытые intensions в
   frontier. Сейчас общий carrier и expansion готовы, но начальные holes ещё
   дают структурные библиотеки (`layer::Query`), а не сама аномалия.
2. Добавить valid/transaction time поверх journal; replay пока восстанавливает
   логическое состояние, но не бивременную политику.
3. Перенести оставшиеся самостоятельные исполнители только по мере их участия
   в сквозном пути, а не механически.
4. Только затем поднимать физическую веху Джанибекова на общий carrier.

## Не смешивать

- `Build` остаётся исполняемым локальным планом Bank; semantic identity задаёт
  `Intension`. Это не две конкурирующие семантики.
- CQ-core и индекс по extent разрешено использовать для планирования, но не
  для слияния `EntityId`.
- `Evidence.context` — контекст вычисления; `source_context` — плоскость
  объявления источника. Они намеренно различны.
