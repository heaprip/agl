# Identity/extent killer test на Hyperon/MeTTa

Дата: 2026-10-25. Ветка эксперимента создана непосредственно от
`checkpoint/pre-killer-2026-10-25`, независимо от Rust-реализации agl.

Проверена официальная ревизия Hyperon
`3f76dc460da6961f57f69f6c3e550c59c74ada83`. Исполняемый сценарий и ожидаемый
stdout лежат в [`experiments/hyperon/`](../../experiments/hyperon/). Все 16
операций завершились `[()]`; это 14 assertions и две мутации Space.

## Вердикт

**Гибрид возможен, профиль agl над Hyperon пока не оправдан.** MeTTa коротко
выражает структуру первых семи пунктов killer test, если пользователь заранее
вводит protocol из ID, projection, evidence, premise и metaedge atoms. Но
Hyperon не обеспечивает этот protocol:

- identity существует только потому, что сценарий вручную ввёл символы `a`
  и `b` и связал их с intensions;
- extent/evidence/context являются обычными позициями обычных expressions;
- удаление основания не инвалидирует зависимые projection, equality и
  metaedge;
- retraction history появляется только после отдельного ручного `add-atom`;
- канонического proof-relevant replay/report в ядре нет.

То есть MeTTa годится как выразительный rewrite/query frontend и независимый
baseline. Authoritative store с identity, dependency validity и replay всё
равно пришлось бы написать как библиотеку правил/grounded layer поверх него.
Это уже собственное ядро agl, только размещённое внутри чужого универсального
интерпретатора.

## Что именно проверено

| Пункт killer test | Результат в чистой MeTTa | Нативная гарантия Hyperon |
| --- | --- | --- |
| разные IDs и intensions | работает с `(entity a ...)`, `(entity b ...)` | нет: IDs — пользовательские symbols |
| одинаковый extent в `p` | обе projections ссылаются на `diag01` | нет: extent — пользовательский atom |
| индекс возвращает `[a,b]` | один `match` возвращает оба bindings | да для записанного pattern, но не как invariant identity |
| relation как endpoint | два metaedge atoms указывают на `a` и `b` | синтаксически да через reified IDs |
| `EqualAt` только в `p` | явный atom находится в `p`, отсутствует в `q` | отсутствие глобального equality получается потому, что `equal-at` — обычный predicate |
| контрпример `(2,2)` в `q` | membership query находит его только у `a` | данные заданы явно, не вычислены Hyperon |
| restriction `q → p` | conjunctive `match` соединяет `holds` с двумя `maps` | query работает; functor laws не проверяются |
| отзыв `a-build` | **не проходит**: dependents остаются | `remove-atom` не знает пользовательский premise DAG |
| история после отзыва | только ручной `(retracted ...)` | автоматической истории нет |
| порядок/replay | `assertEqual` сравнивает множество результатов | нет канонического байтового semantic report |
| оптимизатор не сливает IDs | wrappers сохраняют symbols | без wrappers структурно равные atoms не имеют occurrence identity |

## Почему первые семь пунктов — не прохождение контракта

Универсальный symbolic язык ожидаемо способен **описать** нужные записи. Тем
же способом их можно описать в S-expressions, Prolog facts или JSON. Вопрос
killer test сильнее: продолжает ли система соблюдать различения после
вычисления, оптимизации и revision без дисциплины, которую каждый пользователь
должен помнить вручную.

MeTTa-сценарий специально не подменяет эту границу библиотекой `valid?`:
такую библиотеку можно написать через дополнительные rules и materialization,
но тогда отдельно понадобятся:

1. семантика положительных и отрицательных зависимостей;
2. termination/fixpoint policy;
3. multiple independent derivations;
4. удаление одного основания без удаления другого;
5. immutable history и canonical replay;
6. тесты на порядок и дубликаты.

Это ровно работа evidence/revision kernel, а не бесплатное свойство Hyperon.

## Что Hyperon всё-таки дал

1. Representation protocol очень компактен: никаких специальных AST для
   entity/projection/metaedge не требуется на исследовательском frontend.
2. `match` естественно возвращает обе identity при равном extent и удобно
   исполняет конечный restriction как join.
3. Структура правила и данные находятся в одном Space, поэтому поверх готового
   agl journal можно экспериментировать с reflective search без изменения
   authoritative semantics.
4. Наблюдаемая проблема не в выразимости, а в proof relevance, revision и
   детерминированном состоянии. Это значительно сужает собственную задачу agl.

## Решение по ранее объявленному критерию

- **Не профиль над Hyperon сейчас:** короткий protocol описывает записи, но не
  обеспечивает revision/replay; для прохождения потребуется собственный TMS.
- **Не переносить Hyperon в зависимости agl:** сборка текущей ревизии сама
  требует feature-workaround вокруг optional DAS/JSON, а ядро agl должно
  оставаться маленьким и офлайн.
- **Оставить гибрид как будущую возможность:** MeTTa может быть внешним
  генератором/фронтендом, если все принятые результаты возвращаются в
  authoritative agl store с явными IDs и evidence.
- **Следующий gate собственной реализации:** один реальный `Bank::Entry` и
  один `eval::Derivation` должны без дублирования адаптироваться к новому
  store. Если нет — Rust-ветку killer test удалить, а не наращивать рядом.

## Ограничения эксперимента

- Extents `p/q` заданы atoms, а не вычислены MeTTa из `Glue`; здесь проверяется
  semantic contract хранения и query, не скорость или полнота rewrite search.
- Используются стандартные grounded builtins `match`, `add-atom`,
  `remove-atom` и assertions, но нет пользовательского Rust/Python-кода.
- Не проверялись PLN, DAS contexts и внешние cognitive modules: они могут
  реализовать дополнительную политику, но не меняют обнаруженный контракт
  core Atom/Space.
