# Hyperon/MeTTa: аудит текущего кода против контракта agl

Дата среза: 2026-10-25.

Проверена официальная реализация
[`trueagi-io/hyperon-experimental`](https://github.com/trueagi-io/hyperon-experimental)
на ревизии
[`3f76dc460da6961f57f69f6c3e550c59c74ada83`](https://github.com/trueagi-io/hyperon-experimental/tree/3f76dc460da6961f57f69f6c3e550c59c74ada83).
Это аудит кода, а не пересказ позиционных материалов Hyperon. Сравнение
проводится с контрактом из
[`impl/identity-extent-test.md`](../impl/identity-extent-test.md), а не с общей
целью «сделать AGI».

## Короткий вердикт

Hyperon подтверждает, что исходная интуиция agl не изолирована: отношения и
программы можно хранить как данные, вычислять сопоставлением и переписью,
получать несколько ветвей результата, делать пространства first-class и
подключать внешние вычисления как grounded atoms.

Но текущий Hyperon **не реализует специфический контракт agl**. Его рабочее
ядро — структурные S-выражения, pattern matching по AtomSpace и
недетерминированная интерпретация равенств-переписей. В нём нет встроенного
различения:

```text
entity occurrence != intension != context-indexed extent != evidence
```

Поэтому Hyperon не делает проект лишним велосипедом. Он является обязательным
baseline и источником архитектурных уроков, но не готовой заменой. Уверенность
в этом выводе: 0,9 для проверенной ревизии ядра; расширения PLN/DAS могут
реализовывать отдельные части поверх него, но не меняют публичную семантику
`Atom`, `Space` и интерпретатора.

## Что фактически является носителем вычисления

### Atom — структурный терм, а не occurrence

Публичный `Atom` имеет четыре варианта: `Symbol`, `Expression`, `Variable` и
`Grounded`. `Expression` рекурсивно содержит другие atoms, поэтому отношение,
формулу или программу действительно можно поместить внутрь следующего
отношения. Это важное совпадение с исходной интуицией agl.

Однако равенство atoms структурное: symbols сравниваются по имени,
expressions — по содержимому, grounded values — предоставленным типом. У
`Atom` нет обязательного immutable occurrence ID. Внутренний ID индексатора
не исправляет это: повторная вставка hashable atom возвращает прежний ID, а
expressions этот `AtomStorage` вообще не считает hashable.

Источники в коде:

- [`Atom` и четыре варианта](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/hyperon-atom/src/lib.rs#L827-L849);
- [структурный `PartialEq`](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/hyperon-atom/src/lib.rs#L981-L990);
- [`AtomStorage`: прежний ID для равного atom](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/hyperon-space/src/index/storage.rs#L10-L53).

Следствие: две одинаково записанные связи от разных источников могут иметь
кратность в хранилище, но не получают из ядра две устойчивые семантические
identity с разными историями. Для этого пользователь должен явно оборачивать
их ID и evidence в новые atoms.

### Space — запрашиваемое хранилище, не категория контекстов

`Space` предоставляет `query`, `subst`, `visit` и `atom_count`; `SpaceMut` —
`add`, `remove`, `replace`. Запрос возвращает множество подстановок. Составной
запрос соединяет результаты через общие переменные. `DynSpace` можно поместить
в atom как grounded value, а его собственное равенство — равенство адресов
объектов.

Стандартный `GroundingSpace` хранит `AtomIndex<AllowDuplication>` и выполняет
pattern query. Наблюдатель пространства видит только события
`Add/Remove/Replace`; derivation/evidence DAG из этих событий автоматически не
возникает.

Источники в коде:

- [контракт `Space`](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/hyperon-space/src/lib.rs#L152-L216)
  и [`SpaceMut`](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/hyperon-space/src/lib.rs#L218-L270);
- [identity `DynSpace` по адресу](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/hyperon-space/src/lib.rs#L306-L325);
- [`GroundingSpace` и стратегия дубликатов](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/lib/src/space/grounding/mod.rs#L12-L39);
- [события наблюдателя](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/hyperon-space/src/lib.rs#L45-L66).

В MeTTa можно явно выбрать space через `evalc`, а DAS предоставляет отдельно
названные contexts. Но в проверенном ядре нет порядка контекстов, intersection,
restriction maps или законов identity/composition. Поэтому Hyperon space и agl
context/`Plane` — не одно понятие.

### Interpreter — query переписей плюс внешнее исполнение

При вычислении неграундированного выражения интерпретатор строит запрос
`(= expression $X)` к текущему space. Все найденные bindings становятся
альтернативными ветвями плана. Если голова — executable grounded atom,
управление передаётся Rust-объекту, который возвращает atoms и необязательные
bindings.

Это компактная и сильная модель: правила являются обычными atoms, а
интерпретация естественно многозначна. Одновременно grounded execution —
escape hatch: его код может реализовать семантику и эффекты, не выводимые из
символического space. Результат ядра — atom с bindings, а не четверка
`entity/context/extent/evidence`.

Источники в коде:

- [выбор grounded execution или query](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/lib/src/metta/interpreter.rs#L504-L556);
- [построение запроса `(= expression $X)`](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/lib/src/metta/interpreter.rs#L604-L638);
- [описание минимального плана MeTTa](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/docs/minimal-metta.md).

### Типы — факты и запросы в том же пространстве

Тип задаётся atom вида `(: a A)`, function type — `(-> A B)`, subtype —
отдельным отношением. Проверка типов сама запрашивает эти atoms в space;
неуказанный тип становится `%Undefined%` и может совпасть с требуемым.

Это полезная открытая система типов, но она не равна typed ports открытого
гиперграфа: из неё не следуют boundary composition, корректность склейки или
сохранение occurrence identity.

Источник: [реализация type queries](https://github.com/trueagi-io/hyperon-experimental/blob/3f76dc460da6961f57f69f6c3e550c59c74ada83/lib/src/metta/types.rs#L1-L46).

## Заявленный metagraph и реализованный механизм

Статья
[Reflective Metagraph Rewriting as a Foundation for an AGI “Language of
Thought”](https://arxiv.org/abs/2112.08272) описывает AtomSpace как
типизированный metagraph, допускает представление программ, правил и следов
вывода внутри самого metagraph и предлагает reflective metagraph rewriting как
общую модель.

Это направление, а не законченная формальная семантика: сама статья оставляет
детальную формализацию дальнейшей работе. В проверенной Rust-реализации
публичный carrier остаётся рекурсивным `Atom`, основной execution path — query
равенств и grounded calls, а автоматического proof/provenance graph у
результата нет. Proofs можно кодировать пользовательскими atoms или строить в
когнитивных слоях, но это другое утверждение, чем proof relevance ядра.

Поэтому выражение «Hyperon уже вычисляет переписью произвольного метаграфа»
слишком сильное для описания текущего кода. Точнее: MeTTa представляет
программы структурными atoms, индексирует и сопоставляет их в spaces и ведёт
многоветочное переписывание; metagraph — архитектурная интерпретация и
направление расширения этой модели.

## Сопоставление с контрактом agl

| Свойство | Hyperon на проверенной ревизии | Контракт agl |
| --- | --- | --- |
| relation/formula as data | Да: вложенный `Expression` | Да: relation может быть endpoint |
| несколько результатов | Да: `BindingsSet` и ветви интерпретатора | Да, с identity и evidence каждого результата |
| identity | Структурное равенство atom; identity space по адресу | Immutable ID occurrence отдельно от формы и extent |
| intension | Структура выражения/правила | Отдельный путь построения, не identity и не extent |
| extension | Результат match/eval | Точная проекция entity в выбранном context |
| context | Выбранный `Space`; внешние DAS contexts | Индекс с явно заданными morphisms/restrictions |
| provenance | Можно закодировать atoms; не результат ядра | Машинно-зависимый evidence/derivation DAG |
| revision | `add/remove/replace`, пользовательские правила | Инвалидация зависимого вывода с сохранением истории |
| equality | Структура atom и правила `(= ...)` | `EqualAt(a,b,p)` отдельно от entity equality |
| external computation | Grounded executable Rust objects | Явный oracle с provenance и детерминированным replay |
| типы | Запрашиваемые `(: atom type)` facts | Typed interfaces/ports плюс предметные types |

## Hyperon против killer test

Тест можно **закодировать** в MeTTa, если заранее добавить явные wrappers:

```text
(entity a intension-a)
(entity b intension-b)
(projection a p ((0 0) (1 1)) evidence-a-p)
(projection b p ((0 0) (1 1)) evidence-b-p)
```

Но это будет пользовательская модель контракта, а не гарантия Hyperon. Без
таких wrappers возникают три принципиальные дыры:

1. одинаково записанные atoms не имеют двух обязательных occurrence IDs;
2. совпадение результатов в `p` не создаёт само по себе локальное
   `EqualAt(a,b,p)` с evidence и запретом глобальной конгруэнции;
3. удаление основания не вычисляет автоматически транзитивную инвалидизацию
   зависимых projection/metaedge с сохранением исторических записей.

Именно поэтому killer test остаётся полезным: он не спрашивает, можно ли
*описать* желаемую семантику в универсальном языке. Он проверяет, является ли
она неустранимым контрактом ядра и сохраняют ли её оптимизации.

Отдельный будущий differential experiment должен реализовать этот же конечный
мир в чистой MeTTa без grounded-кода. В отчёте надо разделить:

- что Hyperon сохраняет нативно;
- что требует явного пользовательского ID/evidence protocol;
- что невозможно получить без внешнего состояния или нового интерпретатора.

## Что стоит перенять

1. **Малое интерпретируемое ядро.** Правила и план исполнения не должны
   растворяться в большом наборе специальных Rust-проходов.
2. **First-class spaces.** Хранилище как значение удобно для явной передачи
   вычислительного окружения, даже если agl задаст ему более строгую
   context-семантику.
3. **Многоветочный результат.** Альтернативы должны быть нормальным значением,
   а не исключением или произвольным первым совпадением.
4. **Разделение symbolic matching и grounded boundary.** В agl boundary нужно
   дополнить обязательными входами, версией, evidence и replay record.
5. **Сменные реализации Space.** Индекс, распределённое хранилище и генератор
   не должны определять предметную семантику.

## Что нельзя переносить без исправления

1. **Универсальный `Atom` как единственный identity layer.** Он стирает
   различие proposition, occurrence, projection и evidence.
2. **Структурное equality как предметное тождество.** Оно не выдерживает
   одинаковых extents разных построений и одинаковых записей разных источников.
3. **Grounded operation без журнала.** Иначе детерминизм, объяснимость и отзыв
   основания заканчиваются на границе Rust.
4. **Слово metagraph вместо законов.** Вложенность выражений ещё не доказывает
   open-hypergraph composition, DPO rewriting или indexed semantics.
5. **Типизация как необязательная аннотация там, где нужен kernel invariant.**
   `%Undefined%` полезен для исследования, но не доказывает корректность
   интерфейсной композиции.

## Вывод для проекта

Hyperon снимает претензию на новизну общих фраз «всё есть отношение»,
«программа является данными» и «вычисление есть переписывание». Это уже
реальная инженерная линия со зрелым прототипом. Но он одновременно делает
точнее возможную собственную ставку agl:

> вычисляемой единицей является не структурный терм сам по себе, а устойчивое
> occurrence отношения, чьи intension, context-indexed projections и evidence
> можно независимо запрашивать, пересматривать и использовать как endpoints.

Это пока инженерная гипотеза о полезном представлении мышления, а не модель
человеческой когнитивной архитектуры и не новый calculus. Её ближайшее
доказательство — прохождение identity/extent killer test. Если для прохождения
достаточно тонкого явного protocol поверх MeTTa и он не проигрывает по
простоте, agl следует стать профилем/слоем над готовым движком. Если же
Hyperon постоянно требует внешнего состояния и специальных grounded rules,
собственное маленькое ядро agl получает проверяемое обоснование.

## Следующее ограниченное действие

Не переносить Hyperon в кодовую базу и не начинать вторую общую
реструктуризацию. После реализации локального killer test создать отдельную
ветку `experiment/hyperon-killer-baseline` от принятого checkpoint и повторить
тот же мир в MeTTa. Критерий решения заранее:

- **профиль над Hyperon**, если identity/evidence/revision выражаются коротким
  чистым MeTTa protocol и проверяются запросами;
- **собственное ядро**, если эти свойства требуют host-side ID store,
  imperative callbacks или форка интерпретатора;
- **гибрид**, если Hyperon годится как исследовательский rewrite frontend, но
  agl journal остаётся authoritative semantic store.
