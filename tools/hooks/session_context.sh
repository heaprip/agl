#!/bin/sh
# SessionStart hook (startup, resume, clear, compact): puts the reading order
# and the current state back into context, so a new or compacted session does
# not start from memory. Output must stay small (~10 KB): longer output is
# replaced by a short preview. The card goes first so it survives even then;
# the model itself is read with the Read tool.
cd "$(dirname "$0")/../.." || exit 0
echo "=== agl: контекст сессии (хук tools/hooks/session_context.sh) ==="
echo
cat <<'CARD'
=== Порядок работы ===
- ПЕРВЫМ ДЕЛОМ прочитать самому целиком (Read, не grep): docs/model.md
  (модель и поправки), docs/course.md, docs/decisions.md; затем
  local/concept-graph.md, local/hypotheses.md и хвост CLAUDE.local.md (от
  «Сжатие документов»). Если есть промт в local/prompts/ — по нему.
  Grep — не чтение. Сказать честно, что прочитано, а что нет.
- Роли: автор решает и одобряет; главная сессия говорит с автором и ставит
  поручения, сама не исполняет; agl-worker исполняет одно поручение;
  agl-auditor проверяет до коммита (.claude/agents/).
- Новый модуль — сначала строка в docs/modules.md; tests/registry.rs это
  проверяет.
- Критерий приёмки — из спецификации, записанной до кода; код прошлого
  (legacy-v0) — не материал и не эталон.
- Эксперимент — ветка от контрольной точки; независимые ветки не наследуют
  друг друга; критерий до кода; после выбора — новая контрольная точка
  (решение 24).
- Предложение помощника — гипотеза в local/hypotheses.md (вне git), «не
  принято»; в decisions.md — только по прямому слову автора, безлично;
  молчание — не согласие.
- Высказывания автора — только в CLAUDE.local.md / local/ (решение 30).
- Закончил задачу — обнови docs/course.md, раздел «Сейчас», в том же коммите.
- Перед ответом автору по существу — сверить с local/concept-graph.md и с
  хвостом CLAUDE.local.md («Где остановились»), а не со сводкой сжатия.
CARD
echo
echo "=== docs/course.md: «Сейчас» и «Ждёт автора» ==="
echo
LC_ALL=C awk '/^## /{on = ($0 == "## Сейчас" || $0 == "## Ждёт автора")} on' docs/course.md
echo

