#!/bin/sh
# SessionStart hook (startup, resume, clear, compact): puts the current state,
# the principles and the work order back into context, so a new or compacted
# session does not start from memory.
cd "$(dirname "$0")/../.." || exit 0
echo "=== agl: контекст сессии (хук tools/hooks/session_context.sh) ==="
echo
cat docs/now.md
echo
echo "=== docs/principles.md ==="
echo
cat docs/principles.md
echo
# The author's concept graph is local (not in git); print its nodes and edges
# so a compacted session checks proposals against it, not against memory.
if [ -f local/concept-graph.md ]; then
  echo "=== local/concept-graph.md (узлы и рёбра) ==="
  echo
  sed -n '/^## Узлы/,/^## Проверка атласа/p' local/concept-graph.md | sed '$d'
  sed -n '/^## Обновления/,$p' local/concept-graph.md
  echo
fi
cat <<'CARD'
=== Порядок работы ===
- До предложения или кода прочитать целиком: docs/now.md, docs/plan.md,
  docs/principles.md, docs/decisions.md (и docs/spec/, когда появится).
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
- Предложение помощника — гипотеза в docs/hypotheses.md (с H77), «не
  принято»; в decisions.md — только по прямому слову автора, безлично;
  молчание — не согласие.
- Высказывания автора — только в CLAUDE.local.md / local/ (решение 30).
- Закончил задачу — обнови docs/now.md в том же коммите.
- Перед ответом автору по существу — сверить с графом понятий выше и с
  хвостом CLAUDE.local.md («Где остановились»), а не со сводкой сжатия.
CARD
