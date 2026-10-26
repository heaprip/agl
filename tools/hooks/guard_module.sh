#!/bin/sh
# PreToolUse hook on Write: a new .rs file under src/ or examples/ needs its
# row in docs/modules.md first, or it is a second calculator.
root="$(cd "$(dirname "$0")/../.." && pwd)"
path=$(jq -r '.tool_input.file_path // empty')
case "$path" in
  "$root"/src/*.rs|"$root"/examples/*.rs) ;;
  *) exit 0 ;;
esac
[ -e "$path" ] && exit 0
rel=${path#"$root"/}
grep -qF "| \`$rel\`" "$root/docs/modules.md" && exit 0
jq -n --arg r "$rel" '{hookSpecificOutput: {hookEventName: "PreToolUse", permissionDecision: "deny",
  permissionDecisionReason: ("Новый модуль " + $r + " не зарегистрирован в docs/modules.md. Сначала строка: объект спецификации, что переиспользует, почему отдельный, сквозной тест. Если ответа на «почему отдельный» нет — расширь существующий модуль.")}}'
