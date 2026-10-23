#!/usr/bin/env python3
"""LLM writes .agl, the kernel checks it, the LLM gets the kernel's report back.

    python3 tools/llm_dsl.py prompt            # write docs/dsl/prompt.md only
    python3 tools/llm_dsl.py run [SAMPLES]     # sample, check, feed back
    python3 tools/llm_dsl.py teach             # hidden teacher on recorded runs

Every call is recorded in docs/dsl/calls/<sha256 of request>.json and replayed
from there when the same request is made again, so a rerun costs nothing and
gives the same files. The network is touched only for unrecorded requests.

The key is read from ROUTERAI_KEY / ROUTERAI_BASE_URL in the trading bot's
.env (shared key; never printed).
"""

import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "dsl")
CALLS = os.path.join(OUT, "calls")
ENV = "/Users/user/Projects/python/trading/.env"
LIB = os.path.join(ROOT, "cases", "trunk", "lib.agl")
AGL = os.path.join(ROOT, "target", "release", "agl")

MODEL = "deepseek/deepseek-v4.1-flash-1017"
PROVIDER = {"order": ["deepseek"], "allow_fallbacks": False}
TEMPERATURE = 1.0  # vendor recommendation
MAX_TOKENS = 100_000
EFFORT = "high"
ROUNDS = 3  # first answer plus two rounds of kernel feedback
BUDGET_RUB = 30.0

TEXT = """\
Without oxygen, muscle cells regenerate NAD+ by lactic acid fermentation:
lactate dehydrogenase reduces pyruvate to lactate, oxidizing NADH to NAD+.
Glycolysis turns one glucose into two pyruvate, so two lactate are formed per
glucose and the net yield stays at two ATP. Yeast use alcohol fermentation
instead: pyruvate decarboxylase removes carbon dioxide from pyruvate, giving
acetaldehyde, and alcohol dehydrogenase reduces acetaldehyde to ethanol with
NADH. Neither kind of fermentation needs oxygen, and neither yields ATP beyond
glycolysis. When oxygen is present, NADH is reoxidized by the respiratory chain
instead."""

TASK = f"""\
Задача. Переведи текст ниже в файл `.agl`.

Требования:
1. Первая строка файла — `include lib.agl` (ствол выше подключается целиком).
2. Всё, что ты утверждаешь сам, — со статусом `[llm_proposal]`.
3. Если вещество или реакция уже есть в стволе, используй их идентификаторы.
   Для нового вещества дай идентификатор ChEBI в виде `CHEBI_<номер>`, если
   знаешь его. Чтобы ядро могло проверить баланс реакции, у каждого участника
   должен быть известен состав (`composition`, `formula_known`).
4. Каждое утверждение текста, которое можно проверить, запиши запросом
   `query ... expect ...`.
5. Ядро проверит файл: разбор, линтер, противоречия со стволом, баланс каждой
   реакции, которую ты объявишь (`reaction(id: ...)`), и твои запросы.

Ответ — один блок кода ```agl с файлом целиком. Пояснения, если нужны, — после
блока, коротко.

Текст:

{TEXT}
"""

FEEDBACK = """\
Ядро проверило файл. Номера строк — в твоём файле.

```
{report}
```

Исправь ошибки и пришли файл целиком, снова одним блоком ```agl."""


def read(rel):
    with open(os.path.join(ROOT, rel), encoding="utf-8") as f:
        return f.read()


def prompt_messages():
    system = (
        "Ты пишешь на языке .agl. Это новый язык: в обучающих данных его нет. "
        "Ниже — его описание, примеры и ствол знаний, к которому подключается "
        "твой файл. Пиши только то, что описано; если чего-то в языке нет, "
        "скажи об этом после блока кода."
    )
    parts = [
        "# Описание языка (docs/impl/poc.md)\n\n" + read("docs/impl/poc.md"),
        "# Пример: плоскости и исключения (cases/gas-exchange.agl)\n\n```agl\n"
        + read("cases/gas-exchange.agl") + "```",
        "# Пример: мир казуса кислорода (cases/trunk/oxygen-world.agl)\n\n```agl\n"
        + read("cases/trunk/oxygen-world.agl") + "```",
        "# Пример: правила и запросы (cases/trunk/oxygen.agl)\n\n```agl\n"
        + read("cases/trunk/oxygen.agl") + "```",
        "# Ствол: lib.agl\n\n```agl\n" + read("cases/trunk/lib.agl") + "```",
        "# Ствол: data/metabolism.agl (подключается из lib.agl)\n\n```agl\n"
        + read("data/metabolism.agl") + "```",
        TASK,
    ]
    return [{"role": "system", "content": system}, {"role": "user", "content": "\n\n".join(parts)}]


def env():
    vals = {}
    with open(ENV, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"\s*(ROUTERAI_KEY|ROUTERAI_BASE_URL)\s*=\s*(.*)", line)
            if m:
                vals[m.group(1)] = m.group(2).strip().strip("'\"")
    return vals["ROUTERAI_KEY"], vals["ROUTERAI_BASE_URL"].rstrip("/")


def call(messages, seed):
    body = {
        "model": MODEL,
        "provider": PROVIDER,
        "messages": messages,
        "temperature": TEMPERATURE,
        "max_tokens": MAX_TOKENS,
        "reasoning": {"effort": EFFORT},
        "seed": seed,
        "usage": {"include": True},
    }
    raw = json.dumps(body, ensure_ascii=False, sort_keys=True)
    h = hashlib.sha256(raw.encode()).hexdigest()
    path = os.path.join(CALLS, h + ".json")
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            return json.load(f)["response"], h, True
    key, base = env()
    req = urllib.request.Request(
        base + "/chat/completions",
        data=raw.encode(),
        headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=1800) as r:
        resp = json.load(r)
    os.makedirs(CALLS, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump({"request": body, "response": resp}, f, ensure_ascii=False, indent=1)
    return resp, h, False


def expanded_len(path, stack=()):
    """Lines that `include path` expands to, as the kernel's parser counts them."""
    n = 0
    with open(path, encoding="utf-8") as f:
        for line in f.read().splitlines():
            rel = line.strip()
            if rel.startswith("include "):
                n += expanded_len(os.path.join(os.path.dirname(path), rel[8:].strip()))
            else:
                n += 1
    return n


def extract(content):
    blocks = re.findall(r"```agl\n(.*?)```", content, re.S)
    return blocks[-1] if blocks else None


def check(code, path):
    """Writes the candidate, appends balance checks, runs the kernel.

    Returns (accepted, report for the model, summary)."""
    lines = [l for l in code.splitlines() if not l.strip().startswith("include ")]
    rel = os.path.relpath(LIB, os.path.dirname(path))
    body = [f"include {rel}"] + lines
    rx = sorted(set(re.findall(r"^\s*fact\s+\S+:\s*reaction\(id:\s*([A-Za-z0-9_]+)\)", "\n".join(lines), re.M)))
    if rx:
        body += ["", "# --- harness: balance of every declared reaction ---"]
        body += [f"query balanced_all(reaction: {r}) @ expect yes" for r in rx]
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(body) + "\n")
    offset = expanded_len(LIB)
    res = subprocess.run([AGL, path], capture_output=True, text=True)
    out = res.stdout + res.stderr

    def local(m):
        k = int(m.group(1))
        return f"line {k - offset + 1}" if k > offset else f"trunk line {k}"

    out = re.sub(r"line (\d+)", local, out)
    out = "\n".join(l for l in out.splitlines() if not l.startswith("== "))
    s = {
        "parse_error": "parse error" in out,
        "lint_errors": len(re.findall(r"^Error line", out, re.M)),
        "warnings": len(re.findall(r"^Warning line", out, re.M)),
        "errors": len(re.findall(r"^error:", out, re.M)),
        "conflicts": len(re.findall(r"^conflict", out, re.M)),
        "pass": len(re.findall(r"^PASS", out, re.M)),
        "fail": len(re.findall(r"^FAIL", out, re.M)),
        "reactions": rx,
    }
    s["accepted"] = not (s["parse_error"] or s["lint_errors"] or s["errors"] or s["conflicts"] or s["fail"])
    return s["accepted"], out, s


# Hidden teacher: expectations from the text that the model never sees. They
# must not depend on the model's names, so the teacher computes net results
# itself from trunk relations (step, participates, member) and the example's
# system/uses, and judges viability against two environments given as data,
# not as planes (the model's planes are its own).
TEACHER = """
# --- hidden teacher ---
fact teacher_env_name_a: teacher_env_name(env: anoxic) @ [textbook]
fact teacher_env_name_o: teacher_env_name(env: oxic) @ [textbook]
fact teacher_a1: teacher_env(env: anoxic, species: CHEBI_4167) @ [textbook]
fact teacher_a2: teacher_env(env: anoxic, species: CHEBI_456216) @ [textbook]
fact teacher_a3: teacher_env(env: anoxic, species: CHEBI_43474) @ [textbook]
fact teacher_a4: teacher_env(env: anoxic, species: CHEBI_15378) @ [textbook]
fact teacher_a5: teacher_env(env: anoxic, species: CHEBI_15377) @ [textbook]
fact teacher_o1: teacher_env(env: oxic, species: CHEBI_4167) @ [textbook]
fact teacher_o2: teacher_env(env: oxic, species: CHEBI_456216) @ [textbook]
fact teacher_o3: teacher_env(env: oxic, species: CHEBI_43474) @ [textbook]
fact teacher_o4: teacher_env(env: oxic, species: CHEBI_15378) @ [textbook]
fact teacher_o5: teacher_env(env: oxic, species: CHEBI_15377) @ [textbook]
fact teacher_o6: teacher_env(env: oxic, species: CHEBI_15379) @ [textbook]

rule teacher_top strict @: teacher_top(species: ?x) <-
    participates(species: ?x), ?k = count(?p) over (is_a(species: ?x, parent: ?p)), ?k = 0
rule teacher_net strict @: teacher_net(system: ?s, species: ?x, value: ?v) <-
    system(id: ?s), teacher_top(species: ?x),
    ?v = sum(?u * ?d * ?t * ?sv * ?c) over (uses(system: ?s, pathway: ?p, times: ?u),
                                           member(species: ?y, of: ?x),
                                           step(pathway: ?p, reaction: ?r, direction: ?dir, times: ?t),
                                           dir_value(direction: ?dir, value: ?d),
                                           participates(reaction: ?r, species: ?y, side: ?side, coeff: ?c),
                                           side_value(side: ?side, value: ?sv))
rule teacher_consumed strict @: teacher_consumed(system: ?s, species: ?x) <-
    teacher_net(system: ?s, species: ?x, value: ?v), ?v < 0
rule teacher_viable strict @: teacher_viable(system: ?s, env: ?e) <-
    system(id: ?s), teacher_env_name(env: ?e),
    ?c = count(?x) over (teacher_consumed(system: ?s, species: ?x)),
    ?a = count(?x) over (teacher_consumed(system: ?s, species: ?x), teacher_env(env: ?e, species: ?x)),
    ?c = ?a

# Lactate fermentation: per glucose 2 lactate, 2 ATP, NAD+/NADH return to zero, no O2 needed.
rule teacher_lactate strict @: teacher_claim(claim: lactate_fermentation) <-
    teacher_net(system: ?s, species: CHEBI_4167, value: -1),
    teacher_net(system: ?s, species: CHEBI_16651, value: 2),
    teacher_net(system: ?s, species: CHEBI_30616, value: 2),
    teacher_net(system: ?s, species: CHEBI_57540, value: 0),
    teacher_net(system: ?s, species: CHEBI_57945, value: 0),
    teacher_viable(system: ?s, env: anoxic)
# Alcohol fermentation: per glucose 2 ethanol, 2 CO2, 2 ATP, NAD+/NADH zero, no O2 needed.
rule teacher_alcohol strict @: teacher_claim(claim: alcohol_fermentation) <-
    teacher_net(system: ?s, species: CHEBI_4167, value: -1),
    teacher_net(system: ?s, species: CHEBI_16236, value: 2),
    teacher_net(system: ?s, species: CHEBI_16526, value: 2),
    teacher_net(system: ?s, species: CHEBI_30616, value: 2),
    teacher_net(system: ?s, species: CHEBI_57540, value: 0),
    teacher_net(system: ?s, species: CHEBI_57945, value: 0),
    teacher_viable(system: ?s, env: anoxic)
# Respiration: NADH reoxidized with O2; viable with oxygen, not without.
rule teacher_resp strict @: teacher_claim(claim: respiratory_chain) <-
    teacher_net(system: ?s, species: CHEBI_57540, value: 0),
    teacher_net(system: ?s, species: CHEBI_57945, value: 0),
    teacher_net(system: ?s, species: CHEBI_15379, value: ?o), ?o < 0,
    teacher_viable(system: ?s, env: oxic),
    ?k = count(?e) over (teacher_viable(system: ?s, env: anoxic)), ?k = 0
"""

CLAIMS = ["lactate_fermentation", "alcohol_fermentation", "respiratory_chain"]


def teach(agl_path):
    """Runs the hidden teacher on a checked candidate in {} and in each plane
    the candidate declares. A claim holds if it holds in some plane."""
    with open(agl_path, encoding="utf-8") as f:
        src = f.read()
    planes = [""] + re.findall(r"^\s*plane\s+(\w+)\s*=", src, re.M)
    queries = [f"query teacher_claim(claim: {c}) @ {p}".rstrip() for c in CLAIMS for p in planes]
    tpath = agl_path[: -len(".agl")] + ".teacher.agl"
    with open(tpath, "w", encoding="utf-8") as f:
        f.write(src + TEACHER + "\n" + "\n".join(queries) + "\n")
    res = subprocess.run([AGL, tpath], capture_output=True, text=True)
    out = res.stdout + res.stderr
    verdict = {}
    for c in CLAIMS:
        hits = re.findall(rf"teacher_claim\(claim: {c}\) @ (\{{[^}}]*\}}) → yes", out)
        verdict[c] = hits[0] if hits else None
    trouble = [l for l in out.splitlines() if "teacher" in l and not l.startswith("    ")
               and (l.startswith("conflict") or l.startswith("error") or "Error" in l)]
    if "parse error" in out:
        trouble.append(out.strip().splitlines()[-1])
    os.remove(tpath)
    with open(agl_path[: -len(".agl")] + ".teacher.txt", "w", encoding="utf-8") as f:
        f.write(json.dumps({"claims": verdict, "trouble": trouble}, ensure_ascii=False, indent=1) + "\n")
    return verdict, trouble


def teach_all():
    for sdir in sorted(os.listdir(os.path.join(OUT, "runs"))):
        d = os.path.join(OUT, "runs", sdir)
        for name in sorted(os.listdir(d)):
            if re.fullmatch(r"r\d+\.agl", name):
                v, t = teach(os.path.join(d, name))
                score = sum(1 for x in v.values() if x)
                print(f"{sdir}/{name}: {score}/{len(v)}", {k: bool(x) for k, x in v.items()}, t or "")


def cost(resp):
    return float((resp.get("usage") or {}).get("cost") or 0.0)


def run(samples):
    msgs0 = prompt_messages()
    spent = 0.0
    summary = []
    for sample in range(1, samples + 1):
        msgs = list(msgs0)
        sdir = os.path.join(OUT, "runs", f"s{sample}")
        os.makedirs(sdir, exist_ok=True)
        log = []
        for rnd in range(ROUNDS):
            if spent > BUDGET_RUB:
                print(f"budget {BUDGET_RUB} ₽ reached, stop")
                break
            resp, h, cached = call(msgs, seed=sample)
            spent += 0 if cached else cost(resp)
            msg = resp["choices"][0]["message"]
            content = msg.get("content") or ""
            u = resp.get("usage") or {}
            entry = {
                "round": rnd,
                "call": h,
                "cached": cached,
                "provider": resp.get("provider"),
                "prompt_tokens": u.get("prompt_tokens"),
                "completion_tokens": u.get("completion_tokens"),
                "reasoning_tokens": (u.get("completion_tokens_details") or {}).get("reasoning_tokens"),
                "cached_tokens": (u.get("prompt_tokens_details") or {}).get("cached_tokens"),
                "cost": cost(resp),
                "finish": resp["choices"][0].get("finish_reason"),
            }
            with open(os.path.join(sdir, f"r{rnd}.md"), "w", encoding="utf-8") as f:
                f.write(content)
            code = extract(content)
            if code is None:
                entry["check"] = {"accepted": False, "no_code": True}
                report = "Ответ без блока ```agl."
            else:
                ok, report, s = check(code, os.path.join(sdir, f"r{rnd}.agl"))
                entry["check"] = s
                entry["teacher"] = teach(os.path.join(sdir, f"r{rnd}.agl"))[0]
                with open(os.path.join(sdir, f"r{rnd}.kernel.txt"), "w", encoding="utf-8") as f:
                    f.write(report + "\n")
            log.append(entry)
            print(json.dumps({"sample": sample, **entry}, ensure_ascii=False))
            if entry["check"].get("accepted"):
                break
            msgs = msgs + [
                {"role": "assistant", "content": content},
                {"role": "user", "content": FEEDBACK.format(report=report.strip())},
            ]
        with open(os.path.join(sdir, "log.json"), "w", encoding="utf-8") as f:
            json.dump(log, f, ensure_ascii=False, indent=1)
        summary.append(log)
    print(f"spent this run: {spent:.2f} ₽")


def write_prompt():
    os.makedirs(OUT, exist_ok=True)
    m = prompt_messages()
    with open(os.path.join(OUT, "prompt.md"), "w", encoding="utf-8") as f:
        f.write("<!-- GENERATED by tools/llm_dsl.py prompt — do not edit. -->\n\n")
        f.write("## system\n\n" + m[0]["content"] + "\n\n## user\n\n" + m[1]["content"] + "\n")
        f.write("\n## Обратная связь (шаблон)\n\n" + FEEDBACK + "\n")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "prompt"
    write_prompt()
    if cmd == "teach":
        teach_all()
    elif cmd == "run":
        run(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
