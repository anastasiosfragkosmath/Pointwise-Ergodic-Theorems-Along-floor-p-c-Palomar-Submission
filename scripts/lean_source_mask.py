"""Lean source lexer and forbidden patterns adapted from the project audit."""
from __future__ import annotations
import re
from pathlib import Path

FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"(?<![\w'])sorry(?![\w'])"),
    "admit": re.compile(r"(?<![\w'])admit(?![\w'])"),
    "sorryAx": re.compile(r"(?<![\w'])sorryAx(?![\w'])"),
    "axiom": re.compile(r"(?<![\w'])axiom(?![\w'])"),
    # `constant` is also a common binder/parameter name. Match it as a
    # declaration command, after optional command modifiers and attributes,
    # rather than flagging every use of the identifier.
    "constant": re.compile(
        r"(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|scoped|"
        r"local|partial|nonrec|public)[ \t]+|@\[[^\]\n]*\][ \t\r\n]*)*"
        r"(?P<token>constant)(?![\w'])"
    ),
    "native_decide": re.compile(r"(?<![\w'])native_decide(?![\w'])"),
    "ofReduceBool": re.compile(r"(?<![\w'])ofReduceBool(?![\w'])"),
}

class AuditError(RuntimeError):
    pass

def blank_non_newlines(chars: list[str], start: int, stop: int) -> None:
    for index in range(start, stop):
        if chars[index] not in "\r\n":
            chars[index] = " "

def mask_comments_strings_and_quoted_names(source: str, path: Path) -> str:
    """Mask comments and strings while preserving quoted identifiers and offsets.

    Lean block comments nest. Only the project's literal
    `v!"major.minor.patch"` version strings are accepted among tagged strings;
    other tagged and raw-string forms fail closed.
    """
    chars = list(source)
    index = 0
    size = len(source)
    last_code_char: str | None = None

    while index < size:
        if source.startswith("--", index):
            end = source.find("\n", index + 2)
            if end == -1:
                end = size
            blank_non_newlines(chars, index, end)
            index = end
            continue

        if source.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while index < size and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise AuditError(f"{path}: unterminated nested Lean comment")
            blank_non_newlines(chars, start, index)
            continue

        if source.startswith("«", index):
            start = index
            depth = 1
            index += 1
            while index < size and depth:
                if source.startswith("«", index):
                    depth += 1
                    index += 1
                elif source.startswith("»", index):
                    depth -= 1
                    index += 1
                else:
                    index += 1
            if depth:
                raise AuditError(f"{path}: unterminated quoted identifier")
            # Preserve quoted identifier contents: e.g. «sorryAx» is executable.
            last_code_char = "»"
            continue

        if source[index] == '"':
            # A tag before the string may interpolate executable Lean code.
            # Record it and later allow only the known literal version form.
            is_tagged = last_code_char == "!"
            tag = ""
            if is_tagged:
                tag_end = index - 1
                while tag_end >= 0 and chars[tag_end].isspace():
                    tag_end -= 1
                if tag_end < 0 or chars[tag_end] != "!":
                    raise AuditError(
                        f"{path}:{source.count(chr(10), 0, index) + 1}: "
                        "could not parse tagged string prefix"
                    )
                tag_start = tag_end - 1
                while tag_start >= 0 and (
                    chars[tag_start].isalnum() or chars[tag_start] in "_'"):
                    tag_start -= 1
                tag = "".join(chars[tag_start + 1 : tag_end])
            opening_line = source.count("\n", 0, index) + 1

            before_quote = source[max(0, index - 8) : index]
            if re.search(r"(?:^|[^\w])r#+$", before_quote):
                raise AuditError(
                    f"{path}:{source.count(chr(10), 0, index) + 1}: "
                    "raw string needs an explicit scanner rule"
                )
            if source.startswith('"""', index):
                raise AuditError(
                    f"{path}:{source.count(chr(10), 0, index) + 1}: "
                    "triple-quoted string needs an explicit scanner rule"
                )

            start = index
            index += 1
            content_start = index
            while index < size:
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    content_end = index
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise AuditError(
                    f"{path}: unterminated Lean string literal at offset {start}"
                )
            literal = source[content_start:content_end]
            if is_tagged and not (
                tag == "v" and re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", literal)
            ):
                raise AuditError(
                    f"{path}:{opening_line}: unsupported tagged string "
                    f"{tag!r}; add an explicit scanner rule"
                )
            blank_non_newlines(chars, start, index)
            last_code_char = '"'
            continue

        if source[index].isspace():
            index += 1
            continue

        last_code_char = source[index]
        index += 1

    return "".join(chars)
