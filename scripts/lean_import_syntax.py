"""Shared lexical helpers for one-line Lean import-only files."""

from __future__ import annotations

import re

NAME_SEGMENT = r"[A-Za-z_][A-Za-z0-9_']*"
MODULE_NAME = rf"{NAME_SEGMENT}(?:\.{NAME_SEGMENT})*"
IMPORT_COMMAND_RE = re.compile(rf"import\s+({MODULE_NAME})")
RAW_STRING_START_RE = re.compile(r'r(#+)?"')
CHAR_LITERAL_RE = re.compile(r"'(?:\\[^'\n]+|[^'\\\n])'")


def strip_lean_comments(source: str, *, mask_strings: bool = False) -> tuple[str, str | None]:
    """Remove comments outside string literals; optionally mask string contents.

    Masking preserves newlines and quotes, so strings cannot manufacture commands
    or make a declaration-bearing module appear to be an import-only aggregator.
    """
    output: list[str] = []
    index = 0
    block_depth = 0
    while index < len(source):
        pair = source[index:index + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    output.append("\n")
                index += 1
        elif source[index] == "«":
            end = source.find("»", index + 1)
            if end == -1:
                return "".join(output), "unterminated escaped identifier"
            output.append(source[index:end + 1])
            index = end + 1
        elif (source[index] == "'" and
              (index == 0 or not (source[index - 1].isalnum() or source[index - 1] in "_'")) and
              (char := CHAR_LITERAL_RE.match(source, index))):
            output.append("' '" if mask_strings else char.group())
            index = char.end()
        elif source[index] == "r" and (raw := RAW_STRING_START_RE.match(source, index)):
            delimiter = '"' + (raw.group(1) or "")
            end = source.find(delimiter, raw.end())
            if end == -1:
                return "".join(output), "unterminated raw string literal"
            end += len(delimiter)
            literal = source[index:end]
            output.append('"' + "".join("\n" if c == "\n" else " " for c in literal) + '"'
                          if mask_strings else literal)
            index = end
        elif source[index] == '"':
            output.append('"')
            index += 1
            closed = False
            while index < len(source):
                character = source[index]
                if character == '"':
                    output.append('"')
                    index += 1
                    closed = True
                    break
                if character == "\\" and index + 1 < len(source):
                    escaped = source[index:index + 2]
                    output.append("".join("\n" if c == "\n" else " " for c in escaped)
                                  if mask_strings else escaped)
                    index += 2
                else:
                    output.append(" " if mask_strings and character != "\n" else character)
                    index += 1
            if not closed:
                return "".join(output), "unterminated string literal"
        elif pair == "/-":
            # A comment separates tokens even when it has no surrounding spaces.
            output.append(" ")
            block_depth = 1
            index += 2
        elif pair == "--":
            newline = source.find("\n", index + 2)
            if newline == -1:
                index = len(source)
            else:
                output.append("\n")
                index = newline + 1
        else:
            output.append(source[index])
            index += 1
    if block_depth:
        return "".join(output), "unterminated block comment"
    return "".join(output), None


def pure_import_modules(source: str) -> tuple[list[str], str | None]:
    """Return modules in a nonempty import-only source, or its rejection reason."""
    uncommented, error = strip_lean_comments(source)
    if error is not None:
        return [], error
    commands = [line.strip() for line in uncommented.splitlines() if line.strip()]
    if not commands:
        return [], "file contains no import commands"
    modules: list[str] = []
    for line_number, command in enumerate(commands, start=1):
        match = IMPORT_COMMAND_RE.fullmatch(command)
        if match is None:
            return [], (
                "contains non-import Lean code after comments are removed "
                f"(command {line_number}: {command!r})"
            )
        modules.append(match.group(1))
    return modules, None
