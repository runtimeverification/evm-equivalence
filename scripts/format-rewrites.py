import sys
from collections.abc import Iterable, Iterator
from io import StringIO


def main() -> None:
    for line in sys.stdin:
        print(_process_line(line.rstrip()))


def _process_line(line: str) -> str:
    prefix = "  |"
    if line.startswith(prefix):
        tokens = _tokenize(line)
        return CtorWriter(tokens).print()
    return line


def _tokenize(text: str) -> list[str]:
    import re

    special = '|'.join(['{', '}', r'\(', r'\)', r'\|', ':=', ':', ','])
    segment = r'(«[^»]+»|[^{}()|:,«»\.\s]+)'
    other = fr'{segment}(\.{segment})*'
    pattern = '|'.join([special, other])
    return list(m.group() for m in re.finditer(pattern, text))


class CtorWriter:
    io: StringIO
    it: Iterator[str]
    la: str
    indent: int

    def __init__(self, tokens: Iterable[str]):
        self.io = StringIO()
        self.it = iter(tokens)
        self.la = next(self.it, "")
        self.indent = 4

    def _next(self) -> None:
        if not self.la:
            raise AssertionError(f"Unexpected EOF, buffer:\n{self.io.getvalue()}")
        self.io.write(self.la)
        self.la = next(self.it, "")

    def _space(self) -> None:
        self.io.write(" ")

    def _newline(self) -> None:
        self.io.write("\n" + " " * self.indent)

    def _indent(self) -> None:
        self.indent += 2

    def _dedent(self) -> None:
        self.indent -= 2

    def print(self) -> str:
        self.io.write("  ")
        assert self.la == "|"
        self._next()  # '|'
        self._space()
        self._next()  # identifier
        self._newline()
        while self.la != ":":
            self._binder()
            self._newline()
        self._next()  # ':'
        self._space()
        assert self.la == "Rewrites"
        self._term()
        assert self.la == ""
        return self.io.getvalue()

    def _binder(self) -> None:
        closing = "}" if self.la == "{" else ")"
        self._next()  # opening paren
        while self.la != ":":
            self._next()  # identifier
            self._space()
        self._next()  # ':'
        self._space()
        self._term()  # type
        assert self.la == closing
        self._next()  # closing paren

    def _structure(self) -> None:
        assert self.la == "{"
        self._next()  # {

        self._indent()
        if self.la == "val":
            self._space()
        else:
            self._newline()

        self._field()
        while self.la == ",":
            self._next()  # ','
            self._newline()
            self._field()

        assert self.la == "}"
        self._space()
        self._dedent()
        self._next()

    def _field(self) -> None:
        self._next()  # identifier
        self._space()
        assert self.la == ":="
        self._next()  # :=
        self._space()
        self._term()

    def _term(self) -> None:
        if self.la == "(":
            self._next()  # '('
            if self.la == ")":
                self._next()
            else:
                self._term()
                while self.la != ")":
                    self._space()
                    self._term()
                self._next()  # ')'
        elif self.la == "{":
            self._structure()
        else:
            self._next()

        while self.la not in (")", "}", ",", ""):
            self._space()
            self._term()


if __name__ == "__main__":
    main()
