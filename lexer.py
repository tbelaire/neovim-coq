from collections import namedtuple
import re


Token = namedtuple('Token', ['value', 'line', 'col', 'end_line', 'end_col'])

NON_SPACE_RE = re.compile(r'\S')
COMMENT_OPEN_RE = re.compile(r'\(\*')
COMMENT_BOUNDARY_RE = re.compile(r'\(\*|\*\)')
STRING_DELIM_RE = re.compile(r'\\"|"')
# Important delimiters that cause changes in parser state: begin comment, begin
# string, and period followed by space (but not "..", which appears inside some
# tactic commands)
DELIM_RE = re.compile(r'\(\*|"|(?<!\.)\.($|\s)')
# Tactic  bullets, which stand alone as commands.
BULLET_RE = re.compile(r'([-+*]{1,3}|[{}])($|\s)')

class Lexer(object):
    def __init__(self, buf):
        self._buf = buf
        self._line = 0
        self._col = 0

    def pull(self):
        self.skip_boring()
        if self.at_eof():
            return None

        start_line, start_col = self._line, self._col
        if self.consume(BULLET_RE) is not None:
            pass
        else:
            while True:
                s = self.consume_until(DELIM_RE)
                if s is None:
                    return None
                elif s == '(*':
                    self.skip_comment_body()
                elif s == '"':
                    self.skip_string_body()
                elif s.startswith('.'):
                    # Consume only the actual dot.
                    self._col -= len(s) - 1
                    break
                else:
                    assert False, 'unreachable: bad delimiter %r' % s
        end_line, end_col = self._line, self._col

        lines = self._buf[start_line : end_line + 1]
        if start_line == end_line:
            value = lines[0][start_col : end_col]
        else:
            first = lines[0][start_col:]
            mid = lines[1:-1]
            last = lines[-1][:end_col]
            value = '\n'.join([first] + mid + [last])

        return Token(value, start_line, start_col, end_line, end_col)

    def pull_all(self):
        while True:
            token = self.pull()
            if token is None:
                break
            yield token

    def pull_until(self, line, col):
        while True:
            token = self.pull()
            if token is None or token.end_line > line or \
                    (token.end_line == line and token.end_col > col + 1):
                break
            yield token

    def reset(self):
        self._line = 0
        self._col = 0

    def at_eof(self):
        return self._line >= len(self._buf)

    def consume(self, r):
        if self._line >= len(self._buf):
            return None

        line = self._buf[self._line]
        if self._col >= len(line):
            return None

        m = r.match(line, self._col)
        if m is not None:
            self._col = m.end()
            return m.group()
        else:
            return None

    def consume_until(self, r):
        # Note that if self._buf is an actual buffer, all operations will require an RPC roundtrip,
        # so we should avoid extra operations whenever possible.
        num_lines = len(self._buf)
        while self._line < num_lines:
            line = self._buf[self._line]
            if self._col < len(line):
                m = r.search(line, self._col)
                if m is not None:
                    self._col = m.end()
                    return m.group()
            self._line += 1
            self._col = 0
        return None

    def lookahead(self, r):
        s = self.consume(r)
        if s is not None:
            self._col -= len(s)
        return s

    def next(self):
        if self._line >= len(self._buf):
            return None

        line = self._buf[self._line]
        if self._col >= len(line):
            return None

        return line[self._col]

    def skip_boring(self):
        '''Skip over boring things like whitespace and comments.'''
        self.skip_space()
        while self.consume(COMMENT_OPEN_RE):
            self.skip_comment_body()
            self.skip_space()

    def skip_space(self):
        s = self.consume_until(NON_SPACE_RE)
        if self._col > 0:
            self._col -= 1
        # Otherwise, we are at EOF (col 0 of line `len(buf) + 1`).

    def skip_comment_body(self):
        depth = 1
        while depth > 0:
            s = self.consume_until(COMMENT_BOUNDARY_RE)
            if s is None:
                # Reached EOF
                return
            elif s == '(*':
                depth += 1
            elif s == '*)':
                depth -= 1
            else:
                assert False, 'unreachable: bad comment boundary'

    def skip_string_body(self):
        while True:
            s = self.consume_until(STRING_DELIM_RE)
            if s == '\\"':
                continue
            elif s == '"':
                return
            else:
                assert False, 'unreachable: bad string part'
