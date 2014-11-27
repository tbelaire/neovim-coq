from __future__ import print_function

try:
    import asyncio
except ImportError:
    import trollius as asyncio
from collections import namedtuple
import greenlet
import lxml.etree as ET
import os
import re
import sys
import traceback

import neovim


log = open('fifo', 'w', 1)
sys.stderr = log

real_print = print
def print(*args, **kwargs):
    real_print(*args, file=log, **kwargs)


def make_session():
    #from neovim.msgpack_rpc.event_loop.uv import UvEventLoop
    from neovim.msgpack_rpc.event_loop.asyncio import AsyncioEventLoop
    from neovim.msgpack_rpc.msgpack_stream import MsgpackStream
    from neovim.msgpack_rpc.async_session import AsyncSession
    from neovim.msgpack_rpc.session import Session
    loop = AsyncioEventLoop('stdio')
    msgpack_stream = MsgpackStream(loop)
    async_session = AsyncSession(msgpack_stream)
    session = Session(async_session)
    return (loop, session)




def await(coro):
    task = asyncio.async(coro)

    if task.done():
        return task.result()
    else:
        gr = greenlet.getcurrent()

        def callback(*args):
            if task.cancelled():
                gr.throw(asyncio.CancelledError)

            exc = task.exception()
            if exc is not None:
                gr.throw(exc)

            result = task.result()
            gr.switch(result)

        task.add_done_callback(callback)
        result = gr.parent.switch()
        return result

def defer():
    gr = greenlet.getcurrent()
    def handler():
        gr.switch()
    asyncio.get_event_loop().call_soon_threadsafe(handler)


class VimLock(object):
    """Context manager to ensure a sequence of vim commands executes atomically.  Conceptually,
    consider a lock that ensures exclusive access to vim's state.  Entering the context will block
    (make the current greenlet yield) until the lock is acquired.  Exiting the context will release
    the lock (and yield again).

    In reality, there is no lock.  Exclusivity is ensured by forcing vim to make an `rpcrequest`
    back to this process.  User input processing is blocked until the `rpcrequest` returns.  The
    interior of the `with` block runs during the `rpcrequest` handler.
    """

    """
    Terminology:
     - "target greenlet": the greenlet running the `with the_vim_lock()` block.
     - "dispatch greenlet": the greenlet which invokes `the_vim_lock.dispatch(...)`.
     - "worker greenlet": a greenlet for running background jobs on the event loop.
     - "event loop": the top-level greenlet where the event loop runs.  This is the parent of the
       target and dispatch greenlets.

    The general control flow is as follows:
     1. The target greenlet invokes _enter.
         a. Schedule _enter handler on worker greenlet 1.
         b. Switch from target greenlet to event loop.
     2. Worker greenlet 1 is processed.
         a. Invoke `vim.eval("rpcrequest(...)")`.
         b. Switch from worker greenlet 1 to event loop (to await the completion of `vim.eval`).
     3. Vim sends the `rpcrequest`.  The greenlet handling this request becomes the dispatch
        greenlet, and invokes `the_vim_lock.dispatch`.
         a. Switch from dispatch greenlet to target greenlet, passing the dispatch greenlet.
     4. The target greenlet resumes.  The `with` block finishes running.  The target greenlet
        invokes _exit.
         a. Schedule _exit handler on worker greenlet 2.
         b. Switch from target greenlet to dispatch greenlet.
     5. The dispatch greenlet returns.  Vim's `rpcrequest` terminates.  Worker greenlet 1 resumes.
         a. Terminate worker greenlet 1 (nothing left to do).
     6. Worker greenlet 2 is processed.
         a. Switch from worker greenlet 2 to the target greenlet.  (Worker greenlet 2 is abandoned.)
    """

    def __init__(self, vim):
        self._vim = vim
        self._next_cookie = 0
        self._pending = {}

    def __call__(self):
        return VimLockContext(self)

    def _enter(self):
        cookie = self._next_cookie
        self._next_cookie += 1

        gr = greenlet.getcurrent()
        self._pending[cookie] = gr

        vim = self._vim
        def handler():
            vim.eval('rpcrequest(%d, "locked", %d)' % (vim.channel_id, cookie))

        vim.session.threadsafe_call(handler)
        dispatch_gr = gr.parent.switch()
        return dispatch_gr

    def _exit(self, exc_type, exc_value, traceback, dispatch_gr):
        gr = greenlet.getcurrent()
        def handler():
            if exc_type is not None:
                gr.throw(exc_type, exc_value, traceback)
            else:
                gr.switch()

        self._vim.session.threadsafe_call(handler)
        dispatch_gr.switch()

    def dispatch(self, cookie):
        dispatch_gr = greenlet.getcurrent()
        target_gr = self._pending.pop(cookie)
        target_gr.switch(dispatch_gr)

class VimLockContext(object):
    def __init__(self, owner):
        self._owner = owner
        self._dispatch_gr = None

    def __enter__(self):
        assert self._dispatch_gr is None, \
                'VimLockContext is not reentrant'
        self._dispatch_gr = self._owner._enter()

    def __exit__(self, exc_type, exc_value, traceback):
        self._owner._exit(exc_type, exc_value, traceback, self._dispatch_gr)
        self._dispatch_gr = None
        return None


class XMLStreamParser(object):
    def __init__(self, callback, *args, **kwargs):
        self._callback = callback
        self._depth = 0
        self._builder = ET.TreeBuilder()

        self._parser = ET.XMLParser(*args, target=self, **kwargs)
        self._parser.feed('<fakeroot>')

    def start(self, tag, attrs):
        self._depth += 1
        self._builder.start(tag, attrs)

    def end(self, tag):
        xml = self._builder.end(tag)

        self._depth -= 1
        if self._depth == 1:
            self._callback(xml)

    def data(self, data):
        self._builder.data(data)

    def feed(self, data):
        self._parser.feed(data)


class CoqtopError(Exception):
    pass

class Coqtop(object):
    def __init__(self, args=['coqtop', '-ideslave']):
        from subprocess import PIPE
        coro = asyncio.create_subprocess_exec(*args, stdin=PIPE, stdout=PIPE)
        self._proc = await(coro)
        self._to_coq = self._proc.stdin
        self._from_coq = self._proc.stdout

        self._parser = XMLStreamParser(self._handle_response, encoding='utf-8')
        self._response_buf = []

    def send_raw(self, req):
        msg = ET.tostring(req, encoding='utf-8')
        #print('send: %r' % msg)
        self._to_coq.write(msg)
        await(self._to_coq.drain())
        #print('sent!')

    def recv_raw(self):
        while len(self._response_buf) == 0:
            #print('receiving...')
            msg = await(self._from_coq.read(4096))
            assert len(msg) > 0
            #print('recv: %r' % msg)
            self._parser.feed(msg)

        xml = self._response_buf[0]
        self._response_buf = self._response_buf[1:]
        return xml

    def _handle_response(self, xml):
        self._response_buf.append(xml)

    def recv_value(self):
        def malformed(why):
            return ValueError('malformed response (%s): %r' % (why, ET.tostring(xml)))

        xml = self.recv_raw()
        if xml.tag != 'value':
            raise malformed('unrecognized tag %r' % xml.tag)

        result = xml.get('val')
        if result == 'fail':
            raise CoqtopError(xml.text.strip())
        elif result != 'good':
            raise malformed('unrecognized "val" field %r' % result)

        if len(xml) != 1:
            raise malformed('wrong number of children')

        child = xml[0]
        if len(child) > 0:
            raise malformed('unexpected non-text children in value')
        if child.tag == 'string':
            return child.text or ''
        elif child.tag == 'int':
            return int(child.text)
        else:
            raise malformed('expected value tag, not %r' % child.tag)

    def eval(self, cmd):
        xml = ET.Element('call')
        xml.set('val', 'interp')
        xml.set('id', '0')
        #xml.set('raw', 'true')
        xml.text = cmd
        self.send_raw(xml)

        return self.recv_value()

    def goals(self):
        xml = ET.Element('call')
        xml.set('val', 'goal')
        self.send_raw(xml)
        return ET.tostring(self.recv_raw())

    def rewind(self, steps):
        xml = ET.Element('call')
        xml.set('val', 'rewind')
        xml.set('steps', str(steps))
        self.send_raw(xml)
        return self.recv_value()


Token = namedtuple('Token', ['value', 'line', 'col', 'end_line', 'end_col'])

NON_SPACE_RE = re.compile(r'\S')
COMMENT_OPEN_RE = re.compile(r'\(\*')
COMMENT_BOUNDARY_RE = re.compile(r'\(\*|\*\)')
STRING_DELIM_RE = re.compile(r'\\"|"')
DELIM_RE = re.compile(r'\(\*|"|\.($|\s)')
BULLET_RE = re.compile(r'[-+*{}]($|\s)')

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
        result = []
        while True:
            token = self.pull()
            if token is None:
                break
            result.append(token)
        return result

    def pull_until(self, line, col):
        result = []
        while True:
            token = self.pull()
            if token is None or token.end_line > line or \
                    (token.end_line == line and token.end_col > col + 1):
                break
            result.append(token)
        return result

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

class BufferInfo(object):
    def __init__(self, owner, file_nr, messages_nr, coq):
        self.owner = owner
        self.file_nr = file_nr
        self.messages_nr = messages_nr
        self.coq = coq
        self.pending = False
        self.cmds = []

    def file_buf(self):
        return self.owner.vim.buffers[self.file_nr - 1]

    def messages_buf(self):
        return self.owner.vim.buffers[self.messages_nr - 1]

    def eval(self, cmd):
        self.start_pending(cmd.replace('\n', ' '))
        try:
            result = self.coq.eval(cmd)
            self.cmds.append(cmd)
            self.finish_pending('===', result)
            return True
        except CoqtopError as e:
            self.finish_pending('***', str(e))
            return False

    def rewind(self, steps=1):
        self.start_pending('rewind %d steps' % steps)
        try:
            result = self.coq.rewind(steps)
            if steps > len(self.cmds):
                self.cmds = []
            else:
                self.cmds = self.cmds[:len(self.cmds) - steps]
            self.finish_pending('===', 'OK')
            return True
        except CoqtopError as e:
            self.finish_pending('***', str(e))
            return False

    def eval_to(self, line, col):
        tokens = Lexer(self.file_buf()[:]).pull_until(line, col)
        cmds = [t.value for t in tokens]
        old_cmds = self.cmds
        i = 0
        while i < len(cmds) and i < len(old_cmds) and cmds[i] == old_cmds[i]:
            i += 1

        if i < len(old_cmds):
            ok = self.rewind(len(old_cmds) - i)
            if not ok:
                return False

        for cmd in cmds[i:]:
            ok = self.eval(cmd)
            if not ok:
                return False

        return True

    def post_write_msg(self):
        buf = self.messages_buf()
        if len(buf) > 50:
            buf[50:] = []

        vim = self.owner.vim
        win_nr = vim.eval('bufwinnr(%d)' % buf.number)
        if win_nr != -1:
            vim.windows[win_nr - 1].cursor = (1, 0)

    def start_pending(self, what):
        if self.pending:
            raise ValueError('already have a pending command')
        self.pending = True

        self.messages_buf()[0:0] = [' ... %s' % what, '']
        self.post_write_msg()

    def finish_pending(self, mark, results):
        if not isinstance(results, list):
            results = results.splitlines()

        self.pending = False

        buf = self.messages_buf()
        buf[0] = ' %s %s' % (mark, buf[0][5:])
        buf[1:1] = results
        self.post_write_msg()

class Handler(object):
    def __init__(self, vim):
        self.vim = vim
        self.vim_lock = VimLock(vim)
        self.live_buffers = {}

    def on_setup(self):
        self.init_bindings()

    def on_request(self, cmd, args):
        try:
            if cmd == 'locked':
                self.vim_lock.dispatch(args[0])
            elif cmd == 'init':
                self.init_for_current_buffer()
            elif cmd == 'eval':
                return self.info().eval(args[0])
            else:
                raise ValueError('unknown request %r' % cmd)
        except Exception as e:
            print('request(%s, %s): %s' % (cmd, args, e))
            traceback.print_exc(file=log)
            raise

    def on_notify(self, cmd, args):
        try:
            if cmd == 'init':
                self.init_for_current_buffer()
            elif cmd == 'eval':
                return self.info().eval(args[0])
            elif cmd == 'eval_to':
                return self.info().eval_to(args[0] - 1, args[1] - 1)
            else:
                raise ValueError('unknown notification %r' % cmd)
        except Exception as e:
            print('notify(%s, %s): %s' % (cmd, args, e))
            traceback.print_exc(file=log)

    def run(self):
        self.vim.session.run(self.on_request, self.on_notify, self.on_setup)

    def info(self):
        nr = self.vim.current.buffer.number
        if nr not in self.live_buffers:
            self.init_for_current_buffer()
            #defer()
        return self.live_buffers[nr]

    def init_bindings(self):
        vim = self.vim
        vim.command('command! CoqToHere call rpcnotify(%d, "eval_to", line("."), col("."))' %
                self.vim.channel_id)
        vim.command('command! -nargs=* Coq call rpcnotify(%d, "eval", <q-args>)' %
                self.vim.channel_id)
        vim.command('nnoremap CC :Coq ')
        vim.command('nnoremap CH :CoqToHere<CR>')

    def init_for_current_buffer(self):
        vim = self.vim

        buf = vim.current.buffer
        old_win = vim.eval('winnr()')

        vim.command("rightbelow vertical new Messages\ \(%s\)" % buf.name)
        messages_buf = vim.current.buffer
        messages_buf.options['buftype'] = 'nofile'
        messages_buf.options['swapfile'] = False
        messages_buf.options['buflisted'] = False

        vim.command('%dwincmd w' % old_win)

        coq = Coqtop()

        info = BufferInfo(self, buf.number, messages_buf.number, coq)
        assert buf.number not in self.live_buffers
        self.live_buffers[buf.number] = info
        assert messages_buf.number not in self.live_buffers
        self.live_buffers[messages_buf.number] = info


print('starting...')
loop, session = make_session()
vim = neovim.Nvim.from_session(session)
asyncio.set_event_loop(loop._loop)

Handler(vim).run()

print('stopped')
