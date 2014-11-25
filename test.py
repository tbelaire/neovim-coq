from __future__ import print_function

try:
    import asyncio
except ImportError:
    import trollius as asyncio
import greenlet
import lxml.etree as ET
import os
import sys

import neovim


log = open('fifo', 'w', 1)
sys.stderr = log

real_print = print
def print(*args, **kwargs):
    real_print(grname() + ':', *args, file=log, **kwargs)


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


GR_NAMES = {}
def namegr(name):
    gr = greenlet.getcurrent()
    GR_NAMES[id(gr)] = name

namegr('top level')

def grname(gr=None):
    gr = gr or greenlet.getcurrent()
    return '%s #%x' % (GR_NAMES.get(id(gr), 'anonymous'), id(gr))


class VimLock(object):
    """Context manager to ensure some vim commands execute atomically.  Upon entering this context
    manager, the current greenlet will yield to its parent (optionally providing a value) and resume
    only once the lock is held.  Upon exiting, the greenlet will release the lock, yield again, and
    resume the computation in the background.
    """
    def __init__(self, vim):
        self._vim = vim
        self._next_cookie = 0
        self._pending = {}

    def __call__(self, value=None):
        print('producing vlc with %r' % value)
        return VimLockContext(self, value)

    def _enter(self, value):
        cookie = self._next_cookie
        self._next_cookie += 1

        gr = greenlet.getcurrent()
        self._pending[cookie] = gr

        vim = self._vim
        def handler():
            print('begin locked request')
            vim.eval('rpcrequest(%d, "locked", %d)' % (vim.channel_id, cookie))
            print('end locked request')

        print('schedule lock request for %d' % cookie)
        vim.session.threadsafe_call(handler)
        print('__enter__ yielding to parent %s' % grname(gr.parent))
        dispatch_gr = gr.parent.switch(value)
        print('__enter__ returned from yield with dispatch_gr %s' % grname(dispatch_gr))
        return dispatch_gr

    def dispatch(self, cookie):
        dispatch_gr = greenlet.getcurrent()
        target_gr = self._pending.pop(cookie)
        print('dispatch to %s with dispatcher %s' % (grname(target_gr), grname(dispatch_gr)))
        target_gr.switch(dispatch_gr)

class VimLockContext(object):
    def __init__(self, owner, value):
        self._owner = owner
        self._value = value
        self._dispatch_gr = None

    def __enter__(self):
        print('entering vlc!!')
        assert self._dispatch_gr is None, \
                'VimLockContext is not reentrant'
        self._dispatch_gr = self._owner._enter(self._value)

    def __exit__(self, exc_type, exc_value, traceback):
        print('exiting vlc!!')
        gr = greenlet.getcurrent()
        def handler():
            gr.switch()

        print('schedule unlocked continuation')
        self._owner._vim.session.threadsafe_call(handler)
        print('__exit__ yielding to dispatcher %s' % grname(self._dispatch_gr))
        self._dispatch_gr.switch()
        print('__exit__ returned from yield')
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
        print('send: %r' % msg)
        self._to_coq.write(msg)
        await(self._to_coq.drain())
        print('sent!')

    def recv_raw(self):
        while len(self._response_buf) == 0:
            print('receiving...')
            msg = await(self._from_coq.read(4096))
            assert len(msg) > 0
            print('recv: %r' % msg)
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
        if child.tag != 'string':
            raise malformed('expected <string>, not %r' % child.tag)
        if len(child) > 0:
            raise malformed('unexpected non-text children in <string>')

        return child.text or ''

    def eval(self, cmd):
        xml = ET.Element('call')
        xml.set('val', 'interp')
        xml.set('id', '0')
        xml.set('raw', 'true')
        xml.text = cmd

        self.send_raw(xml)
        return self.recv_value()


coq = None

def on_setup():
    global coq
    coq = Coqtop()

def on_request(cmd, args, **kwargs):
    namegr('request handler')
    if cmd == 'eval':
        return coq.eval(args[0])
    elif cmd == 'locked':
        print('enter lock dispatch')
        vim_lock.dispatch(args[0])
        print('exit lock dispatch')
        return None
    elif cmd == 'testlock':
        print('begin')
        with vim_lock:
            print('a')
            print(vim.eval('2'))
            print('d')
        print('end')
        return 17
    raise ValueError('unknown command %r' % cmd)

def on_notify(*args, **kwargs):
    namegr('notify handler')
    print('got notify: args=%s, kwargs=%s' % (args, kwargs))
    with vim_lock():
        print('entered lock!!')
        print(vim.eval('1'))
        print(vim.eval('2'))
        print('exiting lock!!')
    print('after lock')


print('starting...')
loop, session = make_session()
vim = neovim.Nvim.from_session(session)
asyncio.set_event_loop(loop._loop)

vim_lock = VimLock(vim)

vim.session.run(on_request, on_notify, on_setup)

print('stopped')
