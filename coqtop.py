from __future__ import print_function

from collections import deque, namedtuple
import greenlet
import lxml.etree as ET

from asyncutil import await, asyncio
import util
from xmlutil import XMLStreamParser

print = util.mk_print(__name__)


class CoqtopError(Exception):
    pass

Ok = namedtuple('Ok', ['val'])
Err = namedtuple('Err', ['err'])

Inl = namedtuple('Inl', ['val'])
Inr = namedtuple('Inr', ['val'])

StateId = namedtuple('StateId', ['id'])
Option = namedtuple('Option', ['val'])

OptionState = namedtuple('OptionState', ['sync', 'depr', 'name', 'value'])
OptionValue = namedtuple('OptionValue', ['val'])

def parse_response(xml):
    assert xml.tag == 'value'
    if xml.get('val') == 'good':
        return Ok(parse_value(xml[0]))
    elif xml.get('val') == 'fail':
        return Err(parse_error(xml[0]))
    else:
        assert False, 'expected "good" or "fail" in <value>'

def parse_value(xml):
    if xml.tag == 'unit':
        return ()
    elif xml.tag == 'bool':
        if xml.get('val') == 'true':
            return True
        elif xml.get('val') == 'false':
            return False
        else:
            assert False, 'expected "true" or "false" in <bool>'
    elif xml.tag == 'string':
        return xml.text or ''
    elif xml.tag == 'int':
        return int(xml.text)
    elif xml.tag == 'state_id':
        return StateId(int(xml.get('val')))
    elif xml.tag == 'list':
        return [parse_value(c) for c in xml]
    elif xml.tag == 'option':
        if xml.get('val') == 'none':
            return Option(None)
        elif xml.get('val') == 'some':
            return Option(parse_value(xml[0]))
        else:
            assert False, 'expected "none" or "some" in <option>'
    elif xml.tag == 'pair':
        return tuple(parse_value(c) for c in xml)
    elif xml.tag == 'union':
        if xml.get('val') == 'in_l':
            return Inl(parse_value(xml[0]))
        elif xml.get('val') == 'in_r':
            return Inr(parse_value(xml[0]))
        else:
            assert False, 'expected "in_l" or "in_r" in <union>'
    elif xml.tag == 'option_state':
        sync, depr, name, value = map(parse_value, xml)
        return OptionState(sync, depr, name, value)
    elif xml.tag == 'option_value':
        return OptionValue(parse_value(xml[0]))

def parse_error(xml):
    return ET.tostring(xml)

def build(tag, val=None, children=()):
    attribs = {'val': val} if val is not None else {}
    xml = ET.Element(tag, attribs)
    xml.extend(children)
    return xml

def encode_call(name, arg):
    return build('call', name, [encode_value(arg)])

def encode_value(v):
    if v == ():
        return build('unit')
    elif isinstance(v, bool):
        return build('bool', str(v).lower())
        xml.text = str(v)
        return xml
    elif isinstance(v, str):
        xml = build('string')
        xml.text = v
        return xml
    elif isinstance(v, int):
        xml = build('int')
        xml.text = str(v)
        return xml
    elif isinstance(v, StateId):
        return build('state_id', str(v.id))
    elif isinstance(v, list):
        return build('list', None, [encode_value(c) for c in v])
    elif isinstance(v, Option):
        xml = build('option')
        if v.val is not None:
            xml.set('val', 'some')
            xml.append(encode_value(v.val))
        else:
            xml.set('val', 'none')
        return xml
    elif isinstance(v, Inl):
        return build('union', 'in_l', [encode_value(v.val)])
    elif isinstance(v, Inr):
        return build('union', 'in_r', [encode_value(v.val)])
    # NB: `tuple` check must be at the end because it overlaps with () and
    # namedtuples.
    elif isinstance(v, tuple):
        return build('pair', None, [encode_value(c) for c in v])
    else:
        assert False, 'unrecognized type in encode_value: %r' % (type(v),)

class Coqtop(object):
    # __init__ must run in a greenlet context so it can wait for the subprocess
    # to start up.
    def __init__(self,
            args=['/home/stuart/.local/coq/bin/coqtop', '-ideslave',
                '-main-channel', 'stdfds',
                '-async-proofs', 'on'],
            handler=lambda x: None):
        from subprocess import PIPE
        coro = asyncio.create_subprocess_exec(*args,
                stdin=PIPE,
                stdout=PIPE,
                stderr=open('fifo', 'w'))
        self._proc = await(coro)
        self._to_coq = self._proc.stdin
        self._from_coq = self._proc.stdout

        self._do_recv()

        self._parser = XMLStreamParser(self._handle_response, encoding='utf-8')
        self._response_waiters = deque([])

        self._message_handler = None

    # The low-level receiver code runs directly on the event loop greenlet,
    # inside an ordinary async callback.
    def _do_recv(self):
        coro = self._from_coq.read(4096)
        task = asyncio.async(coro)
        task.add_done_callback(self._handle_recv)

    def _handle_recv(self, task):
        msg = task.result()
        assert len(msg) > 0
        self._parser.feed(msg)
        self._do_recv()

    def _handle_response(self, xml):
        if xml.tag == 'value':
            self._handle_response_value(xml)
        elif xml.tag == 'message':
            self._handle_response_message(xml)
        else:
            print('unhandled: %r' % ET.tostring(xml))

    def _handle_response_value(self, xml):
        resp = parse_response(xml)

        gr = self._response_waiters.popleft()
        def callback():
            gr.switch(resp)
        asyncio.get_event_loop().call_soon_threadsafe(callback)

    def _handle_response_message(self, xml):
        if self._message_handler is None:
            return

        assert xml[0].tag == 'message_level'
        level = xml[0].get('val')

        msg = parse_value(xml[1])

        def task():
            self._message_handler(level, msg)
        gr = greenlet.greenlet(task)
        def callback():
            gr.switch()
        asyncio.get_event_loop().call_soon_threadsafe(callback)

    def set_message_handler(self, f):
        self._message_handler = f

    # The higher-level code runs in a greenlet, so it can block for responses.
    def _get_response(self):
        gr = greenlet.getcurrent()
        self._response_waiters.append(gr)
        return gr.parent.switch()

    def call(self, name, arg):
        xml = encode_call(name, arg)
        msg = ET.tostring(xml, encoding='utf-8')
        self._to_coq.write(msg)
        self._to_coq.drain()
        resp = self._get_response()
        return resp
