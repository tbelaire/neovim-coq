from __future__ import print_function

try:
    import asyncio
except ImportError:
    import trollius as asyncio
from collections import defaultdict, namedtuple
import greenlet
import lxml.etree as ET
import os
import re
import sys
import traceback

import neovim

import asyncutil
from coqtop import Coqtop, Option
import util
import vimutil

log = open('fifo', 'w', 1)
sys.stderr = log

print = util.mk_print(__name__)




if __name__ == '__main__':
    import logging
    handler = logging.FileHandler('fifo', 'w')
    handler.formatter = logging.Formatter(
        '%(asctime)s [%(levelname)s @ %(name)s] %(process)s - %(message)s')
    logging.root.addHandler(handler)
    logging.root.setLevel(logging.NOTSET)
    logging.getLogger('neovim').setLevel(logging.WARNING)

    print('\n\nstarting...')
    loop, session = vimutil.make_session()
    vim = neovim.Nvim.from_session(session)
    asyncio.set_event_loop(loop._loop)

    print('channel: %s' % vim.channel_id)


    import inspect
    import os

    def callback(event, args):
        if event in ('switch', 'throw'):
            old, new = args
            if new.parent is old:
                print(' >>> switch %s -> %s' % (info(old), info(new)))
            elif old.parent is new:
                print(' <<< switch %s -> %s' % (info(old), info(new)))
            else:
                print(' === switch %s -> %s' % (info(old), info(new)))
    #greenlet.settrace(callback)

    asyncutil.set_name('loop')

    handler = vimutil.Handler(vim)

    def do_init():
        from coqtop import *

        global coq
        coq = Coqtop()

        r = coq.call('Init', Option(None))
        s = r.val

        r = coq.call('Add', (('Require Import Arith.', -1), (s, True)))
        s = r.val[0]

        r = coq.call('Add', (('Require Import OmegaTactic.', -1), (s, True)))
        s = r.val[0]

        r = coq.call('Add', (('Require Import Coq.omega.Omega.', -1), (s, True)))
        s = r.val[0]

        r = coq.call('Status', True)

        r = coq.call('Add', (('Theorem two_plus_two : 2 + 2 = 4.', -1), (s, True)))
        s = r.val[0]

        r = coq.call('Add', (('Proof.', -1), (s, True)))
        s = r.val[0]

        r = coq.call('Add', (('omega.', -1), (s, True)))
        s = r.val[0]

        r = coq.call('Add', (('Qed.', -1), (s, True)))
        s = r.val[0]

        r = coq.call('Status', True)

        r = coq.call('Query', ('Print two_plus_two.', s))

    handler.add_notify_handler('init', do_init)

    handler.run()

    print('stopped')
