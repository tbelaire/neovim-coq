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
import coqtop
import lexer
import util
import vimutil

log = open('fifo', 'w', 1)
sys.stderr = log

print = util.mk_print(__name__)



class CoqHandler(vimutil.Handler):
    def __init__(self, *args, **kwargs):
        super(CoqHandler, self).__init__(*args, **kwargs)

        self.goals_buf = None
        self.messages_buf = None

        self.coq = None
        self.root_state = None
        self.cur_state = None

        self.msg_line = 0

        self.add_setup_handler(self.do_setup)
        self.add_notify_handler('open_wins', self.do_open_wins)
        self.add_notify_handler('query', self.do_query)

    def do_setup(self):
        self.init_wins()
        self.init_bindings()
        self.init_coqtop()

    def init_wins(self):
        vim = self.vim

        old_win = vim.eval('winnr()')

        vim.command("rightbelow vertical new Coq\ Goals")
        goals_buf = vim.current.buffer
        goals_buf.options['buftype'] = 'nofile'
        goals_buf.options['swapfile'] = False
        goals_buf.options['buflisted'] = False
        goals_buf[:] = []
        self.goals_buf = goals_buf

        vim.command("rightbelow new Coq\ Messages")
        messages_buf = vim.current.buffer
        messages_buf.options['buftype'] = 'nofile'
        messages_buf.options['swapfile'] = False
        messages_buf.options['buflisted'] = False
        messages_buf[:] = []
        self.messages_buf = messages_buf

        vim.command('%dwincmd w' % old_win)

    def init_bindings(self):
        vim = self.vim
        cmds = [
            'command! CoqOpenWins call rpcnotify(%(id)d, "open_wins")',
            'command! -nargs=* CoqQuery call rpcnotify(%(id)d, "query", <q-args>)',
            #'command! CoqToHere call rpcnotify(%d, "eval_to", line("."), col("."))' %
                #vim.channel_id,
            #'command! CoqLastDot call rpcnotify(%d, "jump_to_dot", line("."), col("."))' %
                #vim.channel_id,
            #'command! -nargs=* Coq call rpcnotify(%d, "eval", <q-args>)' %
                #vim.channel_id,
            #'nnoremap CC :Coq ',
            #'nnoremap CH :CoqToHere<CR>',
            #'nnoremap CD :CoqLastDot<CR>',
            #'highlight CheckedByCoq ctermbg=17 guibg=LightGreen',
            #'highlight SentToCoq ctermbg=60 guibg=LimeGreen',
        ]
        for cmd in cmds:
            vim.command(cmd % {'id': vim.channel_id})

    def init_coqtop(self):
        self.coq = coqtop.Coqtop()
        self.coq.set_message_handler(self.handle_message)

        r = self.coq.call('Init', coqtop.Option(None))
        assert isinstance(r, coqtop.Ok)
        self.root_state = r.val
        self.cur_state = self.root_state

    def do_open_wins(self):
        vim = self.vim
        old_win = vim.eval('winnr()')
        vim.command("rightbelow vertical new Coq\ Goals")
        vim.command("rightbelow new Coq\ Messages")
        vim.command('%dwincmd w' % old_win)

    def do_query(self, msg):
        desc = re.sub(r'\s+', ' ', msg, flags=re.MULTILINE)
        if len(desc) > 80:
            desc = desc[:77] + '...'

        self.messages_buf[0:0] = [' ... %s' % desc, '']
        self.msg_line = 2

        r = self.coq.call('Query', (msg, self.cur_state))
        if isinstance(r, coqtop.Ok):
            self.messages_buf[0] = ' +++ %s' % desc
        else:
            self.messages_buf[0] = ' !!! %s' % desc
            self.messages_buf[2:2] = r.err.split('\n')

        self.messages_buf[0:0] = ['']
        self.msg_line = 0

        win_nr = self.vim.eval('bufwinnr(%d)' % self.messages_buf.number)
        if win_nr != -1:
            self.vim.windows[win_nr - 1].cursor = (1, 0)

    def handle_message(self, level, msg):
        l = self.msg_line
        print(repr(msg.split('\n')))
        self.messages_buf[l:l] = msg.split('\n')

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

    handler = CoqHandler(vim)
    handler.run()

    print('stopped')
