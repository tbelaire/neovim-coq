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



class BufferState(object):
    def __init__(self, owner, buf):
        self._owner = owner
        self._buf = buf
        self._lexer = lexer.Lexer(buf)
        self._cmd_tokens = []
        self._states = []
        self._error_pos = None

    def pre_advance(self, line, col):
        self._lexer.reset()
        ts = list(self._lexer.pull_until(line, col))

        # Only consider commands that actually got processed when deciding
        # whether to advance/retract.
        old_ts = self._cmd_tokens[:len(self._states)]

        i = 0
        while i < len(ts) and i < len(old_ts) and ts[i].value == old_ts[i].value:
            i += 1

        delta = len(ts) - len(old_ts)
        self._cmd_tokens = ts
        self._states = self._states[:i]

        return delta

    def last_command(self):
        if len(self._cmd_tokens) == 0:
            return '<empty buffer>'
        else:
            return self._cmd_tokens[-1].value

    def cur_error(self):
        return self._error_pos

    def cur_pos(self):
        if len(self._states) == 0:
            return (0, 0)
        else:
            t = self._cmd_tokens[len(self._states) - 1]
            return (t.end_line, t.end_col)

    def cur_state(self):
        if len(self._states) == 0:
            return self._owner.root_state
        else:
            return self._states[-1]

    def advance(self):
        s = self.cur_state()

        r = self._owner.coq.call('Edit_at', s)
        if isinstance(r, coqtop.Err):
            return r

        for i in range(len(self._states), len(self._cmd_tokens)):
            cmd = self._cmd_tokens[i].value
            r = self._owner.coq.call('Add', ((cmd, -1), (s, True)))
            if isinstance(r, coqtop.Err):
                return r
            s = r.val[0]
            self._states.append(s)

        r = self._owner.coq.call('Status', True)
        if isinstance(r, coqtop.Err):
            err_s, msg = r.err
            for i, s in enumerate(self._states):
                if s == err_s:
                    # `err_s` is a valid state just before the error.
                    t = self._cmd_tokens[i + 1]
                    self._error_pos = (t.line, t.col)
            return coqtop.Err(msg)
        else:
            self._error_pos = None
            return r


class CoqHandler(vimutil.Handler):
    def __init__(self, *args, **kwargs):
        super(CoqHandler, self).__init__(*args, **kwargs)

        self.goals_buf = None
        self.messages_buf = None

        self.coq = None
        self.root_state = None
        self.cur_state = None

        self.msg_line = 0

        self.buffer_state = {}

        self.add_setup_handler(self.do_setup)
        self.add_notify_handler('open_wins', self.do_open_wins)
        self.add_notify_handler('query', self.do_query)
        self.add_notify_handler('eval_to', self.do_eval_to)
        self.add_notify_handler('last_dot', self.do_goto_last_dot)
        self.add_notify_handler('goto_error', self.do_goto_error)
        self.add_notify_handler('debug', self.do_debug)

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
            'command! CoqToHere call rpcnotify(%(id)d, "eval_to", line("."), col("."))',
            'command! CoqLastDot call rpcnotify(%(id)d, "last_dot")',
            'command! CoqError call rpcnotify(%(id)d, "goto_error")',
            'command! CoqDebug call rpcnotify(%(id)d, "debug")',
            #'command! -nargs=* Coq call rpcnotify(%d, "eval", <q-args>)' %
                #vim.channel_id,
            #'nnoremap CC :Coq ',
            'nnoremap CH :CoqToHere<CR>',
            'nnoremap CD :CoqLastDot<CR>',
            'nnoremap CE :CoqError<CR>',
            'nnoremap C? :CoqDebug<CR>',
            #'highlight CheckedByCoq ctermbg=17 guibg=LightGreen',
            #'highlight SentToCoq ctermbg=60 guibg=LimeGreen',
        ]
        for cmd in cmds:
            vim.command(cmd % {'id': vim.channel_id})

    def init_coqtop(self):
        extra_args_file = '_CoqProject' if os.path.exists('_CoqProject') else None
        self.coq = coqtop.Coqtop(extra_args_file=extra_args_file)
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

    def _begin_call(self, desc):
        self.messages_buf[0:0] = [' ... %s' % desc, '']
        self.msg_line = 2

    def _show_message(self, msg):
        lines = msg.split('\n')
        l = self.msg_line
        self.messages_buf[l:l] = lines
        self.msg_line += len(lines)

    def _end_call(self, desc, result):
        if isinstance(result, coqtop.Ok):
            self.messages_buf[0] = ' +++ %s' % desc
        else:
            self.messages_buf[0] = ' !!! %s' % desc
            err = result.err[-1] if isinstance(result.err, tuple) else result.err
            self._show_message(err)

        self.messages_buf[0:0] = ['']
        self.msg_line = 0

        win_nr = self.vim.eval('bufwinnr(%d)' % self.messages_buf.number)
        if win_nr != -1:
            self.vim.windows[win_nr - 1].cursor = (1, 0)

        self._refresh_goals()

    def _refresh_goals(self):
        r = self.coq.call('Goal', ())
        if r.val.val is None:
            self.goals_buf[:] = ['No goals.']
            return

        goals = r.val.val

        lines = []
        if len(goals.fg) > 0:
            g = goals.fg[0]
            for h in g.hyp:
                lines.extend(h.split('\n'))
            lines.append(' ===')
            lines.extend(g.ccl.split('\n'))

        if len(goals.fg) > 1:
            lines.extend(['', ''])
            lines.append('%d other active goals:' % (len(goals.fg) - 1))
            for i, g in enumerate(goals.fg[1:]):
                ccl_lines = g.ccl.split('\n')
                lines.append(' %3d: %s' % (i + 2, ccl_lines[0]))
                for i in range(1, len(ccl_lines)):
                    lines.append('      %s' % (ccl_lines[i]))

        lines.extend([''])
        if len(goals.bg) > 0:
            lines.append('%d background goals' % len(goals.bg))
        if len(goals.shelved) > 0:
            lines.append('%d shelved goals' % len(goals.shelved))
        if len(goals.given_up) > 0:
            lines.append('%d admitted goals' % len(goals.given_up))

        self.goals_buf[:] = lines


    def do_query(self, msg):
        desc = re.sub(r'\s+', ' ', msg, flags=re.MULTILINE)
        if len(desc) > 80:
            desc = desc[:77] + '...'

        self._begin_call(desc)
        r = self.coq.call('Query', (msg, self.cur_state))
        self._end_call(desc, r)

    def handle_message(self, level, msg):
        self._show_message(msg)

    def get_buffer_state(self, buf):
        if buf.number not in self.buffer_state:
            self.buffer_state[buf.number] = BufferState(self, buf)
        return self.buffer_state[buf.number]

    def do_eval_to(self, line, col):
        bs = self.get_buffer_state(vim.current.buffer)
        delta = bs.pre_advance(line - 1, col - 1)

        last_cmd = re.sub(r'\s+', ' ', bs.last_command(), flags=re.MULTILINE)
        if len(last_cmd) > 50:
            last_cmd = last_cmd[:47] + '...'
        desc = '%s %d to line %d (%s)' % (
                'advance' if delta >= 0 else 'retract',
                abs(delta),
                line,
                last_cmd)

        self._begin_call(desc)
        r = bs.advance()
        self._end_call(desc, r)

    def do_goto_last_dot(self):
        bs = self.get_buffer_state(vim.current.buffer)
        l, c = bs.cur_pos()
        vim.current.window.cursor = (l + 1, c)

    def do_goto_error(self):
        bs = self.get_buffer_state(vim.current.buffer)
        l, c = bs.cur_error() or bs.cur_pos()
        vim.current.window.cursor = (l + 1, c)

    def do_debug(self):
        self._refresh_goals()
        #bs = self.get_buffer_state(vim.current.buffer)
        #print('Buffer status:\n  %d tokens\n  %d states\n  last command: %r' %
        #        (len(bs._cmd_tokens),
        #            len(bs._states),
        #            bs._cmd_tokens[-1]))


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
