import logging
logger = logging.getLogger(__name__)


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


class Handler(object):
    def __init__(self, vim):
        self.vim = vim
        self._setup_handler = None
        self._request_handlers = {}
        self._notify_handlers = {}

    def add_setup_handler(self, f):
        assert self._setup_handler is None
        self._setup_handler = f

    def add_request_handler(self, name, f):
        assert name not in self._request_handlers
        self._request_handlers[name] = f

    def add_notify_handler(self, name, f):
        assert name not in self._notify_handlers
        self._notify_handlers[name] = f

    def _on_setup(self):
        if self._setup_handler is not None:
            self._setup_handler()

    def _on_request(self, cmd, args):
        if cmd in self._request_handlers:
            self._request_handlers[cmd](*args)
        else:
            raise ValueError('unknown request %r' % cmd)

    def _on_notify(self, cmd, args):
        if cmd in self._notify_handlers:
            self._notify_handlers[cmd](*args)
        else:
            raise ValueError('unknown notify %r' % cmd)

    def run(self):
        logger.info('run vim.session')
        self.vim.session.run(self._on_request, self._on_notify, self._on_setup)
