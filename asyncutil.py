try:
    import asyncio
except ImportError:
    import trollius as asyncio
import greenlet


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


_NAME_MAP = {}

def base_name(gr):
    global _NAME_MAP
    if id(gr) not in _NAME_MAP:
        _NAME_MAP[id(gr)] = 'gr_' + str(len(_NAME_MAP))
    return _NAME_MAP[id(gr)]

def name(gr):
    if gr.parent is not None and gr.parent is not gr:
        return '%s/%s' % (name(gr.parent), base_name(gr))
    else:
        return base_name(gr)

def set_name(s):
    gr = greenlet.getcurrent()
    _NAME_MAP[id(gr)] = s
