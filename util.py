from __future__ import print_function

import logging

def mk_print(name):
    logger = logging.getLogger(name)
    def print(*args):
        logger.info('\t'.join(str(a) for a in args))
    return print
