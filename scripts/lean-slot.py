#!/usr/bin/env python3
"""Run a compiler through a shared, FIFO, file-locked semaphore.

A ticket is removed before exec; the selected flock descriptor is inherited by
that compiler and released by the OS when it exits. An interrupted waiter
removes its own ticket. A forcibly killed waiter's exact ticket may be removed
only after reconciling that invocation's terminal state.
"""
import argparse
import datetime
import fcntl
import os
from pathlib import Path
import signal
import sys
import time
import uuid

parser = argparse.ArgumentParser()
parser.add_argument('--slots', type=int, default=2)
parser.add_argument('--lock-dir', required=True)
parser.add_argument('command', nargs=argparse.REMAINDER)
args = parser.parse_args()
command = args.command[1:] if args.command[:1] == ['--'] else args.command
if args.slots < 1 or not command:
    parser.error('positive slots and a command are required')
lock_dir = Path(args.lock_dir)
queue_dir = lock_dir / 'queue'
queue_dir.mkdir(parents=True, exist_ok=True)
ticket = queue_dir / (f'{time.time_ns():020d}-{uuid.uuid4().hex}.request')
ticket.write_text(' '.join(command) + '\n')
print(f'FIFO compiler ticket: {ticket.name}', flush=True)

def interrupted(_sig, _frame):
    raise KeyboardInterrupt

signal.signal(signal.SIGINT, interrupted)
signal.signal(signal.SIGTERM, interrupted)
held = None
try:
    with (lock_dir / 'queue.lock').open('a') as gate:
        while held is None:
            fcntl.flock(gate, fcntl.LOCK_EX)
            try:
                pending = sorted(queue_dir.glob('*.request'))
                if pending and pending[0] == ticket:
                    for slot in range(1, args.slots + 1):
                        fd = os.open(lock_dir / f'{slot}.lock', os.O_CREAT | os.O_WRONLY, 0o600)
                        try:
                            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        except BlockingIOError:
                            os.close(fd)
                        else:
                            held = fd
                            os.set_inheritable(held, True)
                            ticket.unlink()
                            break
            finally:
                fcntl.flock(gate, fcntl.LOCK_UN)
            if held is None:
                time.sleep(0.1)
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    print("FIFO compiler acquired UTC: " + datetime.datetime.now(datetime.timezone.utc).isoformat(), flush=True)
    os.execvp(command[0], command)
finally:
    if ticket.exists():
        ticket.unlink()
    if held is not None:
        os.close(held)
