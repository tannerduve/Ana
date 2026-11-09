"""Trusted local ownership journal for containers created by evaluation adapters.

This does not cover official SWE-bench grader containers created through its SDK.
After interruption, cleanup uses an exact random label, never a global before/
after inventory. Docker and the private journal directory are trusted boundaries.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import uuid
from docker_endpoint import command_environment, docker_host

LABEL = 'org.lean-harness.evaluation-owner'
NAME = 'owned-containers.jsonl'


def docker(*args):
    return subprocess.run(['docker', *args], capture_output=True, text=True, timeout=60,
                          env=command_environment())


def cleanup_token(token, intents, acknowledged, observe):
    report = {'token': token, 'settled': False, 'removed': [], 'remaining': [], 'errors': [],
              'unresolved_intents': [],
              'scope': 'Only exact-label containers created through evaluation create_container; SWE SDK graders not covered.'}
    if not re.fullmatch('[0-9a-f]{32}', token):
        raise ValueError('invalid ownership token')
    try:
        discovered = docker('ps', '-aq', '--no-trunc', '--filter', f'label={LABEL}={token}')
        if discovered.returncode:
            raise RuntimeError('owned-container discovery failed')
        ids = discovered.stdout.split()
        if len(ids) > 256 or any(not re.fullmatch('[0-9a-f]{64}', ident) for ident in ids):
            raise RuntimeError('invalid or excessive owned-container discovery')
        for ident in ids:
            inspected = docker('inspect', ident)
            if inspected.returncode:
                raise RuntimeError('owned-container inspection failed')
            value = json.loads(inspected.stdout)
            if len(value) != 1 or value[0]['Id'] != ident or value[0]['Config'].get('Labels', {}).get(LABEL) != token:
                raise RuntimeError('container ownership changed during cleanup')
            name = value[0].get('Name', '').removeprefix('/')
            if name not in intents or (name in acknowledged and acknowledged[name] != ident):
                raise RuntimeError('labeled container does not match its creation intent/acknowledgement')
            if name not in acknowledged:
                # Durably preserve observed creation before removing the only
                # external evidence that reconciles a lost create response.
                observe(name, ident)
                acknowledged[name] = ident
            removed = docker('rm', '-f', ident)
            if removed.returncode:
                report['errors'].append('owned-container removal failed: ' + ident)
            else:
                report['removed'].append(ident)
        final = docker('ps', '-aq', '--no-trunc', '--filter', f'label={LABEL}={token}')
        if final.returncode:
            raise RuntimeError('final owned-container discovery failed')
        report['remaining'] = final.stdout.split()
        report['unresolved_intents'] = sorted(set(intents) - set(acknowledged))
        if report['unresolved_intents']:
            report['errors'].append('creation outcome unknown; an empty label scan does not resolve an in-flight create')
        report['settled'] = not report['remaining'] and not report['errors']
    except (OSError, ValueError, KeyError, TypeError, AttributeError, RuntimeError, subprocess.SubprocessError) as error:
        report['errors'].append(type(error).__name__ + ': ' + str(error))
    return report


def cleanup_existing(directory):
    path = Path(directory) / NAME
    try:
        with path.open('rb') as stream:
            raw = stream.read(1024 * 1024 + 1)
        if len(raw) > 1024 * 1024 or not raw.endswith(b'\n'):
            raise ValueError('incomplete or oversized ownership journal')
        lines = raw.split(b'\n')[:-1]
        if not lines or len(lines) > 4096:
            raise ValueError('empty or excessive ownership journal')
        records = [json.loads(line) for line in lines]
        if any(not isinstance(row, dict) for row in records):
            raise ValueError('ownership records must be objects')
        header = records[0]
        if header.get('version') != 1 or header.get('kind') != 'owner' or not isinstance(header.get('token'), str):
            raise ValueError('unsupported ownership journal')
        if header.get('docker_endpoint') != docker_host():
            raise ValueError('ownership journal belongs to a different Docker endpoint')
        intents, acknowledged = {}, {}
        for row in records[1:]:
            name = row.get('name')
            if not isinstance(name, str) or not name:
                raise ValueError('invalid container intent name')
            if row.get('kind') == 'intent':
                if name in intents or row.get('token') != header['token'] or not isinstance(row.get('image'), str):
                    raise ValueError('invalid/duplicate creation intent')
                intents[name] = row['image']
            elif row.get('kind') in {'created', 'observed'}:
                ident = row.get('id')
                if name not in intents or name in acknowledged or not isinstance(ident, str) or not re.fullmatch('[0-9a-f]{64}', ident):
                    raise ValueError('invalid creation acknowledgement')
                acknowledged[name] = ident
            else:
                raise ValueError('unsupported ownership record')
        return cleanup_token(header['token'], intents, acknowledged,
            lambda name, ident: append_record(path, {'kind': 'observed', 'name': name, 'id': ident}))
    except (OSError, ValueError, KeyError, TypeError) as error:
        return {'settled': False, 'remaining': [], 'errors': [type(error).__name__ + ': ' + str(error)],
                'scope': 'Ownership unavailable; no unrelated container was removed.'}


def append_record(path, value, create=False):
    flags = os.O_WRONLY | os.O_NOFOLLOW | (os.O_CREAT | os.O_EXCL if create else os.O_APPEND)
    fd = os.open(path, flags, 0o600)
    try:
        data = (json.dumps(value, separators=(',', ':'), allow_nan=False) + '\n').encode()
        while data:
            written = os.write(fd, data)
            if written <= 0:
                raise OSError('ownership append made no progress')
            data = data[written:]
        os.fsync(fd)
    finally:
        os.close(fd)


class Owner:
    def __init__(self, directory):
        self.path = Path(directory) / NAME
        self.token = uuid.uuid4().hex
        self.uncertain = False
        self.append({'kind': 'owner', 'version': 1, 'token': self.token,
                     'docker_endpoint': docker_host()}, create=True)
        fd = os.open(self.path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)

    def append(self, value, create=False):
        try:
            append_record(self.path, value, create)
        except BaseException:
            self.uncertain = True
            raise

    def intent(self, name, image):
        self.append({'kind': 'intent', 'name': name, 'image': image, 'token': self.token})
        return f'{LABEL}={self.token}'

    def created(self, name, ident):
        if not re.fullmatch('[0-9a-f]{64}', ident):
            self.uncertain = True
            raise ValueError('Docker create did not return an exact container ID')
        self.append({'kind': 'created', 'name': name, 'id': ident})

    def cleanup(self):
        result = cleanup_existing(self.path.parent)
        self.uncertain |= not result['settled']
        return result
