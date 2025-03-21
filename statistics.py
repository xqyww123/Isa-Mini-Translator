#!/bin/env python

USAGE = """
statistics.py <PATH TO THE DATABASE>
"""

from sqlitedict import SqliteDict
import sys
import csv
from collections import Counter

if len(sys.argv) != 2:
    print(USAGE)
    exit(1)

total = 0
success = 0
distrs = {}
distr = Counter({})

COMMANDS = {'HAVE', 'END', 'NEXT', 'CONSIDER', 'RULE', 'UNFOLD', 'INTRO', 'APPLY', 'CRUSH',
            'CASE_SPLIT', 'INDUCT', 'OPEN_MODULE', 'CONFIG', 'DEFINE', 'LET', 'HAMMER', 'NOTATION'}

def distr_of_commands (script):
    all_commands = [line.split()[0] for line in script.splitlines() if line.strip() and line.split()]
    commands = [word for word in all_commands if word in COMMANDS]
    return Counter(commands)


decl = 0
with SqliteDict(sys.argv[1]) as db:
    with open('result.csv', 'w', newline='') as f:
        w = csv.writer(f, delimiter=',', quotechar='\"', quoting=csv.QUOTE_MINIMAL)
        for k,v in db.items():
            match k.split(':'):
                case (_,'header',file,_):
                    print(f"{file} has header {v}")
                case (file,line,pos):
                    decl += 1
                case (file,line):
                    if v[0]:
                        for t,s in v[1].items():
                            w.writerow([file,line,v[0],t,s])
                    else:
                        w.writerow([file, line, v[0], v[1]])
                    total += 1
                    if v[0]:
                        success += 1
                        d = distr_of_commands(v[1]['refined'])
                        distrs[file, line] = d
                        distr.update(d)

print(f"{success} / {total} = {success / total}")
print(f"{decl} decls")

total_count = sum(distr.values())
percentage_distribution = {word: (count / total_count * 100) for word, count in distr.items()}
print(percentage_distribution)

