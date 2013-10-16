#!/usr/bin/env python

import sys

times = open('timing.log.sorted')
for line in times:
  time = int(line.split()[0]) / 1e9
  unit = 's'
  filename = line.split()[1]
  if time > 60:
    time = time / 60
    unit = 'm'
    if time > 60:
      time = time / 60
      unit = 'h'
      if time > 24:
        time = time / 24
        unit = 'd'
  print("%5.2f%s : %s" % (time, unit, filename))
