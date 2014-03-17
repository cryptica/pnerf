#!/bin/bash

(cd ../../../../pnerf/paper/workspace && make clean)
rsync ../../../../pnerf/paper/workspace/* .
