#!/usr/bin/env bash

autoflake --quiet --in-place ./kaipy
isort ./kaipy
black ./kaipy
