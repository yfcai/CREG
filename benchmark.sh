#!/bin/bash
echo '
clean
test:clean
test:compile
clean
test:clean
test:compile
clean
test:clean
test:compile
clean
test:clean
test:compile
clean
test:clean
test:compile
clean
test:clean
test:compile
' | sbt
