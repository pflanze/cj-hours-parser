include .sources

_cj-hours-parser:
	sbin/create-sources
	make target/debug/cj-hours-parser

target/debug/cj-hours-parser:
	cargo build

runintegrationtests: _cj-hours-parser
	test/run
	git status test/

runtests: _cj-hours-parser
	cargo test
	make runintegrationtests
