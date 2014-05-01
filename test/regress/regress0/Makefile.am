SUBDIRS = . strings
DIST_SUBDIRS = $(SUBDIRS) #. arith precedence uf uflra uflia bv arrays aufbv auflia datatypes quantifiers rewriterules lemmas push-pop preprocess tptp unconstrained decision fmf strings sets

# don't override a BINARY imported from a personal.mk
@mk_if@eq ($(BINARY),)
@mk_empty@BINARY = cvc4
end@mk_if@

LOG_COMPILER = @srcdir@/../run_regression
AM_LOG_FLAGS = $(RUN_REGRESSION_ARGS) @abs_top_builddir@/src/main/$(BINARY)$(EXEEXT)

if AUTOMAKE_1_11
# old-style (pre-automake 1.12) test harness
TESTS_ENVIRONMENT = \
	$(LOG_COMPILER) \
	$(AM_LOG_FLAGS) $(LOG_FLAGS)
endif

MAKEFLAGS = -k

# These are run for all build profiles.
# If a test shouldn't be run in e.g. competition mode,
# put it below in "TESTS +="

# Regression tests for SMT inputs
SMT_TESTS = \
	constant-rewrite.smt

# Regression tests for SMT2 inputs
SMT2_TESTS = \
	hung13sdk_output2.smt2

# Regression tests for PL inputs
CVC_TESTS = \
	print_lambda.cvc

# Regression tests for TPTP inputs
TPTP_TESTS =

# Regression tests derived from bug reports
BUG_TESTS = \
	bug548a.smt2

TESTS =	$(SMT_TESTS) $(SMT2_TESTS) $(CVC_TESTS) $(TPTP_TESTS) $(BUG_TESTS)

EXTRA_DIST = $(TESTS) \
	simplification_bug4.smt2.expect \
	bug216.smt2.expect

if CVC4_BUILD_PROFILE_COMPETITION
else
TESTS += \
	arrayinuf_error.smt2
endif

# and make sure to distribute it
EXTRA_DIST += \
	subranges.cvc \
	arrayinuf_error.smt2 \
	errorcrash.smt2 \
	error.cvc

# synonyms for "check" in this directory
.PHONY: regress regress0 test
regress regress0 test: check

# do nothing in this subdir
.PHONY: regress1 regress2 regress3
regress1 regress2 regress3:
