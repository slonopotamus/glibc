ifeq ($(subdir),stdio-common)
ldbl-extra-routines += printf_size

tests-internal += test-printf-size-ieee128 test-printf-size-ibm128
CFLAGS-test-printf-size-ieee128.c += -mfloat128 -mabi=ieeelongdouble -Wno-psabi
CFLAGS-test-printf-size-ibm128.c += -mabi=ibmlongdouble -Wno-psabi

ifeq ($(run-built-tests),yes)
tests-special += $(objpfx)test-printf-size-ieee128.out
tests-special += $(objpfx)test-printf-size-ibm128.out
endif

$(objpfx)test-printf-size-ieee128.out: \
  tst-printfsz-islongdouble.sh $(objpfx)test-printf-size-ieee128
	$(SHELL) $^ '$(test-program-prefix)' $@; \
	$(evaluate-test)

$(objpfx)test-printf-size-ibm128.out: \
  tst-printfsz-islongdouble.sh $(objpfx)test-printf-size-ibm128
	$(SHELL) $^ '$(test-program-prefix)' $@; \
	$(evaluate-test)
endif

# Add IEEE binary128 files as make targets.
routines += $(foreach r,$(ldbl-extra-routines),ieee128-$(r))

# On powerpc64le, the routines responsible for converting between long
# double and string (e.g.: printf, scanf, strtold, strfroml) default to
# IBM long double mode.  When support for TS 18661-3 was added, several
# internal functions were modified so that they could also handle
# floating-point variables with IEEE binary128 format, but as an
# additional type, _Float128.
#
# The following rule ensures that the string conversion routines will
# always be built in IBM long double mode, with additional support for
# IEEE binary128, through the use of -mabi=ibmlongdouble and -mfloat128.
ldbl-ibm128-files := $(objpfx)test-%-ibm128^ \
		     $(foreach r,$(ldbl-extra-routines),$(objpfx)$(r)^) \
		     $(foreach r,$(ldbl-extra-routines),$(objpfx)$(r)-internal^)
obj-suf-foreach = $(foreach suf,$(all-object-suffixes),$(subst ^,$(suf),$(1)))

# Removing -mabi=ieeelongdouble is not required, but helps when
# analyzing the flags that were passed to the compiler.
$(call obj-suf-foreach,$(ldbl-ibm128-files)): \
  sysdep-CFLAGS := $(filter-out -mabi=ieeelongdouble -Wno-psabi, \
				$(sysdep-CFLAGS)) \
		   -mabi=ibmlongdouble
