/* Test for the long double variants of *syslog* functions.
   Copyright (C) 2018 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */

#include <stdarg.h>
#include <stddef.h>
#include <syslog.h>

#include <support/check.h>

static void
do_test_call (void *last, ...)
{
  long double ld = -1;
  va_list ap;

  /* Make syslog functions write to stderr with LOG_PERROR.  */
  openlog ("test-syslog", LOG_PERROR | LOG_ODELAY, LOG_USER);

  /* Call syslog functions that take a format string.  */
  SYSLOG_FUNCTION SYSLOG_FUNCTION_PARAMS;
  va_start (ap, last);
  VSYSLOG_FUNCTION VSYSLOG_FUNCTION_PARAMS;
  va_end (ap);
}

static int
do_test (void)
{
  long double ld = -1;
  do_test_call (NULL, ld);

  return 0;
}

#include <support/test-driver.c>
