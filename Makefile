# ################################################################
# SPDX-License-Identifier: BSD-2-Clause
# Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
#
# BSD 2-Clause License (https://www.opensource.org/licenses/bsd-license.php)
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
#    * Redistributions of source code must retain the above copyright
#      notice, this list of conditions and the following disclaimer.
#    * Redistributions in binary form must reproduce the above copyright
#      notice, this list of conditions and the following disclaimer in
#      the documentation and/or other materials provided with the
#      distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
# ################################################################
Q = $(if $(filter 1,$(V) $(VERBOSE)),,@)

# Version numbers
SED ?= sed
SED_ERE_OPT ?= -E
LIBVER_MAJOR_SCRIPT:=`$(SED) -n '/define CUCKOOHASH_VERSION_MAJOR/s/.*[[:blank:]]\([0-9][0-9]*\).*/\1/p' < cuckoohash.h`
LIBVER_MINOR_SCRIPT:=`$(SED) -n '/define CUCKOOHASH_VERSION_MINOR/s/.*[[:blank:]]\([0-9][0-9]*\).*/\1/p' < cuckoohash.h`
LIBVER_PATCH_SCRIPT:=`$(SED) -n '/define CUCKOOHASH_VERSION_RELEASE/s/.*[[:blank:]]\([0-9][0-9]*\).*/\1/p' < cuckoohash.h`
LIBVER_MAJOR := $(shell echo $(LIBVER_MAJOR_SCRIPT))
LIBVER_MINOR := $(shell echo $(LIBVER_MINOR_SCRIPT))
LIBVER_PATCH := $(shell echo $(LIBVER_PATCH_SCRIPT))
LIBVER := $(LIBVER_MAJOR).$(LIBVER_MINOR).$(LIBVER_PATCH)

CURDIR:=$(PWD)

OPTFLAGS := -O3 -fomit-frame-pointer -fpie -fPIC -std=gnu11

DEBUGFLAGS := -Wall -Wextra -Wconversion -Wcast-qual -Wcast-align -Wshadow \
	      -Wstrict-aliasing=1 -Wswitch-enum -Wdeclaration-after-statement \
              -Wstrict-prototypes -Wundef -Wpointer-arith -Wformat-security \
              -Wvla -Wformat=2 -Winit-self -Wfloat-equal -Wwrite-strings \
              -Wredundant-decls -Wstrict-overflow=2 \
              -Werror -Wstrict-aliasing

CFLAGS  = -g $(OPTFLAGS) $(DEBUGFLAGS) -pipe
CPPFLAGS = -c -I$(CURDIR) -D_GNU_SOURCE
LIBS =
LDFLAGS = -shared
ARFLAGS = rcs


ifdef ENABLE_TRACER
	CPPFLAGS += -DENABLE_TRACER
endif

LIBCUCKOO := libcuckoo
LIBSTATIC := $(LIBCUCKOO).a

SONAME_FLAGS = -Wl,-soname=$(LIBNAME).$(SHARED_EXT).$(LIBVER_MAJOR)
SHARED_EXT = so
SHARED_EXT_MAJOR = $(SHARED_EXT).$(LIBVER_MAJOR)
SHARED_EXT_VER = $(SHARED_EXT).$(LIBVER)
LIBDYNAMIC = $(LIBCUCKOO).$(SHARED_EXT_VER)

SRCS = \
	cuckoohash.c \
        xxhash.c

OBJS = ${SRCS:.c=.o}

.SUFFIXES:	.o .c
.PHONY:	all
all:	lib test
.c.o:
	$(CC) $(CFLAGS) $(CPPFLAGS) $<

$(OBJS):	Makefile xxhash.h index_queue.h cuckoohash.h

# library
$(LIBSTATIC):	$(OBJS)
	$(AR) $(ARFLAGS) $@ $^

$(LIBDYNAMIC):	$(OBJS)
	$(CC) $(FLAGS) $^ $(LDFLAGS) $(SONAME_FLAGS) -o $@
	ln -sf $@ $(LIBCUCKOO).$(SHARED_EXT_MAJOR)
	ln -sf $@ $(LIBCUCKOO).$(SHARED_EXT)

.PHONY: lib
lib:  ## generate static and dynamic chtbl libraries
lib: $(LIBSTATIC) $(LIBDYNAMIC)

.PHONY: clean
clean:  ## remove all build artifacts
	$(Q)$(RM) core *.o *.$(SHARED_EXT) *.$(SHARED_EXT).* *.a
	$(MAKE) -C tests clean
	@echo cleaning completed

.PHONY: test
test:	lib
	$(MAKE) -C tests


