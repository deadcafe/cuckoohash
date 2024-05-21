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

CP = cp
NM = nm
GREP = grep
CUCKOO_DIR = ..
TARGET = $(CUCKOO_DIR)/cktest

OPTFLAGS := -O3 -march=native -fomit-frame-pointer -std=gnu11
DEBUGFLAGS := -Wall -Wextra -Wconversion -Wcast-qual -Wcast-align -Wshadow \
	      -Wstrict-aliasing=1 -Wswitch-enum -Wdeclaration-after-statement \
              -Wstrict-prototypes -Wundef -Wpointer-arith -Wformat-security \
              -Wvla -Wformat=2 -Winit-self -Wfloat-equal -Wwrite-strings \
              -Wredundant-decls -Wstrict-overflow=2 \
              -Werror -Wstrict-aliasing

CFLAGS  = -g $(OPTFLAGS) $(DEBUGFLAGS) -pipe
CPPFLAGS = -c -I$(CUCKOO_DIR) -I. -D_GNU_SOURCE
LIBS = -lcuckoo
LDFLAGS = -L$(CUCKOO_DIR) -static

ifdef ENABLE_PAPI
	CPPFLAGS += -DENABLE_PAPI
        LIBS += -lpapi
endif

SRCS    =       \
	tinyallocator.c \
	unittp.c

OBJS = ${SRCS:.c=.o}
DEPENDS = .depend

.SUFFIXES:      .o .c
.PHONY: all clean depend
all:	depend $(TARGET)
.c.o:
	$(CC) $(CFLAGS) $(CPPFLAGS) $<

$(TARGET): $(OBJS)
	$(CC) -o $@ $^ $(LIBS) $(LDFLAGS)

$(OBJS): Makefile

clean:
	$(RM) -f $(OBJS) $(TARGET) $(DEPENDS) *~ core core.*

depend: $(SRCS) Makefile
	-@ $(CC) $(CPPFLAGS) -MM -MG $(SRCS) > $(DEPENDS)

-include $(DEPENDS)
