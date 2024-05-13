#
# SPDX-License-Identifier: BSD-2-Clause
# Copyright(c) 2024 deadcafe.beef@gmail.com. All rights reserved.
#

CURDIR:=$(PWD)

#OPTFLAGS := -O3 -march=native -mrtm -mavx2 -msse4.1 -msse4.2 -mcrc32 -mmovbe -mbmi -fomit-frame-pointer -fpie -fpic
OPTFLAGS := -O3 -march=native -fomit-frame-pointer -fpie -fpic

CFLAGS  = -g $(OPTFLAGS) -Werror -Wextra -Wall -Wstrict-aliasing -std=gnu11 -pipe
CPPFLAGS = -c -I$(CURDIR) -D_GNU_SOURCE -DENABLE_UINIT_TEST
LIBS =
LDFLAGS =

#CFLAGS += -funroll-loops -frerun-loop-opt
#CFLAGS += -fforce-addr

ifdef ENABLE_PAPI
CPPFLAGS += -DENABLE_PAPI
LIBS += -lpapi
endif

ifdef ENABLE_TRACER
CPPFLAGS += -DENABLE_TRACER
endif

SRCS    =       \
	cuckoohash.c \
	main.c

OBJS = ${SRCS:.c=.o}
DEPENDS = .depend
TARGET = cuckoo

.SUFFIXES:	.o .c
.PHONY:	all clean depend
all:	depend $(TARGET)
.c.o:
	$(CC) $(CFLAGS) $(CPPFLAGS) $<

$(TARGET):	$(OBJS)
	$(CC) -o $@ $^ $(LIBS) $(LDFLAGS)

$(OBJS):	Makefile

clean:
	rm -f $(OBJS) $(TARGET) $(DEPENDS) *~ core core.*

depend:	$(SRCS) Makefile
	-@ $(CC) $(CPPFLAGS) -MM -MG $(SRCS) > $(DEPENDS)

-include $(DEPENDS)
