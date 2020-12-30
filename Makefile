CC := gcc
CFLAGS := -O3 -D PRINTON
LDFLAGS := -lm -static -pthread

GLZA: GLZA.c GLZAcomp.c GLZAformat.c GLZAcompress.c GLZAencode.c GLZAdecode.c GLZAmodel.c
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
