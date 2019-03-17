/* Runtime library */

# include <stdio.h>
# include <stdio.h>
# include <malloc.h>
# include <string.h>
# include <stdarg.h>
# include <alloca.h>
# include <stdlib.h>

# define STRING_TAG 0x00000000
# define ARRAY_TAG  0x01000000
# define SEXP_TAG   0x02000000

# define LEN(x) (x & 0x00FFFFFF)
# define TAG(x) (x & 0xFF000000)

# define TO_DATA(x) ((data*)((char*)(x)-sizeof(int)))
# define TO_SEXP(x) ((sexp*)((char*)(x)-2*sizeof(int)))

# define UNBOXED(x) (((int) (x)) & 0x0001)
# define UNBOX(x)   (((int) (x)) >> 1)
# define BOX(x)     ((((int) (x)) << 1) | 0x0001)

typedef struct {
  int tag; 
  char contents[0];
} data; 

typedef struct {
  int tag; 
  data contents; 
} sexp; 

extern int Blength (void *p) {
  data *a = TO_DATA(p);
  return BOX(LEN(a->tag));
}

extern void* Belem (void *p, int i) {
  //printf("Belem: %d[%d]\n", (int)p, UNBOX(i));
  
  data *a = TO_DATA(p);
  i = UNBOX(i);
  
  
  if (TAG(a->tag) == STRING_TAG) {
    return (void*) BOX(a->contents[i]);
  }
  
  void* result = (void*) ((int*) a->contents)[i];

  return result;
}

extern void* Bstring (void *p) {
  int n = strlen (p);
  data *r = (data*) malloc (n + 1 + sizeof (int));

  r->tag = n;
  strncpy (r->contents, p, n + 1);
  
  return r->contents;
}

extern void* Barray (int n, ...) {
  n = UNBOX(n);
  va_list args;
  int i;
  data *r = (data*) malloc (sizeof(int) * (n+1));

  r->tag = ARRAY_TAG | n;
  
  va_start(args, n);
  
  for (i=0; i<n; i++) {
    int ai = va_arg(args, int);
    ((int*)r->contents)[i] = ai; 
  }
  
  va_end(args);

  return r->contents;
}
		 
extern void Bsta (void *s, int n, int v, ...) {
  //printf("Bsta(%d, %d, %d, ", (int)s, n, v);
  
  va_list args;
  int i, k;
  data *a;
	
  va_start(args, v);

  for (i=0; i<n-1; i++) {
	k = UNBOX(va_arg(args, int));
	s = ((int**) s) [k];
  }

 // printf("%d)\n", k);
  
  k = UNBOX(va_arg(args, int));
  a = TO_DATA(s);  
  
  if (TAG(a->tag) == STRING_TAG)((char*) s)[k] = (char) UNBOX(v);
  else ((int*) s)[k] = v;
}

extern int Lraw (int x) {
  return UNBOX(x);
}

extern void Lprintf (char *s, ...) {
  va_list args;

  va_start (args, s);
  vprintf  (s, args); // vprintf (char *, va_list) <-> printf (char *, ...) 
  va_end   (args);
}

extern void* Lstrcat (void *a, void *b) {
  data *da = TO_DATA(a);
  data *db = TO_DATA(b);
  
  data *d  = (data *) malloc (sizeof(int) + LEN(da->tag) + LEN(db->tag) + 1);

  d->tag = LEN(da->tag) + LEN(db->tag);

  strcpy (d->contents, da->contents);
  strcat (d->contents, db->contents);

  return d->contents;
}

extern void Lfprintf (FILE *f, char *s, ...) {
  va_list args;

  va_start (args, s);
  vfprintf (f, s, args);
  va_end   (args);
}

extern FILE* Lfopen (char *f, char *m) {
  return fopen (f, m);
}

extern void Lfclose (FILE *f) {
  fclose (f);
}

extern int Lread () {
  int result;

  printf ("> "); 
  fflush (stdout);
  scanf  ("%d", &result);

  return BOX(result);
}

extern int Lwrite (int n) {
  printf ("%d\n", UNBOX(n));
  fflush (stdout);

  return 0;
}