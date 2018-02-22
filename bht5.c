/*
 * bht v0.2 (beta)
 * beck hash table , is a program for educational purposes
 * it can be useful for a database with a key and a value , value can be a 
 * string with delimeters to allow more complex structures into it.
 * program does not have encryption.
 * delete table is going to save the deleted hashes , and to read it after
 * when using "sync" to synchronize the database.
 * delete_bht , dump_bht & sync_bht are beta.
 * you can archive files with a single key , delete data , dump all the database , insert and select
 * my delete_bht has been finished , you can trust in this function for now
 * by
 * Eduardo Ruiz Duarte
 * rduarte@ciencias.unam.mx
 */
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <ctype.h>
#include <stdlib.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#ifndef PROTOTYPES
#define PROTOTYPES 0
#endif




typedef unsigned char *POINTER;
typedef unsigned short int UINT2;
typedef unsigned long int UINT4;
#if PROTOTYPES
#define PROTO_LIST(list) list
#else
#define PROTO_LIST(list) ()
#endif
#define BUF_SIZE 1024
typedef struct
{
  UINT4 state[4];
  UINT4 count[2];
  unsigned char buffer[64];
} MD5_CTX;
#define FALSE 0
#define TRUE 1
#define DB_FH 0
#define MAX_ENTRIES 1500000
#define DB_SIZE 2173741824	/* casi 2^31 (1 Gb) */
#define MAX_KEYSTR 512
#define MASK_BOUND 0x000fffff

typedef struct db_header
{
  uint32_t id;
  uint32_t last_entry;
  uint32_t last_seq;
} dbheader_t;

typedef struct hash
{
  uint32_t data_init;
  uint32_t data_final;
  uint32_t data_seq;
  uint64_t hashval;
} hash_t;

struct select_t
{
  uint8_t *data;
  size_t datasiz;
  hash_t *db;
};
uint32_t gblsiz = 0;
int32_t mkbht (int8_t * filename);
hash_t *open_bht (int8_t * filename, uint32_t siz);
void insert_bht (uint8_t * filename, uint8_t * key, uint8_t * value,
		 uint32_t val_len);
struct select_t select_bht (uint8_t * filename, uint8_t *);
void MD5Init PROTO_LIST ((MD5_CTX *));
void unmapfile (void *addr, uint32_t dsiz);
void dump_bht (uint8_t * filename);
void MD5Update PROTO_LIST ((MD5_CTX *, unsigned char *, unsigned int));
void MD5Final PROTO_LIST ((unsigned char[16], MD5_CTX *));
void muestramd5_humano (uint8_t * md5);
void md5cadena (uint8_t * md5, uint8_t * datos, uint8_t datos_len);
void delete_bht (uint8_t * filename, uint8_t * key);
uint8_t *mapfile (uint8_t * filename);
uint32_t crc32 (const void *buf, size_t size);
int32_t close_bht (hash_t * ptr);
void help (uint8_t * filename);

/* Global variables for handling just 1 db in Memory for interative mode with option -F */
uint8_t fastio = 0;
hash_t *global_htdb;

uint8_t *
mapfile (uint8_t * filename)
{
  struct stat stval;
  uint8_t *value;
  int32_t fdvalue;
  fprintf (stderr, "Mapping file as a value\n");
  if (stat ((char *) filename, &stval) != 0)
    {
      fprintf (stderr, "File does not exists for mapping\n");
      perror ("stat");
      exit (EXIT_FAILURE);
    }
  fdvalue = open ((char *) filename, O_RDONLY, S_IRUSR);
  if (fdvalue < 0)
    {
      fprintf (stderr, "Couldnt open file for insertion\n");
      perror ("open");
      exit (EXIT_FAILURE);
    }
  value = mmap (0, stval.st_size, PROT_READ, MAP_SHARED, fdvalue, 0);
  close (fdvalue);
  if (value == NULL)
    {
      fprintf (stderr, "Couldnt mmap file for insertion\n");
      perror ("mmap");
      close (fdvalue);
      exit (EXIT_FAILURE);
    }
  return value;
}

void
unmapfile (void *addr, uint32_t dsiz)
{
  if (munmap (addr, dsiz) != 0)
    {
      fprintf (stderr, "Error unmapping file\n");
      perror ("munmap");
      exit (EXIT_FAILURE);
    }
  return;
}

uint32_t
hash_function (uint8_t * key, uint32_t len, void *bhash)
{
  uint32_t hash_id;

  uint8_t strmd5[16];

  memset(bhash,0x0,sizeof(uint64_t));
  md5cadena ((uint8_t *) & strmd5, key, strlen ((char *) key));
  memcpy (&hash_id, &strmd5, sizeof (uint32_t));
  memcpy (bhash, &strmd5, sizeof(uint64_t));
  hash_id ^= ~crc32 (key, len);
  hash_id = ((hash_id) * sizeof (hash_t)) & MASK_BOUND;
#ifdef DEBUG
printf("Hash_id(%s)=%x\n",key,hash_id);
#endif
  return hash_id;
}

struct select_t
select_bht (uint8_t * filename, uint8_t * key)
{
  uint32_t hash_id;
  uint8_t *bhandler;
  struct select_t sl;
  uint64_t bighash = 0;
  dbheader_t *hdr;
  hash_t *htdb, *backup;
/*
  if (!fastio)
    htdb = open_bht ((int8_t *) filename, 0);
*/
      if (global_htdb != 0x0)
	htdb = global_htdb;
      else
	htdb = open_bht ((int8_t *) filename, 0);
      global_htdb = htdb;

  backup = htdb;
  bhandler = (uint8_t *) htdb;
  hash_id = hash_function (key, strlen ((char *) key), &bighash);
  hdr = (dbheader_t *) htdb;
  htdb = htdb + hash_id ;
#ifdef DEBUG
  printf ("Data is in %d - %d offsets, hashid=%x, bighash=%016llx \n", htdb->data_init, htdb->data_final,hash_id,bighash);
  printf ("Current offset %d\n",
	  (int) (MASK_BOUND * sizeof (hash_t)) + htdb->data_init);
#endif
  bhandler = bhandler + ((MASK_BOUND) * sizeof (hash_t)) + htdb->data_init;
  sl.data = bhandler;
  sl.datasiz = htdb->data_final - htdb->data_init;
  
#ifdef DEBUG
  if(htdb->hashval != 0) 
#endif
  if(htdb->hashval != bighash)  {
#ifdef DEBUG
        printf("Nothing to select, maybe collision but fixed, hash_slot=%x, slot_bigvalue=%016llx, curr_hash=%016llx\n",hash_id,htdb->hashval,bighash);
#endif
	sl.datasiz = 0;
	sl.data = NULL;
  }

  sl.db = backup;
  return sl;
}

void
dump_bht (uint8_t * filename)
{
  hash_t *htdb, *backup;
  uint32_t last;
  uint8_t *data;
  dbheader_t *hdr;
  fprintf (stderr, "Beggining dump of database\n");
  htdb = open_bht ((int8_t *) filename, 0);
  backup = htdb;
  hdr = (dbheader_t *) backup;
  last = hdr->last_seq;
  /* First element is "special" */
  htdb += last;
  data = (uint8_t *) backup + sizeof (hash_t) * MASK_BOUND;
  data += htdb->data_init;
  fprintf (stderr, "[%06x]: -> ",
	   (htdb->data_seq ^ 0xffffffff) ^ MASK_BOUND);
  write (2, data, htdb->data_final - htdb->data_init);
  fprintf (stderr, "\n");
/* We are going to jump to the sequence numbers of the hashes */
  while (htdb->data_seq != 0)
    {
      fprintf (stderr, "[%06x]: -> ", htdb->data_seq);
      htdb = backup + htdb->data_seq;
      data = (uint8_t *) backup + sizeof (hash_t) * MASK_BOUND;
      data += htdb->data_init;
      /* i dont want to malloc and i dont know the size of the data so ill write the difference */
      write (2, data, htdb->data_final - htdb->data_init);
      fprintf (stderr, "\n");
    }
  close_bht (backup);
  exit (0);
}

/* fucking complicated */
void
sync_bht (hash_t * htdb, hash_t deleted, uint32_t dbsiz, uint32_t nlink)
{
  hash_t *backup, *link;
  uint32_t i = 0, last, diffrem, seq_save[2], cpbytes;
  uint8_t *chandler;
  dbheader_t *hdr;
  backup = htdb;
  link = backup;
  hdr = (dbheader_t *) backup;
  last = hdr->last_seq;
  diffrem = deleted.data_final - deleted.data_init;
  printf ("diff rem = %d\n", diffrem);
  htdb = backup + last;

  while (1)
    {
      /* Save the current sequence (the entry that was before the current) */
      /* We are going backwards */

      seq_save[i % 3] = htdb->data_seq;
      if (i > 0)
	htdb = backup + seq_save[i % 3];
      /*seq_save = htdb->data_seq; */

      /* We substract the size of the deleted data to all the offsets after the deleted offset */
      if (htdb->data_seq != 0)
	{
	  htdb->data_init -= diffrem;
	  htdb->data_final -= diffrem;
	}
      /* If now we are in the deleted element we need to link the neighborhood of this element */
      if (htdb->data_seq == 0)
	{
	  printf ("Linking nodes: %x <--> %x\n", nlink,
		  seq_save[((i - 1) % 3)]);
	  htdb->data_init = 0;
	  htdb->data_final = 0;
	  htdb = backup + seq_save[(i - 1) % 3];
	  htdb->data_seq = nlink;
	  break;
	}
      i++;

    }
  /* Pointing to the hash of the deleted data (i was 2 hours here.. because the fucking data type , increment 
   * of "1" with a non "1" byte type is 1*sizeof(type) so i used uint8_t (fuck) */
  htdb = backup;
  chandler = (uint8_t *) htdb;
  chandler += (MASK_BOUND * sizeof (hash_t)) + deleted.data_init;
  /* Copying the rest of the file to overwrite deleted data */
  cpbytes =
    dbsiz - (deleted.data_init + (sizeof (hash_t) * MASK_BOUND) + diffrem);
  memcpy (chandler, chandler + diffrem, cpbytes);

}

void
delete_bht (uint8_t * filename, uint8_t * key)
{
  uint32_t hash_id, i, datasize, newsize, nlink;
  uint64_t bighash;
  uint8_t *bhandler;
  struct stat tr;
  dbheader_t *hdr;
  hash_t *htdb, *backup, del;

  if (stat ((char *) filename, &tr) != 0)
    {
      fprintf (stderr, "File %s does not exists\n", filename);
      perror ("stat");
      exit (EXIT_FAILURE);
    }
  htdb = open_bht ((int8_t *) filename, 0);
  backup = htdb;
  bhandler = (uint8_t *) htdb;
  hash_id = hash_function (key, strlen ((char *) key),&bighash);
  hdr = (dbheader_t *) htdb;
  htdb = htdb + hash_id;
  bhandler = bhandler + (MASK_BOUND * sizeof (hash_t)) + htdb->data_init;
  datasize = htdb->data_final - htdb->data_init;



  if(htdb->hashval != bighash) {
	if(htdb->hashval == 0) {
		fprintf(stderr,"Nothing to delete in %x, bighash=%x not found in slot\n",hash_id,bighash);
		close_bht(backup);
		return;
	}
	else {
	 	fprintf(stderr,"Nothing to delete in %x, collision but handled with bighash=%x\n",hash_id,bighash);
		close_bht(backup);
		return;
	}
   }


  /* Superimportant , with this line the delete method passed from beta to release , this decrements the size of 
   * the last entry pointer when deleted, i dunno why i forgot it */
  hdr->last_entry -= datasize;
  nlink = htdb->data_seq;
  printf ("final=%d\ninit=%d\n", htdb->data_final, htdb->data_init);
  if (htdb->data_final + htdb->data_init + htdb->data_seq == 0)
    {
      fprintf (stderr, "Entry %d already free\n", hash_id);
      exit (EXIT_FAILURE);
    }
  else
    for (i = 0; i < datasize; i++)
      bhandler[i] = 0;
  del.data_final = htdb->data_final;
  del.data_init = htdb->data_init;
  del.data_seq = hash_id;	/*Used data_seq to save the hash of the deleted value */
  htdb->data_final = 0;
  htdb->data_init = 0;
  htdb->data_seq = 0;

  fprintf (stderr, "Syncing..\n");
  sync_bht (backup, del, tr.st_size, nlink);
  fprintf (stderr, "Synced\n");
  close_bht (backup);
  truncate ((char *) filename,
	    (newsize = tr.st_size - (del.data_final - del.data_init)));
  return;
}

void
insert_bht (uint8_t * dbfile, uint8_t * key, uint8_t * value,
	    uint32_t val_len)
{
  dbheader_t *hdr;
  uint32_t hash_id;
  uint8_t *bhandler;
  struct stat dbft;
  uint64_t bighash;
  hash_t *htdb, *backup;
  if (stat ((char *) dbfile, &dbft) < 0)
    {
      perror ("stat");
      exit (EXIT_FAILURE);
    }
  htdb = open_bht ((int8_t *) dbfile, dbft.st_size + val_len);
  backup = htdb;
  gblsiz = dbft.st_size + val_len;
  hdr = (dbheader_t *) htdb;
  hash_id = hash_function (key, strlen ((char *) key),&bighash);
  bhandler = (uint8_t *) htdb;
  htdb = htdb + hash_id;


  if ((htdb->data_init == 0) && (htdb->data_final == 0))
    {
      hdr->last_entry += val_len;
      htdb->data_init = hdr->last_entry - val_len;
      htdb->data_final = hdr->last_entry;
      htdb->data_seq = hdr->last_seq;
      htdb->hashval = bighash;
      hdr->last_seq = hash_id;
    }
  else
    {
      fprintf (stdout,
	       "########### An entry on %d already exists use -u for update or -d for delete ########\n",
	       hash_id);
      close_bht (htdb - hash_id);
      exit (EXIT_FAILURE);
    }
  bhandler += (MASK_BOUND* sizeof (hash_t)) + hdr->last_entry - val_len;
  printf ("Offset for insertion is %d\n",
	  (int) ((MASK_BOUND * sizeof (hash_t)) + hdr->last_entry -
		 val_len));
  printf ("Copying value=%s\n", value);
  memcpy (bhandler, value, val_len);
#ifdef DEBUG
  printf ("New entry at [%d]\n", hash_id);
  printf ("Closing db\n");
#endif
  close_bht (backup);
  return;
}


int32_t
close_bht (hash_t * ptr)
{
  if (munmap (ptr, gblsiz) == 0)
    return TRUE;
  else
    {
      perror ("munmap");
      return FALSE;
    }
  return -1;
}

hash_t *
open_bht (int8_t * filename, uint32_t siz)
{
  hash_t *ret;
  int32_t ht;
  struct stat htft;
  gblsiz = siz;

  if ((ht = open ((char *) filename, O_RDWR, S_IRWXU)) < 0)
    {
      perror ("open");
      exit (EXIT_FAILURE);
    }
  if (fstat (ht, &htft) < 0)
    {
      perror ("fstat");
      exit (EXIT_FAILURE);
    }
  if (siz != 0)
    ftruncate (ht, siz);
  else
    siz = htft.st_size;
  gblsiz = siz;
  if ((ret =
       mmap (NULL, siz, PROT_WRITE | PROT_READ, MAP_SHARED, ht, 0)) == NULL)
    {
      perror ("mmap");
      close (ht);
      exit (EXIT_FAILURE);
    }
  close (ht);
  return ret;
}

int32_t
mkbht (int8_t * filename)
{

  int32_t ht, i;
  hash_t cero;
  hash_t *ptr;
  dbheader_t hdr;
  cero.data_init = 0L;
  cero.data_final = 0L;
  cero.data_seq = 0L;
  cero.hashval = 0LL;
  memset(&cero,0x0,sizeof(hash_t));
  if ((ht = open ((char *) filename, O_RDWR | O_CREAT, S_IRWXU)) < 0)
    {
      perror ("open");
      return FALSE;
    }
  gblsiz = MASK_BOUND * sizeof (hash_t);
  if ((ptr =
       mmap (NULL, gblsiz,
	     PROT_WRITE | PROT_READ, MAP_SHARED, ht, 0)) == NULL)
    {
      perror ("mmap");
      close (ht);
      return FALSE;
    }
  printf ("Creating hash table null entries...\n");
  for (i = 0; i < MASK_BOUND; i++)
    write (ht, &cero, sizeof (hash_t));
  close (ht);
  hdr.id = DB_FH;
  hdr.last_entry = 0;
  hdr.last_seq = 0;
  memcpy (ptr, &hdr, sizeof (dbheader_t));	/* Must be 4 bytes */
  munmap (ptr, gblsiz);
  return TRUE;
}

void
help (uint8_t * filename)
{
  fprintf (stderr,
	   "bht v0.1 by Eduardo Ruiz Duarte: rduarte@ciencias.unam.mx\n");
  fprintf (stderr,
	   "Usage: First argument (argv[1]) must be -s or -i or -I (select or insert or interactive select)\n");
  fprintf (stderr,
	   "then if you are using -s you need to specify -k key and -d databasefile (order has no significance)\n");
  fprintf (stderr,
	   "if you are using -i you need to specify -k key -d databasefile and -v [-f file] valueofkey (order has no significance)\n");
  fprintf (stderr,
	   "With interactive mode you can specify -F after the name of the database for fast IO\n");


  fprintf (stderr,
	   "You can dump all the database with -a , and remove keys with -r\nSee the examples:\n");
  fprintf (stderr,
	   "Example inserting:\n$ %s -i -k someusername -v somepasswordforusername -d password.db\n\n",
	   filename);
  fprintf (stderr,
	   "Example inserting a file\n$ %s -i -k someidentifier -v -f somefile.extension -d somedb.db\n\n",
	   filename);
  fprintf (stderr,
	   "Example searching:\n$ %s -s -k someusername -d password.db\n\n",
	   filename);
  fprintf (stderr,
	   "Example removing:\n$ %s -r -k someusername -d password.db\n\n",
	   filename);
  fprintf (stderr,
	   "Example interactive search with fast IO:\n$ %s -I -d password.db -F\n\n",
	   filename);
  fprintf (stderr, "Example dumping all:\n$ %s -a -d password.db\n\n",
	   filename);

  exit (EXIT_FAILURE);
}

/*
 * Utileria para calcular MD5
 * usando la libreria de dominio publico
 * de MD5 de Ron Rivest 
 * opciones son las siguientes:
 * -s PALABRA      <--- Esta opcion causara dar el MD5 de "PALABRA"
 * -f archivo.ext  <--- Esta opcion causara dar el MD5 de los datos contenidos en archivo.ext
 *  Ejemplo:
 *  compilamos: 
 *  $ gcc -Wall -O3 -funroll-loops mimd5.c -o mimd5
 *  Sacamos MD5 de una palabra sin el \n (0x0a)
 *  $ ./mimd5 -s PALABRA
 *  md5 = b03a64941de342cabfabf4d9b580c8c0
 *  Sacamod MD5 de archivo:
 *  $ ./mimd5 -f /etc/passwd
 *  md5 = 596768f75cb50f03b08c8c39adac6226
 * 
 * Si desean implementar esto en alguno de sus programas solo quiten la seccion main() de este programa
 * incluyan este archivo como objeto en su ejecutable y usen las funciones que implemente de la sigueinte forma:
 *
 * si quieren calcular el MD5 de una cadena hagan
 *
 *
 * md5cadena (md5, datos, tamanio_de_datos);
 *
 * donde "md5" es el buffer donde se guardara el MD5 crudo.. este de preferencia debe de ser "unsigned char *md5"
 * datos es el apuntador a los datos que se calculara md5 tambien es "unsigned char *datos"
 * tamanio_de_datos es el entero que denota cuantos bytes leer del apuntador "datos" y es "unsigned int tamanio_de_datos"
 *
 * despues debemos de mostrar el MD5 en formato humano.. entonces haremos
 *
 * muestramd5_humano(md5);
 * donde "md5" es lo que se obtubo de datos MD5 crudos
 *
 * Si se quiere calcular el MD5 de un archivo debe de hacerse
 *
 * md5archivo("/path/al/archivo.ext",md5);
 *
 * donde "/path/al/archivo.ext" es el archivo del cual se extraeran los datos para calcular el MD5
 * y "md5" es donde se guardara el md5.. ambos son "unsigned char *"
 * 
 * Realmente es muy sencillo
 * pero cualquier duda haganmela saber... nose si esto era lo que querian.. pero en un principio me dijeron que es esto
 * pero si requieren otra cosa , haganmela saber a detalle.
 *
 * por
 * Eduardo Ruiz
 * rduarte@ciencias.unam.mx
 */

void
md5archivo (int8_t * archivo, uint8_t * md5)
{
  int32_t sobrante, partes, i, archfd;
  struct stat arch_stat;
  uint8_t buf[BUF_SIZE];
  MD5_CTX md5_context;
  if ((archfd = open ((char *) archivo, O_RDONLY)) < 0)
    {
      fprintf (stderr, "No se pudo abrir archivo\n");
      perror ("open");
      exit (-1);
    }
  fstat (archfd, &arch_stat);
  partes = arch_stat.st_size / BUF_SIZE;
  if ((sobrante = (arch_stat.st_size % BUF_SIZE)) != 0)
    partes = (arch_stat.st_size / BUF_SIZE) + 1;
  MD5Init (&md5_context);
  if (sobrante != 0)
    for (i = 0; i < partes; i++)
      {
	if (i != partes - 1)
	  {
	    read (archfd, (uint8_t *) & buf, BUF_SIZE);
	    MD5Update (&md5_context, buf, BUF_SIZE);
	  }
	if (i == partes - 1)
	  {
	    read (archfd, (uint8_t *) & buf, sobrante);
	    MD5Update (&md5_context, buf, sobrante);
	    close (archfd);
	    break;
	  }
      }
  if (sobrante == 0)
    for (i = 0; i < partes; i++)
      {
	read (archfd, (uint8_t *) & buf, BUF_SIZE);
	MD5Update (&md5_context, buf, BUF_SIZE);
      }

  close (archfd);
  MD5Final (md5, &md5_context);
  return;
}

void
md5cadena (uint8_t * md5, uint8_t * datos, uint8_t datos_len)
{

  MD5_CTX context;
  MD5Init (&context);
  MD5Update (&context, datos, datos_len);
  MD5Final (md5, &context);

  return;
}

void
muestramd5_humano (uint8_t * md5)
{
  int32_t i;
  printf ("md5 = ");
  for (i = 0; i < 16; i++)
    printf ("%02x", md5[i]);
  printf ("\n");
  return;
}

#define S11 7
#define S12 12
#define S13 17
#define S14 22
#define S21 5
#define S22 9
#define S23 14
#define S24 20
#define S31 4
#define S32 11
#define S33 16
#define S34 23
#define S41 6
#define S42 10
#define S43 15
#define S44 21

static void MD5Transform PROTO_LIST ((UINT4[4], unsigned char[64]));
static void Encode PROTO_LIST ((unsigned char *, UINT4 *, unsigned int));
static void Decode PROTO_LIST ((UINT4 *, unsigned char *, unsigned int));
static void MD5_memcpy PROTO_LIST ((POINTER, POINTER, unsigned int));
static void MD5_memset PROTO_LIST ((POINTER, int, unsigned int));

static unsigned char PADDING[64] = {
  0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};

#define F(x, y, z) (((x) & (y)) | ((~x) & (z)))
#define G(x, y, z) (((x) & (z)) | ((y) & (~z)))
#define H(x, y, z) ((x) ^ (y) ^ (z))
#define I(x, y, z) ((y) ^ ((x) | (~z)))
#define ROTATE_LEFT(x, n) (((x) << (n)) | ((x) >> (32-(n))))

#define FF(a, b, c, d, x, s, ac) { \
 (a) += F ((b), (c), (d)) + (x) + (UINT4)(ac); \
 (a) = ROTATE_LEFT ((a), (s)); \
 (a) += (b); \
  }
#define GG(a, b, c, d, x, s, ac) { \
 (a) += G ((b), (c), (d)) + (x) + (UINT4)(ac); \
 (a) = ROTATE_LEFT ((a), (s)); \
 (a) += (b); \
  }
#define HH(a, b, c, d, x, s, ac) { \
 (a) += H ((b), (c), (d)) + (x) + (UINT4)(ac); \
 (a) = ROTATE_LEFT ((a), (s)); \
 (a) += (b); \
  }
#define II(a, b, c, d, x, s, ac) { \
 (a) += I ((b), (c), (d)) + (x) + (UINT4)(ac); \
 (a) = ROTATE_LEFT ((a), (s)); \
 (a) += (b); \
  }

void
MD5Init (context)
     MD5_CTX *context;
{
  context->count[0] = context->count[1] = 0;
  context->state[0] = 0x67452301;
  context->state[1] = 0xefcdab89;
  context->state[2] = 0x98badcfe;
  context->state[3] = 0x10325476;
}

void
MD5Update (context, input, inputLen)
     MD5_CTX *context;
     unsigned char *input;
     unsigned int inputLen;
{
  unsigned int i, index, partLen;

  index = (unsigned int) ((context->count[0] >> 3) & 0x3F);

  if ((context->count[0] += ((UINT4) inputLen << 3))
      < ((UINT4) inputLen << 3))
    context->count[1]++;
  context->count[1] += ((UINT4) inputLen >> 29);

  partLen = 64 - index;

  if (inputLen >= partLen)
    {
      MD5_memcpy
	((POINTER) & context->buffer[index], (POINTER) input, partLen);
      MD5Transform (context->state, context->buffer);

      for (i = partLen; i + 63 < inputLen; i += 64)
	MD5Transform (context->state, &input[i]);

      index = 0;
    }
  else
    i = 0;

  MD5_memcpy
    ((POINTER) & context->buffer[index], (POINTER) & input[i], inputLen - i);
}

void
MD5Final (digest, context)
     unsigned char digest[16];
     MD5_CTX *context;
{
  unsigned char bits[8];
  unsigned int index, padLen;

  Encode (bits, context->count, 8);

  index = (unsigned int) ((context->count[0] >> 3) & 0x3f);
  padLen = (index < 56) ? (56 - index) : (120 - index);
  MD5Update (context, PADDING, padLen);

  MD5Update (context, bits, 8);

  Encode (digest, context->state, 16);

  MD5_memset ((POINTER) context, 0, sizeof (*context));
}

static void
MD5Transform (state, block)
     UINT4 state[4];
     unsigned char block[64];
{
  UINT4 a = state[0], b = state[1], c = state[2], d = state[3], x[16];

  Decode (x, block, 64);

  FF (a, b, c, d, x[0], S11, 0xd76aa478);	/* 1 */
  FF (d, a, b, c, x[1], S12, 0xe8c7b756);	/* 2 */
  FF (c, d, a, b, x[2], S13, 0x242070db);	/* 3 */
  FF (b, c, d, a, x[3], S14, 0xc1bdceee);	/* 4 */
  FF (a, b, c, d, x[4], S11, 0xf57c0faf);	/* 5 */
  FF (d, a, b, c, x[5], S12, 0x4787c62a);	/* 6 */
  FF (c, d, a, b, x[6], S13, 0xa8304613);	/* 7 */
  FF (b, c, d, a, x[7], S14, 0xfd469501);	/* 8 */
  FF (a, b, c, d, x[8], S11, 0x698098d8);	/* 9 */
  FF (d, a, b, c, x[9], S12, 0x8b44f7af);	/* 10 */
  FF (c, d, a, b, x[10], S13, 0xffff5bb1);	/* 11 */
  FF (b, c, d, a, x[11], S14, 0x895cd7be);	/* 12 */
  FF (a, b, c, d, x[12], S11, 0x6b901122);	/* 13 */
  FF (d, a, b, c, x[13], S12, 0xfd987193);	/* 14 */
  FF (c, d, a, b, x[14], S13, 0xa679438e);	/* 15 */
  FF (b, c, d, a, x[15], S14, 0x49b40821);	/* 16 */

  GG (a, b, c, d, x[1], S21, 0xf61e2562);	/* 17 */
  GG (d, a, b, c, x[6], S22, 0xc040b340);	/* 18 */
  GG (c, d, a, b, x[11], S23, 0x265e5a51);	/* 19 */
  GG (b, c, d, a, x[0], S24, 0xe9b6c7aa);	/* 20 */
  GG (a, b, c, d, x[5], S21, 0xd62f105d);	/* 21 */
  GG (d, a, b, c, x[10], S22, 0x2441453);	/* 22 */
  GG (c, d, a, b, x[15], S23, 0xd8a1e681);	/* 23 */
  GG (b, c, d, a, x[4], S24, 0xe7d3fbc8);	/* 24 */
  GG (a, b, c, d, x[9], S21, 0x21e1cde6);	/* 25 */
  GG (d, a, b, c, x[14], S22, 0xc33707d6);	/* 26 */
  GG (c, d, a, b, x[3], S23, 0xf4d50d87);	/* 27 */
  GG (b, c, d, a, x[8], S24, 0x455a14ed);	/* 28 */
  GG (a, b, c, d, x[13], S21, 0xa9e3e905);	/* 29 */
  GG (d, a, b, c, x[2], S22, 0xfcefa3f8);	/* 30 */
  GG (c, d, a, b, x[7], S23, 0x676f02d9);	/* 31 */
  GG (b, c, d, a, x[12], S24, 0x8d2a4c8a);	/* 32 */

  HH (a, b, c, d, x[5], S31, 0xfffa3942);	/* 33 */
  HH (d, a, b, c, x[8], S32, 0x8771f681);	/* 34 */
  HH (c, d, a, b, x[11], S33, 0x6d9d6122);	/* 35 */
  HH (b, c, d, a, x[14], S34, 0xfde5380c);	/* 36 */
  HH (a, b, c, d, x[1], S31, 0xa4beea44);	/* 37 */
  HH (d, a, b, c, x[4], S32, 0x4bdecfa9);	/* 38 */
  HH (c, d, a, b, x[7], S33, 0xf6bb4b60);	/* 39 */
  HH (b, c, d, a, x[10], S34, 0xbebfbc70);	/* 40 */
  HH (a, b, c, d, x[13], S31, 0x289b7ec6);	/* 41 */
  HH (d, a, b, c, x[0], S32, 0xeaa127fa);	/* 42 */
  HH (c, d, a, b, x[3], S33, 0xd4ef3085);	/* 43 */
  HH (b, c, d, a, x[6], S34, 0x4881d05);	/* 44 */
  HH (a, b, c, d, x[9], S31, 0xd9d4d039);	/* 45 */
  HH (d, a, b, c, x[12], S32, 0xe6db99e5);	/* 46 */
  HH (c, d, a, b, x[15], S33, 0x1fa27cf8);	/* 47 */
  HH (b, c, d, a, x[2], S34, 0xc4ac5665);	/* 48 */

  II (a, b, c, d, x[0], S41, 0xf4292244);	/* 49 */
  II (d, a, b, c, x[7], S42, 0x432aff97);	/* 50 */
  II (c, d, a, b, x[14], S43, 0xab9423a7);	/* 51 */
  II (b, c, d, a, x[5], S44, 0xfc93a039);	/* 52 */
  II (a, b, c, d, x[12], S41, 0x655b59c3);	/* 53 */
  II (d, a, b, c, x[3], S42, 0x8f0ccc92);	/* 54 */
  II (c, d, a, b, x[10], S43, 0xffeff47d);	/* 55 */
  II (b, c, d, a, x[1], S44, 0x85845dd1);	/* 56 */
  II (a, b, c, d, x[8], S41, 0x6fa87e4f);	/* 57 */
  II (d, a, b, c, x[15], S42, 0xfe2ce6e0);	/* 58 */
  II (c, d, a, b, x[6], S43, 0xa3014314);	/* 59 */
  II (b, c, d, a, x[13], S44, 0x4e0811a1);	/* 60 */
  II (a, b, c, d, x[4], S41, 0xf7537e82);	/* 61 */
  II (d, a, b, c, x[11], S42, 0xbd3af235);	/* 62 */
  II (c, d, a, b, x[2], S43, 0x2ad7d2bb);	/* 63 */
  II (b, c, d, a, x[9], S44, 0xeb86d391);	/* 64 */

  state[0] += a;
  state[1] += b;
  state[2] += c;
  state[3] += d;

  MD5_memset ((POINTER) x, 0, sizeof (x));
}

static void
Encode (output, input, len)
     unsigned char *output;
     UINT4 *input;
     unsigned int len;
{
  unsigned int i, j;

  for (i = 0, j = 0; j < len; i++, j += 4)
    {
      output[j] = (unsigned char) (input[i] & 0xff);
      output[j + 1] = (unsigned char) ((input[i] >> 8) & 0xff);
      output[j + 2] = (unsigned char) ((input[i] >> 16) & 0xff);
      output[j + 3] = (unsigned char) ((input[i] >> 24) & 0xff);
    }
}

static void
Decode (output, input, len)
     UINT4 *output;
     unsigned char *input;
     unsigned int len;
{
  unsigned int i, j;

  for (i = 0, j = 0; j < len; i++, j += 4)
    output[i] = ((UINT4) input[j]) | (((UINT4) input[j + 1]) << 8) |
      (((UINT4) input[j + 2]) << 16) | (((UINT4) input[j + 3]) << 24);
}


static void
MD5_memcpy (output, input, len)
     POINTER output;
     POINTER input;
     unsigned int len;
{
  unsigned int i;

  for (i = 0; i < len; i++)
    output[i] = input[i];
}

static void
MD5_memset (output, value, len)
     POINTER output;
     int value;
     unsigned int len;
{
  unsigned int i;

  for (i = 0; i < len; i++)
    ((char *) output)[i] = (char) value;
}

uint32_t crc32_tab[] = {
  0x00000000, 0x77073096, 0xee0e612c, 0x990951ba, 0x076dc419, 0x706af48f,
  0xe963a535, 0x9e6495a3, 0x0edb8832, 0x79dcb8a4, 0xe0d5e91e, 0x97d2d988,
  0x09b64c2b, 0x7eb17cbd, 0xe7b82d07, 0x90bf1d91, 0x1db71064, 0x6ab020f2,
  0xf3b97148, 0x84be41de, 0x1adad47d, 0x6ddde4eb, 0xf4d4b551, 0x83d385c7,
  0x136c9856, 0x646ba8c0, 0xfd62f97a, 0x8a65c9ec, 0x14015c4f, 0x63066cd9,
  0xfa0f3d63, 0x8d080df5, 0x3b6e20c8, 0x4c69105e, 0xd56041e4, 0xa2677172,
  0x3c03e4d1, 0x4b04d447, 0xd20d85fd, 0xa50ab56b, 0x35b5a8fa, 0x42b2986c,
  0xdbbbc9d6, 0xacbcf940, 0x32d86ce3, 0x45df5c75, 0xdcd60dcf, 0xabd13d59,
  0x26d930ac, 0x51de003a, 0xc8d75180, 0xbfd06116, 0x21b4f4b5, 0x56b3c423,
  0xcfba9599, 0xb8bda50f, 0x2802b89e, 0x5f058808, 0xc60cd9b2, 0xb10be924,
  0x2f6f7c87, 0x58684c11, 0xc1611dab, 0xb6662d3d, 0x76dc4190, 0x01db7106,
  0x98d220bc, 0xefd5102a, 0x71b18589, 0x06b6b51f, 0x9fbfe4a5, 0xe8b8d433,
  0x7807c9a2, 0x0f00f934, 0x9609a88e, 0xe10e9818, 0x7f6a0dbb, 0x086d3d2d,
  0x91646c97, 0xe6635c01, 0x6b6b51f4, 0x1c6c6162, 0x856530d8, 0xf262004e,
  0x6c0695ed, 0x1b01a57b, 0x8208f4c1, 0xf50fc457, 0x65b0d9c6, 0x12b7e950,
  0x8bbeb8ea, 0xfcb9887c, 0x62dd1ddf, 0x15da2d49, 0x8cd37cf3, 0xfbd44c65,
  0x4db26158, 0x3ab551ce, 0xa3bc0074, 0xd4bb30e2, 0x4adfa541, 0x3dd895d7,
  0xa4d1c46d, 0xd3d6f4fb, 0x4369e96a, 0x346ed9fc, 0xad678846, 0xda60b8d0,
  0x44042d73, 0x33031de5, 0xaa0a4c5f, 0xdd0d7cc9, 0x5005713c, 0x270241aa,
  0xbe0b1010, 0xc90c2086, 0x5768b525, 0x206f85b3, 0xb966d409, 0xce61e49f,
  0x5edef90e, 0x29d9c998, 0xb0d09822, 0xc7d7a8b4, 0x59b33d17, 0x2eb40d81,
  0xb7bd5c3b, 0xc0ba6cad, 0xedb88320, 0x9abfb3b6, 0x03b6e20c, 0x74b1d29a,
  0xead54739, 0x9dd277af, 0x04db2615, 0x73dc1683, 0xe3630b12, 0x94643b84,
  0x0d6d6a3e, 0x7a6a5aa8, 0xe40ecf0b, 0x9309ff9d, 0x0a00ae27, 0x7d079eb1,
  0xf00f9344, 0x8708a3d2, 0x1e01f268, 0x6906c2fe, 0xf762575d, 0x806567cb,
  0x196c3671, 0x6e6b06e7, 0xfed41b76, 0x89d32be0, 0x10da7a5a, 0x67dd4acc,
  0xf9b9df6f, 0x8ebeeff9, 0x17b7be43, 0x60b08ed5, 0xd6d6a3e8, 0xa1d1937e,
  0x38d8c2c4, 0x4fdff252, 0xd1bb67f1, 0xa6bc5767, 0x3fb506dd, 0x48b2364b,
  0xd80d2bda, 0xaf0a1b4c, 0x36034af6, 0x41047a60, 0xdf60efc3, 0xa867df55,
  0x316e8eef, 0x4669be79, 0xcb61b38c, 0xbc66831a, 0x256fd2a0, 0x5268e236,
  0xcc0c7795, 0xbb0b4703, 0x220216b9, 0x5505262f, 0xc5ba3bbe, 0xb2bd0b28,
  0x2bb45a92, 0x5cb36a04, 0xc2d7ffa7, 0xb5d0cf31, 0x2cd99e8b, 0x5bdeae1d,
  0x9b64c2b0, 0xec63f226, 0x756aa39c, 0x026d930a, 0x9c0906a9, 0xeb0e363f,
  0x72076785, 0x05005713, 0x95bf4a82, 0xe2b87a14, 0x7bb12bae, 0x0cb61b38,
  0x92d28e9b, 0xe5d5be0d, 0x7cdcefb7, 0x0bdbdf21, 0x86d3d2d4, 0xf1d4e242,
  0x68ddb3f8, 0x1fda836e, 0x81be16cd, 0xf6b9265b, 0x6fb077e1, 0x18b74777,
  0x88085ae6, 0xff0f6a70, 0x66063bca, 0x11010b5c, 0x8f659eff, 0xf862ae69,
  0x616bffd3, 0x166ccf45, 0xa00ae278, 0xd70dd2ee, 0x4e048354, 0x3903b3c2,
  0xa7672661, 0xd06016f7, 0x4969474d, 0x3e6e77db, 0xaed16a4a, 0xd9d65adc,
  0x40df0b66, 0x37d83bf0, 0xa9bcae53, 0xdebb9ec5, 0x47b2cf7f, 0x30b5ffe9,
  0xbdbdf21c, 0xcabac28a, 0x53b39330, 0x24b4a3a6, 0xbad03605, 0xcdd70693,
  0x54de5729, 0x23d967bf, 0xb3667a2e, 0xc4614ab8, 0x5d681b02, 0x2a6f2b94,
  0xb40bbe37, 0xc30c8ea1, 0x5a05df1b, 0x2d02ef8d
};



uint32_t
crc32 (const void *buf, size_t size)
{
  const uint8_t *p = buf;
  uint32_t crc;

  crc = ~0U;
  while (size--)
    crc = crc32_tab[(crc ^ *p++) & 0xFF] ^ (crc >> 8);
  return crc ^ ~0U;
}



void
str_truncate (char *str)
{

  int i;
  for (i = 0; i < strnlen(str,MAX_KEYSTR-1); i++)
    if ( (str[i] == 0x20) ||  (str[i] == 0x0a) ) { 
      str[i] = 0x0;
 	 return;
     }

return;


}


int
main (int argc, char **argv)
{
  char *valback, *mfile, *filename, *key, *value, keystr[MAX_KEYSTR],
    result[MAX_KEYSTR],newdata[MAX_KEYSTR];
  const char *conststr = "301:";
  struct stat fst, stval, fh;
  struct select_t seleccion;
  int strsize = 0;
  int i, aflag, sflag, iflag, hflag, rflag, dflag, vflag, fflag, kflag, Iflag,
    errorf;
  sflag = aflag = iflag = hflag = rflag = dflag = vflag = kflag = fflag =
    Iflag = 0;
  errorf = 0;
  /*
     printf ("Dumping\n");
     dump_bht ((uint8_t *) argv[1]);
     printf ("Dumped\n");
   */
  if (argv[1] == NULL)
    {
      help ((uint8_t *) argv[0]);
      exit (EXIT_FAILURE);
    }
  if (argv[1][0] != '-')
    {
      fprintf (stderr, "Options in argv[1] must be -h,-s o -i\n");
      help ((uint8_t *) argv[0]);
      exit (EXIT_FAILURE);
    }
  switch (argv[1][1])
    {
    case 's':
      sflag = 1;
      break;
    case 'i':
      iflag = 1;
      break;
    case 'r':
      rflag = 1;
      break;
    case 'a':
      aflag = 1;
      break;
    case 'h':
      hflag = 1;
      break;
    case 'I':
      Iflag = 1;
      break;
    default:
      fprintf (stderr, "Option -%c does not exists\n", argv[1][1]);
      help ((uint8_t *) argv[0]);
      exit (EXIT_FAILURE);
      break;			/* costumbre */
    };

  if (Iflag)
    {
      if ((argv[2] == NULL) || (strcmp (argv[2], "-d") != 0))
	{
	  fprintf (stderr,
		   "Need to specify a database with an argument -d database\n");
	  exit (EXIT_FAILURE);
	}
      else
	{
	  if (stat (argv[3], &fh) != 0)
	    {
	      fprintf (stderr, "No existe el archivo db \'%s\'\n", argv[3]);
	      exit (EXIT_FAILURE);
	    }

	}
      filename = argv[3];

      if (argv[4] != NULL)
	{
	  if (strcmp (argv[4], "-F") != 0)
	    {
	      printf
		("Only argument -F is allowed in interactive mode for FAST io\n");
	      exit (EXIT_FAILURE);
	    }
	  else
	    fastio = 1;
	}

      memset (&keystr, 0, sizeof (keystr));
/*
      while ( (strsize = read (0, &keystr, sizeof (keystr))) != EOF)
*/
        if (setvbuf(stdout, NULL, _IOLBF, 0) != 0) {
                fprintf(stderr, "No pude configurar stdout buffer\n");
                exit(EXIT_FAILURE);
        }
/*
 *
 * SOLO PARA LF.TELMEX.COM obligamos a fastio = 1
 *
 *
 */
fastio=1;
      while ( fgets((char *)&keystr,sizeof(keystr),stdin) != NULL)
	{
/*
	  strsize = read (0, &keystr, sizeof (keystr));
*/
	  str_truncate ((char *) &keystr);
	  seleccion = select_bht ((uint8_t *) filename, (uint8_t *) & keystr);
	  if (seleccion.datasiz < 1)
	    fprintf (stdout,"%s\n", keystr);
	  else
	    {
	      memset (&result, 0, sizeof (result));
	      memset(&newdata,0,sizeof(newdata));
	      memcpy(newdata,seleccion.data,seleccion.datasiz);
	      fprintf (stdout,"301:%s\n", newdata);
	      memset (&keystr, 0, sizeof (keystr));
	      /*
	         write (1, conststr, strlen (conststr));
	         write (1, seleccion.data, seleccion.datasiz);
	         printf ("\n");
	       */
	    }

/*
	  if (!fastio)
	    close_bht (seleccion.db);
*/

	}
    }


  if (hflag == 1)
    help ((uint8_t *) argv[0]);
  if (aflag == 1)
    {
      if (argv[2] == NULL)
	{
	  fprintf (stderr,
		   "Need to specify a database with an argument -d database\n");
	  exit (EXIT_FAILURE);
	}
      if (strcmp (argv[2], "-d") != 0)
	{
	  fprintf (stderr,
		   "For dumping database need to specify a database with -d\n");
	  exit (EXIT_FAILURE);
	}
      if (argv[3] != NULL)
	dump_bht ((uint8_t *) argv[3]);
      else
	{
	  fprintf (stderr, "Need to specify a database file with -d\n");
	  exit (EXIT_FAILURE);
	}
      return 0;
    }

  if (iflag == 1)
    {
      for (i = 2; i < argc; i++)
	{
	  if (argv[i] == NULL)
	    {
	      fprintf (stderr,
		       "Option -i requires more flags ,for example\n$ %s -i -k key -v value -d mydb.db\n",
		       argv[0]);
	      exit (EXIT_FAILURE);
	    }
	  if (argv[i][0] == '-')
	    switch (tolower (argv[i][1]))
	      {
	      case 'k':
		if (argv[i + 1] == NULL)
		  {
		    fprintf (stderr,
			     "Option -k requires an argument (hash key)\n");
		    errorf = 1;
		  }
		key = argv[i + 1];
		kflag = 1;
		break;
	      case 'f':
		continue;
	      case 'v':
		if (argv[i + 1] == NULL)
		  {
		    fprintf (stderr,
			     "Option -v requires an argument (value of key)\n");
		    errorf = 1;
		  }
		if (((argv[i + 1][0] == '-') && (argv[i + 1][1] == 'f'))
		    && (argv[i + 2] != NULL))
		  {
		    fflag = 1;
		    mfile = argv[i + 2];
		  }
		else
		  value = argv[i + 1];
		vflag = 1;
		break;
	      case 'd':
		if (argv[i + 1] == NULL)
		  {
		    fprintf (stderr,
			     "Option -d requires an argument (database file)\n");
		    errorf = 1;
		  }
		filename = argv[i + 1];
		dflag = 1;
		break;
	      default:
		fprintf (stderr, "Option -%c does not exists\n", argv[i][1]);
		errorf = 1;
		break;
	      };
	}
      if (kflag == 0)
	{
	  fprintf (stderr, "Need to give me a hash key with -k\n");
	  errorf = 1;
	}
      if (dflag == 0)
	{
	  fprintf (stderr,
		   "Need to give me a file to be a database with -d\n");
	  errorf = 1;
	}
      if (vflag == 0)
	{
	  fprintf (stderr, "Need to give me a value key with -v\n");
	  errorf = 1;
	}
      if (errorf == 1)
	exit (EXIT_FAILURE);
      if (stat (filename, &fst) != 0)
	mkbht ((int8_t *) filename);
      if (fflag == 1)
	{
	  value = (char *) mapfile ((uint8_t *) mfile);
	  valback = value;
	  if (stat (mfile, &stval) != 0)
	    {
	      fprintf (stderr, "Strange error file now does not exists\n");
	      exit (EXIT_FAILURE);
	    }
	}
      else
	stval.st_size = strlen (value);



      insert_bht ((uint8_t *) filename, (uint8_t *) key, (uint8_t *) value,
		  stval.st_size);
      if (fflag == 1)
	unmapfile (valback, stval.st_size);
      return 0;
    }
  if (rflag == 1)
    {
      fprintf (stderr, "Removing..\n");
      for (i = 2; i < argc; i++)
	{
	  if (argv[i] == NULL)
	    {
	      fprintf (stderr,
		       "Option -r requieres more flags , for example\n$ %s -r -k key -d mydb.db\n",
		       argv[0]);
	      exit (EXIT_FAILURE);
	    }
	  if (argv[i][0] == '-')
	    switch (tolower (argv[i][1]))
	      {
	      case 'k':
		if (argv[i + 1] == NULL)
		  {
		    fprintf (stderr,
			     "Option -k requires an argument (hash key)\n");
		    errorf = 1;
		  }
		key = argv[i + 1];
		kflag = 1;
		break;
	      case 'd':
		if (argv[i + 1] == NULL)
		  {
		    fprintf (stderr,
			     "Option -d requires an argument (database file)\n");
		    errorf = 1;
		  }
		filename = argv[i + 1];
		dflag = 1;
		break;
	      default:
		fprintf (stderr, "Option -%c does not exists\n", argv[i][1]);
		errorf = 1;
		break;
	      };

	}
      if (kflag == 0)
	{
	  fprintf (stderr, "Need to give me a hash key with option -k\n");
	  errorf = 1;
	}
      if (dflag == 0)
	{
	  fprintf (stderr,
		   "Need to give me a file to be a database with option -d\n");
	  errorf = 1;
	}
      if (errorf == 1)
	exit (EXIT_FAILURE);
      if (stat (filename, &fst) != 0)
	{
	  mkbht ((int8_t *) filename);
	  fprintf (stderr,
		   "The file %s does not exists, i have created the database , for now i cant make search until you insert something\n",
		   filename);
	  exit (EXIT_FAILURE);
	}

      delete_bht ((uint8_t *) filename, (uint8_t *) key);
      return 0;
    }

  hflag = dflag = rflag = vflag = kflag = errorf = 0;
  if (sflag == 1)
    {
      for (i = 2; i < argc; i++)
	{
	  if (argv[i] == NULL)
	    {
	      fprintf (stderr,
		       "Option -s requires more flags ,for example\n$ %s -s -k key -d mydb.db\n",
		       argv[0]);
	      exit (EXIT_FAILURE);
	    }
	  if (argv[i][0] == '-')
	    switch (tolower (argv[i][1]))
	      {
	      case 'k':
		if (argv[i + 1] == NULL)
		  {
		    fprintf (stderr,
			     "Option -k requires an argument (hash key)\n");
		    errorf = 1;
		  }
		key = argv[i + 1];
		kflag = 1;
		break;
	      case 'd':
		if (argv[i + 1] == NULL)
		  {
		    fprintf (stderr,
			     "Option -d requires an argument (database file)\n");
		    errorf = 1;
		  }
		filename = argv[i + 1];
		dflag = 1;
		break;
	      default:
		fprintf (stderr, "Option -%c does not exists\n", argv[i][1]);
		errorf = 1;
		break;
	      };
	}

      if (kflag == 0)
	{
	  fprintf (stderr, "Need to give me a hash key with option -k\n");
	  errorf = 1;
	}
      if (dflag == 0)
	{
	  fprintf (stderr,
		   "Need to give me a file to be a database with option -d\n");
	  errorf = 1;
	}
      if (errorf == 1)
	exit (EXIT_FAILURE);
      if (stat (filename, &fst) != 0)
	{
	  mkbht ((int8_t *) filename);
	  fprintf (stderr,
		   "The file %s does not exists, i have created the database , for now i cant make search until you insert something\n",
		   filename);
	  exit (EXIT_FAILURE);
	}
      seleccion = select_bht ((uint8_t *) filename, (uint8_t *) key);
      fprintf (stderr, "[%s] -> ", key);
      write (1, seleccion.data, seleccion.datasiz);
      printf ("\n");
      close_bht (seleccion.db);
      return 0;
    }
  return 1;
}
