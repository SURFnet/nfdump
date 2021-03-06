// vi: noexpandtab tabstop=4 shiftwidth=4:
/**
 * \file
 * Functions for reading and writing nfdump files
 *
 * \copyright
 *  Copyright (c) 2017, Peter Haag
 *  Copyright (c) 2014, Peter Haag
 *  Copyright (c) 2011, Peter Haag
 *  Copyright (c) 2004-2008, SWITCH - Teleinformatikdienste fuer Lehre und Forschung
 *  All rights reserved.
 * 
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions are met:
 * 
 *   * Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright notice,
 *     this list of conditions and the following disclaimer in the documentation
 *     and/or other materials provided with the distribution.
 *   * Neither the name of the author nor the names of its contributors may be
 *     used to endorse or promote products derived from this software without
 *     specific prior written permission.
 * 
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 *  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 *  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 *  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 *  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 *  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 *  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 *  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 *  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 *  ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 *  POSSIBILITY OF SUCH DAMAGE.
 * 
 */

#include "config.h"

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/uio.h>
#include <time.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/param.h>
#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <stdlib.h>
#include <assert.h>
#ifdef HAVE_LIBBZ2
#include <bzlib.h>
#endif

#ifdef HAVE_STDINT_H
#include <stdint.h>
#endif

#include "minilzo.h"
#include "lz4.h"
#ifdef HAVE_LIBLZMA
#include <lzma.h>
#endif
#include "nf_common.h"
#include "nffile.h"
#include "flist.h"
#include "util.h"

/* global vars */

// required for idet filter in nftree.c
char 	*CurrentIdent;


#define READ_FILE	1
#define WRITE_FILE	1

// Compression buffer sizes
#define LZO_BUFFSIZE(size)  (((size) + (size) / 16 + 64 + 3) + sizeof(data_block_header_t))
#define BZ2_BUFFSIZE(size)  ((101 * (size)) / 100 + 600 + sizeof(data_block_header_t))
#define LZ4_BUFFSIZE(size)  (LZ4_compressBound(size) + sizeof (data_block_header_t))
#ifdef HAVE_LIBLZMA
#define LZMA_BUFFSIZE(size) (lzma_stream_buffer_bound(size) + sizeof (data_block_header_t))
#else
#define LZMA_BUFFSIZE(size) ((size) + sizeof (data_block_header_t))
#endif

static int lzo_initialized = 0;
static int lz4_initialized = 0;
static int bz2_initialized = 0;
static int lzma_initialized = 0;
#ifdef HAVE_LIBLZMA
static int lzma_preset = 6;
#endif

static int LZO_initialize(void);
static int LZ4_initialize(void);
static int BZ2_initialize(void);
static int LZMA_initialize(void);


static int OpenRaw(char *filename, stat_record_t *stat_record, int *compressed);

extern char *nf_error;

/* function prototypes */
static nffile_t *NewFile(void);

/* function definitions */

void SumStatRecords(stat_record_t *s1, stat_record_t *s2) {

	s1->numflows			+= s2->numflows;
	s1->numbytes			+= s2->numbytes;
	s1->numpackets			+= s2->numpackets;
	s1->numflows_tcp		+= s2->numflows_tcp;
	s1->numflows_udp		+= s2->numflows_udp;
	s1->numflows_icmp		+= s2->numflows_icmp;
	s1->numflows_other		+= s2->numflows_other;
	s1->numbytes_tcp		+= s2->numbytes_tcp;
	s1->numbytes_udp		+= s2->numbytes_udp;
	s1->numbytes_icmp		+= s2->numbytes_icmp;
	s1->numbytes_other		+= s2->numbytes_other;
	s1->numpackets_tcp		+= s2->numpackets_tcp;
	s1->numpackets_udp		+= s2->numpackets_udp;
	s1->numpackets_icmp		+= s2->numpackets_icmp;
	s1->numpackets_other	+= s2->numpackets_other;
	s1->sequence_failure	+= s2->sequence_failure;

	if ( s2->first_seen < s1->first_seen ) {
		s1->first_seen = s2->first_seen;
		s1->msec_first = s2->msec_first;
	}
	if ( s2->first_seen == s1->first_seen && 
		 s2->msec_first < s1->msec_first ) 
			s1->msec_first = s2->msec_first;

	if ( s2->last_seen > s1->last_seen ) {
		s1->last_seen = s2->last_seen;
		s1->msec_last = s2->msec_last;
	}
	if ( s2->last_seen == s1->last_seen && 
		 s2->msec_last > s1->msec_last ) 
			s1->msec_last = s2->msec_last;

} // End of SumStatRecords


static int LZO_initialize(void) {

	if (lzo_init() != LZO_E_OK) {
		// this usually indicates a compiler bug - try recompiling 
		// without optimizations, and enable `-DLZO_DEBUG' for diagnostics
		LogError("Compression lzo_init() failed.\n");
		return 0;
	} 
	lzo_initialized = 1;

	return 1;

} // End of LZO_initialize

static int LZ4_initialize (void) {

	int lz4_buff_size = LZ4_compressBound(BUFFSIZE + sizeof (data_block_header_t));
	if ( lz4_buff_size > (2 * BUFFSIZE) ) {
		LogError ("LZ4_compressBound() error in %s line %d: Buffer too small\n", __FILE__, __LINE__);
		return 0;
	}
	lz4_initialized = 1;

	return 1;

} // End of LZ4_initialize

static int BZ2_initialize (void) {
#ifdef HAVE_LIBBZ2
	bz2_initialized = 1;
	return 1;
#else
	LogError("BZ2 compression support not compiled in.\n");
	return 0;
#endif
} // End of BZ2_initialize


static int LZMA_initialize(void) {
#ifdef HAVE_LIBLZMA
	lzma_initialized = 1;
	return 1;
#else
	LogError("LZMA compression support not compiled in.\n");
	return 0;
#endif
}


#ifdef HAVE_LIBBZ2
static void BZ2_prep_stream (bz_stream*);
static void BZ2_prep_stream (bz_stream* bs)
{
   bs->bzalloc = NULL;
   bs->bzfree = NULL;
   bs->opaque = NULL;
} // End of BZ2_prep_stream
#endif


nffile_t *OpenFile(char *filename, nffile_t *nffile){
struct stat stat_buf;
int ret, allocated;

	if ( !nffile ) {
		nffile = NewFile();
		if ( nffile == NULL ) {
			return NULL;
		}
		allocated = 1;
	} else 
		allocated = 0;


	if ( filename == NULL ) {
		// stdin
		// Zero Stat
		nffile->fd = STDIN_FILENO;
	} else {
		// regular file
		if ( stat(filename, &stat_buf) ) {
			LogError("Can't stat '%s': %s\n", filename, strerror(errno));
			if ( allocated ) {
				DisposeFile(nffile);
				return NULL;
			}
		}

		if (!S_ISREG(stat_buf.st_mode) ) {
			LogError("'%s' is not a file\n", filename);
			if ( allocated ) {
				DisposeFile(nffile);
				return NULL;
			}
		}

		// printf("Statfile %s\n",filename);
		nffile->fd = open(filename, O_RDONLY);
		if ( nffile->fd < 0 ) {
			LogError("Error open file: %s\n", strerror(errno));
			if ( allocated ) {
				DisposeFile(nffile);
				return NULL;
			}
		}

	}

	ret = read(nffile->fd, (void *)nffile->file_header, sizeof(file_header_t));
	if ( nffile->file_header->magic != MAGIC ) {
		LogError("Open file '%s': bad magic: 0x%X\n", filename ? filename : "<stdin>", nffile->file_header->magic );
		CloseFile(nffile);
		if ( allocated ) {
			DisposeFile(nffile);
			return NULL;
		}
	}

	if ( nffile->file_header->version != LAYOUT_VERSION_1 ) {
		LogError("Open file %s: bad version: %u\n", filename, nffile->file_header->version );
		CloseFile(nffile);
		if ( allocated ) {
			DisposeFile(nffile);
			return NULL;
		}
	}

	ret = read(nffile->fd, (void *)nffile->stat_record, sizeof(stat_record_t));
	if ( ret < 0 ) {
		LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		CloseFile(nffile);
		if ( allocated ) {
			DisposeFile(nffile);
			return NULL;
		}
	}

	CurrentIdent		= nffile->file_header->ident;

	int compression = FILE_COMPRESSION(nffile);
	switch (compression) {
		case NOT_COMPRESSED:
			break;
		case LZO_COMPRESSED: 
			if ( !lzo_initialized && !LZO_initialize() && allocated ) {
				DisposeFile(nffile);
				return NULL;
			}
			break;
		case LZ4_COMPRESSED: 
			if ( !lz4_initialized && !LZ4_initialize() && allocated ) {
				DisposeFile(nffile);
				return NULL;
			}
			break;
		case BZ2_COMPRESSED: 
			if ( !bz2_initialized && !BZ2_initialize() && allocated ) {
				DisposeFile(nffile);
				return NULL;
			}
			break;
		case LZMA_COMPRESSED: 
			if ( !lzma_initialized && !LZMA_initialize() && allocated ) {
				DisposeFile(nffile);
				return NULL;
			}
			break;
	}

	return nffile;

} // End of OpenFile

void CloseFile(nffile_t *nffile){

	if ( !nffile ) 
		return;

	// do not close stdout
	if ( nffile->fd )
		close(nffile->fd);

} // End of CloseFile

int ChangeIdent(char *filename, char *Ident) {
file_header_t	FileHeader;
struct stat stat_buf;
int fd;

	if ( filename == NULL ) 
		return 0;

	if ( stat(filename, &stat_buf) ) {
		LogError("Can't stat '%s': %s\n", filename, strerror(errno));
		return -1;
	}

	if (!S_ISREG(stat_buf.st_mode) ) {
		LogError("'%s' is not a file\n", filename);
		return -1;
	}

	fd =  open(filename, O_RDWR);
	if ( fd < 0 ) {
		LogError("Error open file: %s\n", strerror(errno));
		return fd;
	}

	if ( read(fd, (void *)&FileHeader, sizeof(FileHeader)) < 0 ) {
		LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd);
		return -1;
	}
	if ( FileHeader.magic != MAGIC ) {
		LogError("Open file '%s': bad magic: 0x%X\n", filename, FileHeader.magic );
		close(fd);
		return -1;
	}
	if ( FileHeader.version != LAYOUT_VERSION_1 ) {
		LogError("Open file %s: bad version: %u\n", filename, FileHeader.version );
		close(fd);
		return -1;
	}

	strncpy(FileHeader.ident, Ident, IDENTLEN);
	FileHeader.ident[IDENTLEN - 1] = 0;

	if ( lseek(fd, 0, SEEK_SET) < 0 ) {
		LogError("lseek() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd);
		return -1;
	}

	if ( write(fd, (void *)&FileHeader, sizeof(file_header_t)) <= 0 ) {
		LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
	}

	if ( close(fd) < 0 ) {
		LogError("close() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return -1;
	}
	
	return 0;

} // End of ChangeIdent


void PrintStat(stat_record_t *s) {

	if ( s == NULL )
		return;

	// format info: make compiler happy with conversion to (unsigned long long), 
	// which does not change the size of the parameter
	printf("Ident: %s\n", CurrentIdent);
	printf("Flows: %llu\n", (unsigned long long)s->numflows);
	printf("Flows_tcp: %llu\n", (unsigned long long)s->numflows_tcp);
	printf("Flows_udp: %llu\n", (unsigned long long)s->numflows_udp);
	printf("Flows_icmp: %llu\n", (unsigned long long)s->numflows_icmp);
	printf("Flows_other: %llu\n", (unsigned long long)s->numflows_other);
	printf("Packets: %llu\n", (unsigned long long)s->numpackets);
	printf("Packets_tcp: %llu\n", (unsigned long long)s->numpackets_tcp);
	printf("Packets_udp: %llu\n", (unsigned long long)s->numpackets_udp);
	printf("Packets_icmp: %llu\n", (unsigned long long)s->numpackets_icmp);
	printf("Packets_other: %llu\n", (unsigned long long)s->numpackets_other);
	printf("Bytes: %llu\n", (unsigned long long)s->numbytes);
	printf("Bytes_tcp: %llu\n", (unsigned long long)s->numbytes_tcp);
	printf("Bytes_udp: %llu\n", (unsigned long long)s->numbytes_udp);
	printf("Bytes_icmp: %llu\n", (unsigned long long)s->numbytes_icmp);
	printf("Bytes_other: %llu\n", (unsigned long long)s->numbytes_other);
	printf("First: %u\n", s->first_seen);
	printf("Last: %u\n", s->last_seen);
	printf("msec_first: %u\n", s->msec_first);
	printf("msec_last: %u\n", s->msec_last);
	printf("Sequence failures: %u\n", s->sequence_failure);
} // End of PrintStat

static nffile_t *NewFile(void) {
nffile_t *nffile;

	// Create struct
	nffile = calloc(1, sizeof(nffile_t));
	if ( !nffile ) {
		LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return NULL;
	}
	nffile->buff_ptr = NULL;
	nffile->fd	 	= 0;

	// Init file header
	nffile->file_header = calloc(1, sizeof(file_header_t));
	if ( !nffile->file_header ) {
		LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return NULL;
	}
	nffile->file_header->magic 	   = MAGIC;
	nffile->file_header->version   = LAYOUT_VERSION_1;
	nffile->file_header->flags 	   = 0;
	nffile->file_header->NumBlocks = 0;

	nffile->stat_record = calloc(1, sizeof(stat_record_t));
	if ( !nffile->stat_record ) {
		LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return NULL;
	}

/*
	XXX catalogs not yet implemented
	nffile->catalog = calloc(1, sizeof(catalog_t));
	if ( !nffile->catalog ) {
		LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return NULL;
	}
	nffile->catalog->NumRecords = 0;
	nffile->catalog->size 		= sizeof(catalog_t) - sizeof(data_block_header_t);
	nffile->catalog->id 		= CATALOG_BLOCK;
	nffile->catalog->pad 		= 0;
	nffile->catalog->reserved 	= 0;
*/
	// init data buffer
	nffile->block_header = malloc(BUFFSIZE + sizeof(data_block_header_t));
	if ( !nffile->block_header ) {
		LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return NULL;
	}
	nffile->block_header->size 		 = 0;
	nffile->block_header->NumRecords = 0;
	nffile->block_header->id		 = DATA_BLOCK_TYPE_2;
	nffile->block_header->flags		 = 0;

	nffile->buff_ptr = (void *)((pointer_addr_t)nffile->block_header + sizeof(data_block_header_t));
	
	return nffile;

} // End of NewFile

nffile_t *DisposeFile(nffile_t *nffile) {
	free(nffile->file_header);
	free(nffile->stat_record);
	if (nffile->block_header) 
		free(nffile->block_header);
	free(nffile);
	return NULL;
} // End of DisposeFile

nffile_t *OpenNewFile(char *filename, nffile_t *nffile, int compress, int anonymized, char *ident) {
size_t			len;
int 			fd, flags;

	switch (compress) {
		case NOT_COMPRESSED:
			flags = FLAG_NOT_COMPRESSED;
			break;
		case LZO_COMPRESSED:
			flags = FLAG_LZO_COMPRESSED;
			if ( !lzo_initialized && !LZO_initialize() ) {
				LogError("Failed to initialize LZO compression");
				return NULL;
			}
			break;
		case LZ4_COMPRESSED:
			flags = FLAG_LZ4_COMPRESSED;
			if ( !lz4_initialized && !LZ4_initialize() ) {
				LogError("Failed to initialize LZ4 compression");
				return NULL;
			}
			break;
		case BZ2_COMPRESSED:
			flags = FLAG_BZ2_COMPRESSED;
			if ( !bz2_initialized && !BZ2_initialize() ) {
				LogError("Failed to initialize BZ2 compression");
				return NULL;
			}
			break;
		case LZMA_COMPRESSED:
			flags = FLAG_LZMA_COMPRESSED;
			if ( !lzma_initialized && !LZMA_initialize() ) {
				LogError("Failed to initialize LZMA compression");
				return NULL;
			}
			break;
		default:
			LogError("Unknown compression ID: %i\n", compress);
			return NULL;
	}

	fd = 0;
	if ( strcmp(filename, "-") == 0 ) { // output to stdout
		fd = STDOUT_FILENO;
	} else {
		fd = open(filename, O_CREAT | O_RDWR | O_TRUNC, S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH );
		if ( fd < 0 ) {
			LogError("Failed to open file %s: '%s'" , filename, strerror(errno));
			return NULL;
		}
	}

	// Allocate new struct if not given
	if ( nffile == NULL ) {
		nffile = NewFile();
		if ( nffile == NULL ) {
			return NULL;
		}
	}

	nffile->fd = fd;

	if ( anonymized ) 
		SetFlag(flags, FLAG_ANONYMIZED);

	nffile->file_header->flags 	   = flags;

/*
	XXX catalogs not yet implemented
	if ( nffile->catalog && nffile->catalog->NumRecords ) {
		memset((void *)nffile->catalog->entries, 0, nffile->catalog->NumRecords * sizeof(struct catalog_entry_s));
		nffile->catalog->NumRecords = 0;
		nffile->catalog->size		= 0;
	} 
*/
	if ( nffile->stat_record ) {
		memset((void *)nffile->stat_record, 0, sizeof(stat_record_t));
		nffile->stat_record->first_seen = 0x7fffffff;
		nffile->stat_record->msec_first = 999;
	}

	if ( ident ) {
		strncpy(nffile->file_header->ident, ident, IDENTLEN);
		nffile->file_header->ident[IDENTLEN - 1] = 0;
	} 

	nffile->file_header->NumBlocks = 0;
	len = sizeof(file_header_t);
	if ( write(nffile->fd, (void *)nffile->file_header, len) < len ) {
		LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(nffile->fd);
		nffile->fd = 0;
		return NULL;
	}

	// write empty stat record - ist updated when file gets closed
	len = sizeof(stat_record_t);
	if ( write(nffile->fd, (void *)nffile->stat_record, len) < len ) {
		LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(nffile->fd);
		nffile->fd = 0;
		return NULL;
	}

/* skip writing catalog in this test version
	XXX catalogs not yet implemented
	if ( WriteExtraBlock(nffile, (data_block_header_t *)nffile->catalog) < 0 ) {
		LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(nffile->fd);
		return NULL;
	}
*/

	return nffile;

} /* End of OpenNewFile */

nffile_t *AppendFile(char *filename) {
nffile_t		*nffile;

	// try to open the existing file
	nffile = OpenFile(filename, NULL);
	if ( !nffile )
		return NULL;

	// file is valid - re-open the file mode RDWR
	close(nffile->fd);
	nffile->fd = open(filename, O_RDWR | O_APPEND, S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH );
	if ( nffile->fd < 0 ) {
		LogError("Failed to open file %s: '%s'" , filename, strerror(errno));
		DisposeFile(nffile);
		return NULL;
	}

	// init output data buffer
	nffile->block_header = malloc(BUFFSIZE + sizeof(data_block_header_t));
	if ( !nffile->block_header ) {
		LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(nffile->fd);
		DisposeFile(nffile);
		return NULL;
	}
	nffile->block_header->size 		 = 0;
	nffile->block_header->NumRecords = 0;
	nffile->block_header->id		 = DATA_BLOCK_TYPE_2;
	nffile->block_header->flags		 = 0;
	nffile->buff_ptr = (void *)((pointer_addr_t)nffile->block_header + sizeof(data_block_header_t));

	int compression = FILE_COMPRESSION(nffile);
	switch (compression) {
		case NOT_COMPRESSED:
			break;
		case LZO_COMPRESSED: 
			if ( !lzo_initialized && !LZO_initialize() ) {
				LogError("Failed to initialize LZO compression");
				close(nffile->fd);
				DisposeFile(nffile);
				return NULL;
			}
			break;
		case LZ4_COMPRESSED: 
			if ( !lz4_initialized && !LZ4_initialize() ) {
				LogError("Failed to initialize LZ4 compression");
				close(nffile->fd);
				DisposeFile(nffile);
				return NULL;
			}
			break;
		case BZ2_COMPRESSED: 
			if ( !bz2_initialized && !BZ2_initialize() ) {
				LogError("Failed to initialize BZ2 compression");
				close(nffile->fd);
				DisposeFile(nffile);
				return NULL;
			}
			break;
	}

	return nffile;

} /* End of AppendFile */

int RenameAppend(char *from, char *to) {
int fd_to, fd_from, ret;
int compressed_to, compressed_from;
stat_record_t stat_record_to, stat_record_from;
data_block_header_t *block_header;
void *p;

	fd_to = OpenRaw(to, &stat_record_to, &compressed_to);
	if ( fd_to == 0 ) {
		// file does not exists, use rename
		return rename(from, to) == 0 ? 1 : 0;
	}

	fd_from = OpenRaw(from, &stat_record_from, &compressed_from);
	if ( fd_from <= 0 ) {
		// file does not exists - strange
		close(fd_to);
		return 0;
	}

	// both files open - append data
	ret = lseek(fd_to, 0, SEEK_END);
	if ( ret < 0 ) {
		LogError("lseek() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd_from);
		close(fd_to);
		return 0;
	}

	block_header = malloc(sizeof(data_block_header_t) + BUFFSIZE);
	if ( !block_header ) {
		LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno));
		close(fd_from);
		close(fd_to);
		return 0;
	}
	p = (void *)((void *)block_header + sizeof(data_block_header_t));

	while (1) {
		ret = read(fd_from, (void *)block_header, sizeof(data_block_header_t));
		if ( ret == 0 ) 
			// EOF
			break;

		if ( ret < 0 ) {
			// that's bad! difficult to recover. stat will be inconsistent
			LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
			break;
		}

		// read data block
		ret = read(fd_from, p, block_header->size);
		if ( ret != block_header->size ) {
			// that's bad! difficult to recover. stat will be inconsistent
			LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
			break;
		}
		// append data block
		ret = write(fd_to, block_header, sizeof(data_block_header_t) + block_header->size);
		if ( ret < 0 ) {
			// that's bad! difficult to recover. stat will be inconsistent
			LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
			break;
		}
	}

	SumStatRecords(&stat_record_to, &stat_record_from);
	// both files open - append data
	ret = lseek(fd_to, sizeof(file_header_t), SEEK_SET);
	if ( ret < 0 ) {
		LogError("lseek() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd_from);
		close(fd_to);
		return 0;
	}

	if ( write(fd_to, (void *)&stat_record_to, sizeof(stat_record_t)) <= 0 ) {
		LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd_from);
		close(fd_to);
		return 0;
	}

	close(fd_from);
	close(fd_to);
	unlink(from);
	return 1;

} // End of RenameAppend

static int OpenRaw(char *filename, stat_record_t *stat_record, int *compressed) {
struct stat stat_buf;
file_header_t file_header;
int fd, ret;

	if ( stat(filename, &stat_buf) ) {
		// file does not exists
		return 0;
	}

	// file exists - should be a regular file 
	if (!S_ISREG(stat_buf.st_mode) ) {
		// should nor really happen - catch it anyway
		LogError("'%s' is not a regular file\n", filename);
		return -1;
	}

	// file exists - append to existing
	fd = open(filename, O_RDWR, S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH );
	if ( fd < 0 ) {
		LogError("open() failed for file %s: '%s'" , filename, strerror(errno));
		return -1;
	}

	ret = read(fd, (void *)&file_header, sizeof(file_header_t));
	if ( ret < 0 ) {
		LogError("read() failed for file %s: '%s'" , filename, strerror(errno));
		close(fd);
		return -1;
	}

	if ( file_header.magic != MAGIC ) {
		LogError("Open file '%s': bad magic: 0x%X\n", filename, file_header.magic );
		close(fd);
		return -1;
	}

	if ( file_header.version != LAYOUT_VERSION_1 ) {
		LogError("Open file %s: bad version: %u\n", filename, file_header.version );
		close(fd);
		return -1;
	}

	ret = read(fd, (void *)stat_record, sizeof(stat_record_t));
	if ( ret < 0 ) {
		LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd);
		return -1;
	}

	if ( file_header.flags & FLAG_LZO_COMPRESSED ) 
		*compressed = FLAG_LZO_COMPRESSED;
	else if ( file_header.flags & FLAG_LZ4_COMPRESSED )
		*compressed = FLAG_LZ4_COMPRESSED;
	else if ( file_header.flags & FLAG_BZ2_COMPRESSED )
		*compressed = FLAG_BZ2_COMPRESSED;
	else
		*compressed = 0;

	return fd;

} // End of OpenRaw

int CloseUpdateFile(nffile_t *nffile, char *ident) {

	if ( nffile->block_header->size ) {
		int ret = WriteBlock(nffile);
		if ( ret < 0 ) {
			LogError("Failed to flush output buffer");
			return 0;
		}
	}

	if ( lseek(nffile->fd, 0, SEEK_SET) < 0 ) {
		// lseek on stdout works if output redirected:
		// e.g. -w - > outfile
		// but fails on pipe e.g. -w - | ./nfdump .... 
		if ( nffile->fd == STDOUT_FILENO ) {
			return 1;
		} else {
			LogError("lseek() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
			close(nffile->fd);
			return 0;
		}
	}

	if ( ident ) {
		strncpy(nffile->file_header->ident, ident, IDENTLEN);
	} else {
		if ( strlen(nffile->file_header->ident) == 0 ) 
		strncpy(nffile->file_header->ident, IDENTNONE, IDENTLEN);
	}

	if ( write(nffile->fd, (void *)nffile->file_header, sizeof(file_header_t)) <= 0 ) {
		LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
	}
	if ( write(nffile->fd, (void *)nffile->stat_record, sizeof(stat_record_t)) <= 0 ) {
		LogError("write() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
	}
	if ( close(nffile->fd) < 0 ) {
		LogError("close() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return 0;
	}

	nffile->file_header->NumBlocks = 0;
	
	return 1;

} /* End of CloseUpdateFile */


/**
 * Decompresses datablock that was compressed with LZO.
 * \see CompressLzo
 * \param in_block Pointer to block that is to be decompressed
 * \param out_block Address of pointer to block that will contain decompressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return Size of out_block on success, NF_ERROR otherwise
 */
ssize_t DecompressLzo(const data_block_header_t *in_block, data_block_header_t **out_block) {
int ret;
lzo_uint new_len = sizeof(data_block_header_t) + BUFFSIZE;
	// Allocate space for decompressed data
	*out_block = (data_block_header_t*)malloc(new_len);
	if (*out_block == NULL) {
		LogError("Failed to allocate LZO decompression buffer");
		return NF_ERROR;
	}
	// Copy block header
	**out_block = *in_block;

	// Point to start of block data
	lzo_bytep in_data = (lzo_bytep)in_block + sizeof(data_block_header_t);
	lzo_bytep out_data = (lzo_bytep)*out_block + sizeof(data_block_header_t);
	lzo_uint out_size = BUFFSIZE;

	ret = lzo1x_decompress(in_data, in_block->size, out_data, &out_size, NULL);
	if (ret != LZO_E_OK ) {
		free(*out_block);
		*out_block = NULL;
		LogError("Decompression failed. LZO error: %d\n", ret);
		return NF_CORRUPT;
	}
	(*out_block)->size = out_size;
	return out_size + sizeof(data_block_header_t);
}


/**
 * Decompresses datablock that was compressed with BZ2.
 * \see CompressBz2
 * \param in_block Pointer to block that is to be decompressed
 * \param out_block Address of pointer to block that will contain decompressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return Size of out_block on success, NF_ERROR otherwise
 */
ssize_t DecompressBz2(const data_block_header_t *in_block, data_block_header_t **out_block) {
#ifdef HAVE_LIBBZ2
bz_stream bs;
BZ2_prep_stream (&bs);
ssize_t new_len = sizeof(data_block_header_t) + BUFFSIZE;
	// Allocate space for decompressed data
	*out_block = (data_block_header_t*)malloc(new_len);
	if (*out_block == NULL) {
		LogError("Failed to allocate BZ2 decompression buffer");
		return NF_ERROR;
	}
	// Copy block header
	**out_block = *in_block;

	BZ2_bzDecompressInit (&bs, 0, 0);
	bs.next_in = (char*)in_block + sizeof(data_block_header_t);
	bs.avail_in = in_block->size;
	bs.next_out = (char*)*out_block + sizeof(data_block_header_t);
	bs.avail_out = BUFFSIZE;
	for (;;) {
		int ret = BZ2_bzDecompress (&bs);
		if (ret == BZ_OK) {
			continue;
		} else if (ret != BZ_STREAM_END) {
			free(*out_block);
		    *out_block = NULL;
			BZ2_bzDecompressEnd (&bs);
		    LogError("Decompression failed. BZ2 error: %d\n", ret);
			return NF_CORRUPT;
		} else {
			break;
		}
	}
	(*out_block)->size = bs.total_out_lo32;
	BZ2_bzDecompressEnd (&bs);
	return (*out_block)->size + sizeof(data_block_header_t);
#else
	LogError("BZ2 compression support not compiled in.\n");
	return NF_ERROR;
#endif
}

/**
 * Decompresses datablock that was compressed with LZ4.
 * \see CompressLz4
 * \param in_block Pointer to block that is to be decompressed
 * \param out_block Address of pointer to block that will contain decompressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return Size of out_block on success, NF_ERROR otherwise
 */
ssize_t DecompressLz4(const data_block_header_t *in_block, data_block_header_t **out_block) {
int ret;
size_t new_len = sizeof(data_block_header_t) + BUFFSIZE;
	// Allocate space for decompressed data
	*out_block = (data_block_header_t*)malloc(new_len);
	if (*out_block == NULL) {
		LogError("Failed to allocate LZ4 decompression buffer");
		return NF_ERROR;
	}
	// Copy block header
	**out_block = *in_block;

	// Point to start of block data
	char* in_data = (char*)in_block + sizeof(data_block_header_t);
	char* out_data = (char*)*out_block + sizeof(data_block_header_t);

	ret = LZ4_decompress_safe(in_data, out_data, in_block->size, BUFFSIZE);
	if (ret < 0 ) {
		free(*out_block);
		*out_block = NULL;
		LogError("Decompression failed. LZ4 error: %d\n", ret);
		return NF_CORRUPT;
	}
	(*out_block)->size = ret;
	return ret + sizeof(data_block_header_t);
}

/**
 * Decompresses datablock that was compressed with LZMA.
 * \see CompressLzma
 * \param in_block Pointer to block that is to be decompressed
 * \param out_block Address of pointer to block that will contain decompressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return Size of out_block on success, NF_ERROR otherwise
 */
ssize_t DecompressLzma(const data_block_header_t *in_block, data_block_header_t **out_block) {
#ifdef HAVE_LIBLZMA
int ret;
uint64_t mem_limit = 0x04000000;
size_t in_pos = 0, out_pos = 0;
size_t new_len = sizeof(data_block_header_t) + BUFFSIZE;

	// Allocate space for decompressed data
	*out_block = (data_block_header_t*)malloc(new_len);
	if (*out_block == NULL) {
		LogError("Failed to allocate LZ4 decompression buffer");
		return NF_ERROR;
	}
	// Copy block header
	**out_block = *in_block;

	// Point to start of block data
	unsigned char* in_data = (unsigned char*)in_block + sizeof(data_block_header_t);
	unsigned char* out_data = (unsigned char*)*out_block + sizeof(data_block_header_t);

	ret = lzma_stream_buffer_decode(
			&mem_limit,  // Max memory to be used
			0,           // Flags
			NULL,        // allocator. NULL means (malloc, free)
			in_data,
			&in_pos,
			in_block->size,
			out_data,
			&out_pos,
			BUFFSIZE);
	if (ret != LZMA_OK) {
		free(*out_block);
		*out_block = NULL;
		LogError("Decompression failed. LZMA error: %d\n", ret);
		return NF_CORRUPT;
	}
    (*out_block)->size = out_pos;
	return out_pos + sizeof(data_block_header_t);
#else
	LogError("LZMA support is not compiled in.\n");
	return NF_ERROR;
#endif
}

/**
 * Dummy decompression.
 * Just copies the input in order to match behavious of other decompression functions.
 * \param in_block Pointer to block that is to be copied
 * \param out_block Address of pointer to block that will contain copied data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return Size of out_block on success, NF_ERROR otherwise
 */
ssize_t DecompressNone(const data_block_header_t *in_block, data_block_header_t **out_block) {
size_t new_len = sizeof(data_block_header_t) + BUFFSIZE;
size_t out_len;

	// Allocate space for decompressed data
	*out_block = (data_block_header_t*)malloc(new_len);
	if (*out_block == NULL) {
		LogError("Failed to allocate decompression buffer");
		return NF_ERROR;
	}
	// Copy block header
	**out_block = *in_block;

	// Point to start of block data
	unsigned char* in_data = (unsigned char*)in_block + sizeof(data_block_header_t);
	unsigned char* out_data = (unsigned char*)*out_block + sizeof(data_block_header_t);
	out_len = in_block->size < BUFFSIZE ? in_block->size : BUFFSIZE;
	memcpy(out_data, in_data, out_len);
    (*out_block)->size = out_len;
	return out_len + sizeof(data_block_header_t);
}

/**
 * Reads one block of data from the file handle in nffile into
 * block. The block buffer in nffile will not be touched.
 * \param nffile File handle structure providing the file to read from.
 * \param block Address of pointer to block that will be allocated and
 *              will become the responsibilty of the caller when the
 *              function returns a value bigger than 0.
 * \return size of out_block, otherwise NF_EOF (0) when the end of the input
 *         file was reached or a negative value to indicate an error.
 */
ssize_t ReadBlockData(nffile_t *nffile, data_block_header_t **block) {
ssize_t ret, buff_size, request_size;
void 	*read_ptr; 
data_block_header_t *header, *buff;

    assert(*block == NULL);

    header = (data_block_header_t*)malloc(sizeof(data_block_header_t));

	if (header == NULL) {
		LogError("Failed to allocate memory for block header");
		return NF_ERROR;
	}

	ret = read(nffile->fd, header, sizeof(data_block_header_t));
	if ( ret == 0 ) {		// EOF
	    free(header);
		return NF_EOF;
	}
		
	if ( ret < 0 ) {	// ERROR
		free(header);
		return NF_ERROR;
	}
		
	// Check for sane buffer size
	if ( ret != sizeof(data_block_header_t) ) {
		// this is most likely a corrupt file
		free(header);
		LogError("Corrupt data file: Read %i bytes, requested %u\n", ret, sizeof(data_block_header_t));
		return NF_CORRUPT;
	}

	// Check for sane buffer size
	if ( header->size > BUFFSIZE ) {
		// this is most likely a corrupt file
		free(header);
		LogError("Corrupt data file: Requested buffer size %u exceeds max. buffer size.\n", header->size);
		return NF_CORRUPT;
	}

	buff_size = sizeof(data_block_header_t) + header->size;
	buff = (data_block_header_t*)realloc(header, buff_size);
	if (buff == NULL) {
		free(header);
		LogError("Buffer allocation error");
		return NF_ERROR;
	}

	request_size = buff->size;
	read_ptr = (void*)buff + sizeof(data_block_header_t);
	while (request_size > 0) {
		ret = read(nffile->fd, read_ptr, request_size);
	
		if ( ret == 0 ) {
			// EOF not expected here - this should never happen, file may be corrupt
			free(buff);
			LogError("Corrupt data file: Unexpected EOF while reading data block.\n");
			return NF_CORRUPT;
		}

		if ( ret == -1 ) {	// ERROR
			free(buff);
			LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
			return NF_ERROR;
		}
		request_size -= ret;
		read_ptr += ret;
	}

	*block = buff;
	return buff_size;
}


/**
 * Decompresses a block.
 * \param compression Integer indicating the type of compression
 * \param in_block Address of pointer to block that is to be decompressed.
 * \param out_block Address of pointer to block with decompressed data. This block
 *                  will be allocated and becomes the responsibility of the caller
 *                  when the function returns successfully.
 * \return size of out_block or NF_ERROR in case of failure
 */
ssize_t DecompressBlock(int compression, const data_block_header_t* in_block, data_block_header_t **out_block) {
int ret = 0;

    assert(in_block != NULL);
    assert(*out_block == NULL);

	switch (compression) {
		case NOT_COMPRESSED:
			ret = DecompressNone(in_block, out_block);
			break;
		case LZO_COMPRESSED:
			ret = DecompressLzo(in_block, out_block);
			break;
		case BZ2_COMPRESSED:
			ret = DecompressBz2(in_block, out_block);
			break;
		case LZ4_COMPRESSED:
			ret = DecompressLz4(in_block, out_block);
			break;
		case LZMA_COMPRESSED:
			ret = DecompressLzma(in_block, out_block);
			break;
		default:
			LogError("Unknown compression ID: %i\n", compression);
			return NF_ERROR;
	}
	if (ret < 0) {
		return NF_ERROR;
	}
	return ret;
}


int ReadBlock(nffile_t *nffile) {
int ret;
data_block_header_t *block = NULL;
data_block_header_t *decompressed_block = NULL;

	ret = (int)ReadBlockData(nffile, &block);
	
	if (ret <= NF_EOF) {
		return ret;
	}

	ret = (int)DecompressBlock(FILE_COMPRESSION(nffile), block, &decompressed_block);
    free(block);

	if (ret < 0) {
		free(decompressed_block);
		return ret;
	}

	memcpy(nffile->block_header, decompressed_block, ret);

	free(decompressed_block);

	return ret;
} // End of ReadBlock


/**
 * Compresses datablock with LZO 1x compression.
 * \param in_block Pointer to block that is to be compressed
 * \param out_block Address of pointer to block that will contain compressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return 0 on success, NF_ERROR otherwise
 */
int CompressLzo(const data_block_header_t *in_block, data_block_header_t **out_block) {
lzo_bytep in;
lzo_bytep out;
lzo_uint in_len;
lzo_uint out_len;
int ret;

	in_len = (lzo_uint)in_block->size;
	*out_block = (data_block_header_t *)malloc(LZO_BUFFSIZE(in_len));
	// Copy the header
	**out_block = *in_block;

	in = (lzo_bytep)((pointer_addr_t)in_block + sizeof(data_block_header_t));	
	out = (lzo_bytep)((pointer_addr_t)*out_block + sizeof(data_block_header_t));	

	lzo_voidp wrkmem = (lzo_voidp*)malloc(LZO1X_1_MEM_COMPRESS);

	ret = lzo1x_1_compress(in, in_len, out, &out_len, wrkmem);

	free(wrkmem);

	if (ret != LZO_E_OK) {
        free(*out_block);
        *out_block = NULL;
		LogError("LZO compression failed: %d" , ret);
		return NF_ERROR;
	}
    (*out_block)->size = out_len;
    return 0;
}

/**
 * Compresses datablock with BZ2 compression.
 * BZ2 compression compresses to about half the size of (the default) LZO compression,
 * but decompression is fairly slow.
 * \param in_block Pointer to block that is to be compressed
 * \param out_block Address of pointer to block that will contain compressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return 0 on success, NF_ERROR otherwise
 */
int CompressBz2(const data_block_header_t *in_block, data_block_header_t **out_block) {
#ifdef HAVE_LIBBZ2
lzo_uint in_len;
lzo_uint out_len;
int ret;

	in_len = in_block->size;
	out_len = BZ2_BUFFSIZE(in_len);
	*out_block = (data_block_header_t *)malloc(out_len);
	// Copy the header
	**out_block = *in_block;

	bz_stream bs;
	BZ2_prep_stream (&bs);
	BZ2_bzCompressInit (&bs, 9, 0, 0);

	bs.next_in = (char*) ( (pointer_addr_t)in_block  + sizeof (data_block_header_t));
	bs.next_out = (char*) ( (pointer_addr_t)*out_block + sizeof (data_block_header_t));
	bs.avail_in = in_len;
	bs.avail_out = out_len;

	for (;;) {
		ret = BZ2_bzCompress (&bs, BZ_FINISH);
		if (ret == BZ_FINISH_OK) continue;
		if (ret != BZ_STREAM_END) {
			free(*out_block);
			*out_block = NULL;
			LogError("BZ2 compression failed: %d" , ret);
			BZ2_bzCompressEnd (&bs);
			return NF_ERROR;
		}
		break;
	}

	(*out_block)->size = bs.total_out_lo32;
	BZ2_bzCompressEnd (&bs);
	return 0;
#else
	LogError("BZ2 compression support not compiled in.\n");
	return NF_ERROR;
#endif
}


/**
 * Compresses datablock with LZ4 compression.
 * LZ4 compression compresses about 5% worse than (the default) LZO compression,
 * but compression is upto 20% faster and decompression is around 40% faster.
 * \param in_block Pointer to block that is to be compressed
 * \param out_block Address of pointer to block that will contain compressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return 0 on success, NF_ERROR otherwise
 */
int CompressLz4(const data_block_header_t *in_block, data_block_header_t **out_block) {
char* in;
char* out;
size_t in_len;
int ret;

	in_len = (size_t)in_block->size;
	*out_block = (data_block_header_t *)malloc(LZ4_BUFFSIZE(in_len));
	// Copy the header
	**out_block = *in_block;

	in = (char*)((pointer_addr_t)in_block + sizeof(data_block_header_t));	
	out = (char*)((pointer_addr_t)*out_block + sizeof(data_block_header_t));	

	ret = LZ4_compress_default(in, out, in_len, BUFFSIZE);

	if (ret < 0) {
        free(*out_block);
        *out_block = NULL;
		LogError("LZ4 compression failed: %d" , ret);
		return NF_ERROR;
	}
    (*out_block)->size = ret;
    return 0;
}


/**
 * Compresses datablock with LZ4 compression.
 * LZMA compression compresses slightly better than BZ2, but has much faster
 * decompression at the expense of very slow compression
 * \param in_block Pointer to block that is to be compressed
 * \param out_block Address of pointer to block that will contain compressed data.
 *                  This pointer will be allocated and becomes the responsibility of
 *                  the caller in case the function returns successfuly.
 * \return 0 on success, NF_ERROR otherwise
 */
int CompressLzma(const data_block_header_t *in_block, data_block_header_t **out_block) {
#ifdef HAVE_LIBLZMA
unsigned char* in;
unsigned char* out;
size_t in_len;
size_t out_len;
size_t out_pos = sizeof(data_block_header_t);
int ret;

	in_len = (size_t)in_block->size;
	out_len = LZMA_BUFFSIZE(in_len);
	*out_block = (data_block_header_t *)malloc(out_len);
	// Copy the header
	**out_block = *in_block;

	in = (unsigned char*)((pointer_addr_t)in_block + sizeof(data_block_header_t));	
	out = (unsigned char*)*out_block;

	ret = lzma_easy_buffer_encode(
			lzma_preset,       // preset: high values are expensive and don't bring much
			LZMA_CHECK_CRC64,  // data corruption check
			NULL,              // allocator. NULL means (malloc, free)
			in,
			in_len,
			out,
			&out_pos,
			out_len);
    
	if (ret != LZMA_OK) {
        free(*out_block);
        *out_block = NULL;
		LogError("LZMA compression failed: %d" , ret);
		return NF_ERROR;
	}
    (*out_block)->size = out_pos;
	return 0;
#else
	LogError("LZMA compression support not compiled in.\n");
	return NF_ERROR;
#endif
}


int WriteBlock(nffile_t *nffile) {
data_block_header_t *out_block_header = NULL;
int ret = 0;

	// empty blocks need not to be stored 
	if ( nffile->block_header->size == 0 )
		return 1;

	switch (FILE_COMPRESSION(nffile)) {
		case LZO_COMPRESSED:
		    ret = CompressLzo(nffile->block_header, &out_block_header);
			break;
		case BZ2_COMPRESSED:
			ret = CompressBz2(nffile->block_header, &out_block_header);
			break;
		case LZ4_COMPRESSED:
			ret = CompressLz4(nffile->block_header, &out_block_header);
			break;
		case LZMA_COMPRESSED:
			ret = CompressLzma(nffile->block_header, &out_block_header);
			break;
		default:
			// not compressed
			out_block_header = nffile->block_header;
	}

	// Compression failure
	if (ret < 0) {
		return ret;
	}

	ret = write (nffile->fd, (void *) out_block_header, sizeof (data_block_header_t) + out_block_header->size);
	if (ret > 0) {
		nffile->block_header->size = 0;
		nffile->block_header->NumRecords = 0;
		nffile->file_header->NumBlocks++;
	}

	if (out_block_header != nffile->block_header) {
		free(out_block_header);
	}

	return ret;


} // End of WriteBlock

inline void ExpandRecord_v1(common_record_t *input_record, master_record_t *output_record ) {
uint32_t	*u;
size_t		size;
void		*p = (void *)input_record;

	// Copy common data block
	size = sizeof(common_record_t) - sizeof(uint8_t[4]);
	memcpy((void *)output_record, p, size);
	p = (void *)input_record->data;

	if ( (input_record->flags & FLAG_IPV6_ADDR) != 0 )	{ // IPv6
		// IPv6
		// keep compiler happy
		// memcpy((void *)output_record->v6.srcaddr, p, 4 * sizeof(uint64_t));	
		memcpy((void *)output_record->ip_union._ip_64.addr, p, 4 * sizeof(uint64_t));	
		p = (void *)((pointer_addr_t)p + 4 * sizeof(uint64_t));
	} else { 	
		// IPv4
		u = (uint32_t *)p;
		output_record->v6.srcaddr[0] = 0;
		output_record->v6.srcaddr[1] = 0;
		output_record->v4.srcaddr 	 = u[0];

		output_record->v6.dstaddr[0] = 0;
		output_record->v6.dstaddr[1] = 0;
		output_record->v4.dstaddr 	 = u[1];
		p = (void *)((pointer_addr_t)p + 2 * sizeof(uint32_t));
	}

	// packet counter
	if ( (input_record->flags & FLAG_PKG_64 ) != 0 ) { 
		// 64bit packet counter
		value64_t	l, *v = (value64_t *)p;
		l.val.val32[0] = v->val.val32[0];
		l.val.val32[1] = v->val.val32[1];
		output_record->dPkts = l.val.val64;
		p = (void *)((pointer_addr_t)p + sizeof(uint64_t));
	} else {	
		// 32bit packet counter
		output_record->dPkts = *((uint32_t *)p);
		p = (void *)((pointer_addr_t)p + sizeof(uint32_t));
	}

	// byte counter
	if ( (input_record->flags & FLAG_BYTES_64 ) != 0 ) { 
		// 64bit byte counter
		value64_t	l, *v = (value64_t *)p;
		l.val.val32[0] = v->val.val32[0];
		l.val.val32[1] = v->val.val32[1];
		output_record->dOctets = l.val.val64;
		p = (void *)((pointer_addr_t)p + sizeof(uint64_t));
	} else {	
		// 32bit bytes counter
		output_record->dOctets = *((uint32_t *)p);
		p = (void *)((pointer_addr_t)p + sizeof(uint32_t));
	}

} // End of ExpandRecord_v1

int ModifyCompressFile(char * rfile, char *Rfile, int compress) {
int 			i, anonymized, compression;
ssize_t			ret;
nffile_t		*nffile_r, *nffile_w;
stat_record_t	*_s;
char 			*filename, outfile[MAXPATHLEN];
void			*tmp;

	SetupInputFileSequence(NULL, rfile, Rfile);

	nffile_r = NULL;
	while (1) {
		nffile_r = GetNextFile(nffile_r, 0, 0);

		// last file
		if ( nffile_r == EMPTY_LIST )
			break;

		filename = GetCurrentFilename();

		if ( !nffile_r || !filename) {
			break;
		}
	
		compression = FILE_COMPRESSION(nffile_r);
		if ( compression == compress ) {
			printf("File %s is already same compression methode\n", filename);
			continue;
		}

		// tmp filename for new output file
		snprintf(outfile, MAXPATHLEN, "%s-tmp", filename);
		outfile[MAXPATHLEN-1] = '\0';

		anonymized = IP_ANONYMIZED(nffile_r);

		// allocate output file
		nffile_w = OpenNewFile(outfile, NULL, compress, anonymized, NULL);
		if ( !nffile_w ) {
			CloseFile(nffile_r);
			DisposeFile(nffile_r);
			return NF_ERROR;
		}

		// Use same buffer for read/write
		tmp = nffile_r->block_header;
		nffile_r->block_header =  nffile_w->block_header;
		nffile_r->buff_ptr 	   =  nffile_w->buff_ptr;
	
		// swap stat records :)
		_s = nffile_r->stat_record;
		nffile_r->stat_record = nffile_w->stat_record;
		nffile_w->stat_record = _s;
	
		for ( i=0; i < nffile_r->file_header->NumBlocks; i++ ) {
			ret = ReadBlock(nffile_r);
			if ( ret < 0 ) {
				ret = NF_ERROR;
				LogError("Error while reading data block. Abort.\n");
				nffile_r->block_header = tmp;
				CloseFile(nffile_r);
				DisposeFile(nffile_r);
				CloseFile(nffile_w);
				DisposeFile(nffile_w);
				unlink(outfile);
				return NF_ERROR;
			}
			if ( WriteBlock(nffile_w) <= 0 ) {
				ret = NF_ERROR;
				LogError("Failed to write output buffer to disk: '%s'" , strerror(errno));
				nffile_r->block_header = tmp;
				CloseFile(nffile_r);
				DisposeFile(nffile_r);
				CloseFile(nffile_w);
				DisposeFile(nffile_w);
				unlink(outfile);
				return NF_ERROR;
			}
		}

		printf("File %s compression changed\n", filename);
		if ( !CloseUpdateFile(nffile_w, nffile_r->file_header->ident) ) {
			unlink(outfile);
			LogError("Failed to close file: '%s'" , strerror(errno));
		} else {
			unlink(filename);
			rename(outfile, filename);
		}

		DisposeFile(nffile_w);
	}
	return 0;

} // End of ModifyCompressFile

void QueryFile(char *filename) {
int i;
nffile_t	*nffile;
uint32_t num_records, type1, type2, type3;
struct stat stat_buf;
ssize_t	ret;
off_t	fsize;

	if ( stat(filename, &stat_buf) ) {
		LogError("Can't stat '%s': %s\n", filename, strerror(errno));
		return;
	}

	nffile = OpenFile(filename, NULL);
	if ( !nffile ) {
		return;
	}

	num_records = 0;
	// set file size to current position ( file header )
	fsize = lseek(nffile->fd, 0, SEEK_CUR);
	type1 = 0;
	type2 = 0;
	type3 = 0;
	printf("File    : %s\n", filename);
	printf ("Version : %u - %s\n", nffile->file_header->version,
		FILE_IS_LZO_COMPRESSED (nffile) ? "lzo compressed" :
		FILE_IS_LZ4_COMPRESSED (nffile) ? "lz4 compressed" :
		FILE_IS_BZ2_COMPRESSED (nffile) ? "bz2 compressed" :
		    "not compressed");

	printf("Blocks  : %u\n", nffile->file_header->NumBlocks);
	for ( i=0; i < nffile->file_header->NumBlocks; i++ ) {
		if ( (fsize + sizeof(data_block_header_t)) > stat_buf.st_size ) {
			LogError("Unexpected read beyond EOF! File corrupted. Abort.\n");
			LogError("Expected %u blocks, counted %i\n", nffile->file_header->NumBlocks, i);
			break;
		}
		ret = read(nffile->fd, (void *)nffile->block_header, sizeof(data_block_header_t));
		if ( ret < 0 ) {
			LogError("Error reading block %i: %s\n", i, strerror(errno));
			break;
		}

		// Should never happen, as catched already in first check, but test it anyway ..
		if ( ret == 0 ) {
			LogError("Unexpected end of file reached. Expected %u blocks, counted %i\n", nffile->file_header->NumBlocks, i);
			break;
		}
		if ( ret < sizeof(data_block_header_t) ) {
			LogError("Short read: Expected %u bytes, read: %i\n", sizeof(data_block_header_t), ret);
			break;
		}
		fsize += sizeof(data_block_header_t);

		num_records += nffile->block_header->NumRecords;
		switch ( nffile->block_header->id) {
			case DATA_BLOCK_TYPE_1:
				type1++;
				break;
			case DATA_BLOCK_TYPE_2:
				type2++;
				break;
			case Large_BLOCK_Type:
				type3++;
				break;
			default:
				printf("block %i has unknown type %u\n", i, nffile->block_header->id);
		}

		if ( (fsize + nffile->block_header->size ) > stat_buf.st_size ) {
			LogError("Expected to seek beyond EOF! File corrupted. Abort.\n");
			break;
		}
		fsize += nffile->block_header->size;
		
		ret = lseek(nffile->fd, nffile->block_header->size, SEEK_CUR);
		if ( ret < 0 ) {
			LogError("Error seeking block %i: %s\n", i, strerror(errno));
			break;
		}
		if ( fsize != ret ) {
			LogError("Expected seek: Expected: %u, got: %u\n", fsize, ret);
			break;
		}
	}

	if ( fsize < stat_buf.st_size ) {
		LogError("Extra data detected after regular blocks: %i bytes\n", stat_buf.st_size-fsize);
	}

	printf(" Type 1 : %u\n", type1);
	printf(" Type 2 : %u\n", type2);
	printf(" Type 3 : %u\n", type3);
	printf("Records : %u\n", num_records);

	CloseFile(nffile);
	DisposeFile(nffile);

} // End of QueryFile

// simple interface to get a statrecord from a file without nffile overhead
stat_record_t *GetStatRecord(char *filename, stat_record_t *stat_record) {
file_header_t file_header;
int fd, ret;

	fd = open(filename, O_RDONLY);
	if ( fd < 0 ) {
		LogError("open() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return NULL;
	}

	ret = read(fd, (void *)&file_header, sizeof(file_header_t));
	if ( ret < 0 ) {
		LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd);
		return NULL;
	}

	if ( file_header.magic != MAGIC ) {
		LogError("Open file '%s': bad magic: 0x%X\n", filename ? filename : "<stdin>", file_header.magic );
		close(fd);
		return NULL;
	}

	if ( file_header.version != LAYOUT_VERSION_1 ) {
		LogError("Open file %s: bad version: %u\n", filename, file_header.version );
		close(fd);
		return NULL;
	}

	ret = read(fd, (void *)stat_record, sizeof(stat_record_t));
	if ( ret < 0 ) {
		LogError("read() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		close(fd);
		return NULL;
	}

	close(fd);
	return stat_record;

} // End of GetStatRecord



#ifdef COMPAT15
/*
 * v1 -> v2 record conversion:
 * A netflow record in v1 block format has the same size as in v2 block format.
 * Therefore, the conversion rearranges the v1 layout into v2 layout
 *
 * old record size = new record size = 36bytes + x, where x is the sum of
 * IP address block (IPv4 or IPv6) + packet counter + byte counter ( 4/8 bytes)
 *
 * v1											v2
 *
 *  0 uint32_t    flags;						uint16_t	type; 	
 *												uint16_t	size;
 *
 *  1 uint16_t    size;							uint8_t		flags;		
 * 												uint8_t 	exporter_sysid;
 *    uint16_t    exporter_ref; => 0			uint16_t	ext_map;
 *
 *  2 uint16_t    msec_first;					uint16_t	msec_first;
 *    uint16_t    msec_last;					uint16_t	msec_last;
 *
 *  3 uint32_t    first;						uint32_t	first;
 *  4 uint32_t    last;							uint32_t	last;
 *
 *  5 uint8_t     dir;							uint8_t		fwd_status;
 *    uint8_t     tcp_flags;					uint8_t		tcp_flags;
 *    uint8_t     prot;							uint8_t		prot;
 *    uint8_t     tos;							uint8_t		tos;
 *
 *  6 uint16_t    input;						uint16_t	srcport;
 *    uint16_t    output;						uint16_t	dstport;
 *
 *  7 uint16_t    srcport;						x bytes IP/pkts/bytes
 *    uint16_t    dstport;
 *
 *  8 uint16_t    srcas;
 *    uint16_t    dstas;
 *												uint16_t    input;
 *												uint16_t    output;
 *
 *												uint16_t    srcas;
 *	9 x bytes IP/pkts/byte						uint16_t    dstas;
 *
 *
 */

void Convert_v1_to_v2(void *mem) {
common_record_t    *v2 = (common_record_t *)mem;
common_record_v1_t *v1 = (common_record_v1_t *)mem;
uint32_t *index 	   = (uint32_t *)mem;
uint16_t tmp1, tmp2, srcas, dstas, *tmp3;
size_t cplen;

	// index 0
	tmp1 	 = v1->flags;
	v2->type = CommonRecordType;
	v2->size = v1->size;

	// index 1
	v2->flags 		   = tmp1;
	v2->exporter_sysid = 0;
	v2->ext_map 	   = 0;

	// index 2, 3, 4 already in sync

	// index 5
	v2->fwd_status = 0;

	// index 6
	tmp1 = v1->input;
	tmp2 = v1->output;
	v2->srcport = v1->srcport;
	v2->dstport = v1->dstport;

	// save AS numbers
	srcas = v1->srcas;
	dstas = v1->dstas;

	cplen = 0;
	switch (v2->flags) {
		case 0:
			// IPv4 8 byte + 2 x 4 byte counter
			cplen = 16;
			break;
		case 1:
			// IPv6 32 byte + 2 x 4 byte counter
			cplen = 40;
			break;
		case 2:
			// IPv4 8 byte + 1 x 4 + 1 x 8 byte counter
			cplen = 20;
			break;
		case 3:
			// IPv6 32 byte + 1 x 4 + 1 x 8 byte counter
			cplen = 44;
			break;
		case 4:
			// IPv4 8 byte + 1 x 8 + 1 x 4 byte counter
			cplen = 20;
			break;
		case 5:
			// IPv6 32 byte + 1 x 8 + 1 x 4 byte counter
			cplen = 44;
			break;
		case 6:
			// IPv4 8 byte + 2 x 8 byte counter
			cplen = 24;
			break;
		case 7:
			// IPv6 32 byte + 2 x 8 byte counter
			cplen = 48;
			break;
		default:
			// this should never happen - catch it anyway
			cplen = 0;
	}
	// copy IP/pkts/bytes block
	memcpy((void *)&index[7], (void *)&index[9], cplen );

	// hook 16 bit array at the end of copied block
	tmp3 = (uint16_t *)&index[7+(cplen>>2)];
	// 2 byte I/O interfaces 
	tmp3[0] = tmp1;
	tmp3[1] = tmp2;
	// AS numbers
	tmp3[2] = srcas;
	tmp3[3] = dstas;

} // End of Convert_v1_to_v2
#endif

