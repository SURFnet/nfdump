// vi: noexpandtab tabstop=4 shiftwidth=4:
/**
 * \file
 * Main program for the nfdump tool
 *
 * \copyright
 *  Copyright (c) 2017, Peter Haag
 *  Copyright (c) 2017, SURFnet
 *  Copyright (c) 2014, Peter Haag
 *  Copyright (c) 2009, Peter Haag
 *  Copyright (c) 2004-2008, SWITCH - Teleinformatikdienste fuer Lehre und Forschung
 *  All rights reserved.
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
 *  $Author: haag $
 *
 *  $Id: nfdump.c 69 2010-09-09 07:17:43Z haag $
 *
 *  $LastChangedRevision: 69 $
 *	
 *
 */

#include "config.h"

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdarg.h>
#include <errno.h>
#include <time.h>
#include <string.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/resource.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#ifdef HAVE_STDINT_H
#include <stdint.h>
#endif

#include "nffile.h"
#include "nfx.h"
#include "nfnet.h"
#include "bookkeeper.h"
#include "collector.h"
#include "exporter.h"
#include "nf_common.h"
#include "netflow_v5_v7.h"
#include "netflow_v9.h"
#include "rbtree.h"
#include "nftree.h"
#include "nfprof.h"
#include "nfdump.h"
#include "nflowcache.h"
#include "nfstat.h"
#include "nfexport.h"
#include "ipconv.h"
#include "util.h"
#include "flist.h"

#ifndef DEVEL
#   define dbg_printf(...) /* printf(__VA_ARGS__) */
#else
#   define dbg_printf(...) printf(__VA_ARGS__)
#endif

/* hash parameters */
#define NumPrealloc 128000

#define AGGR_SIZE 7

/* Global Variables */
FilterEngine_data_t	*Engine;

extern char	*FilterFilename;
extern uint32_t loopcnt;

#ifdef COMPAT15
extern extension_descriptor_t extension_descriptor[];
#endif

/* Local Variables */
const char *nfdump_version = VERSION;

static uint64_t total_bytes;
static uint32_t total_flows;
static uint32_t skipped_blocks;
static uint32_t	is_anonymized;
static time_t 	t_first_flow, t_last_flow;
static char		Ident[IDENTLEN];


int hash_hit = 0; 
int hash_miss = 0;
int hash_skip = 0;

extension_map_list_t *extension_map_list;

extern generic_exporter_t **exporter_list;
/*
 * Output Formats:
 * User defined output formats can be compiled into nfdump, for easy access
 * The format has the same syntax as describe in nfdump(1) -o fmt:<format>
 *
 * A format description consists of a single line containing arbitrary strings
 * and format specifier as described below:
 *
 * 	%ts		// Start Time - first seen
 * 	%te		// End Time	- last seen
 * 	%td		// Duration
 * 	%pr		// Protocol
 * 	%sa		// Source Address
 * 	%da		// Destination Address
 * 	%sap	// Source Address:Port
 * 	%dap	// Destination Address:Port
 * 	%sp		// Source Port
 * 	%dp		// Destination Port
 *  %nh		// Next-hop IP Address
 *  %nhb	// BGP Next-hop IP Address
 * 	%sas	// Source AS
 * 	%das	// Destination AS
 * 	%in		// Input Interface num
 * 	%out	// Output Interface num
 * 	%pkt	// Packets - default input
 * 	%ipkt	// Input Packets
 * 	%opkt	// Output Packets
 * 	%byt	// Bytes - default input
 * 	%ibyt	// Input Bytes
 * 	%obyt	// Output Bytes
 * 	%fl		// Flows
 * 	%flg	// TCP Flags
 * 	%tos	// Tos - Default src
 * 	%stos	// Src Tos
 * 	%dtos	// Dst Tos
 * 	%dir	// Direction: ingress, egress
 * 	%smk	// Src mask
 * 	%dmk	// Dst mask
 * 	%fwd	// Forwarding Status
 * 	%svln	// Src Vlan
 * 	%dvln	// Dst Vlan
 * 	%ismc	// Input Src Mac Addr
 * 	%odmc	// Output Dst Mac Addr
 * 	%idmc	// Output Src Mac Addr
 * 	%osmc	// Input Dst Mac Addr
 * 	%mpls1	// MPLS label 1
 * 	%mpls2	// MPLS label 2
 * 	%mpls3	// MPLS label 3
 * 	%mpls4	// MPLS label 4
 * 	%mpls5	// MPLS label 5
 * 	%mpls6	// MPLS label 6
 * 	%mpls7	// MPLS label 7
 * 	%mpls8	// MPLS label 8
 * 	%mpls9	// MPLS label 9
 * 	%mpls10	// MPLS label 10
 *
 * 	%bps	// bps - bits per second
 * 	%pps	// pps - packets per second
 * 	%bpp	// bps - Bytes per package
 *
 * The nfdump standard output formats line, long and extended are defined as follows:
 */

#define FORMAT_line "%ts %td %pr %sap -> %dap %pkt %byt %fl"

#define FORMAT_long "%ts %td %pr %sap -> %dap %flg %tos %pkt %byt %fl"

#define FORMAT_extended "%ts %td %pr %sap -> %dap %flg %tos %pkt %byt %pps %bps %bpp %fl"

#define FORMAT_biline "%ts %td %pr %sap <-> %dap %opkt %ipkt %obyt %ibyt %fl"

#define FORMAT_bilong "%ts %td %pr %sap <-> %dap %flg %tos %opkt %ipkt %obyt %ibyt %fl"

#define FORMAT_nsel "%ts %evt %xevt %pr %sap -> %dap %xsap -> %xdap %ibyt %obyt"

#define FORMAT_nel "%ts %nevt %pr %sap -> %dap %nsap -> %ndap"

#ifdef NSEL
#	define DefaultMode "nsel"
#else 
#	define DefaultMode "line"
#endif

/* The appropriate header line is compiled automatically.
 *
 * For each defined output format a v6 long format automatically exists as well e.g.
 * line -> line6, long -> long6, extended -> extended6
 * v6 long formats need more space to print IP addresses, as IPv6 addresses are printed in full length,
 * where as in standard output format IPv6 addresses are condensed for better readability.
 * 
 * Define your own output format and compile it into nfdumnp:
 * 1. Define your output format string.
 * 2. Test the format using standard syntax -o "fmt:<your format>"
 * 3. Create a #define statement for your output format, similar than the standard output formats above.
 * 4. Add another line into the printmap[] struct below BEFORE the last NULL line for you format:
 *    { "formatname", format_special, FORMAT_definition, NULL },
 *   The first parameter is the name of your format as recognized on the command line as -o <formatname>
 *   The second parameter is always 'format_special' - the printing function.
 *   The third parameter is your format definition as defined in #define.
 *   The forth parameter is always NULL for user defined formats.
 * 5. Recompile nfdump
 */

// Assign print functions for all output options -o
// Teminated with a NULL record
printmap_t printmap[] = {
	{ "raw",		format_file_block_record,  	NULL 			},
	{ "line", 		format_special,      		FORMAT_line 	},
	{ "long", 		format_special, 			FORMAT_long 	},
	{ "extended",	format_special, 			FORMAT_extended	},
	{ "biline", 	format_special,      		FORMAT_biline 	},
	{ "bilong", 	format_special,      		FORMAT_bilong 	},
	{ "pipe", 		flow_record_to_pipe,      	NULL 			},
	{ "csv", 		flow_record_to_csv,      	NULL 			},
	{ "null", 		flow_record_to_null,      	NULL 			},
#ifdef NSEL
	{ "nsel",		format_special, 			FORMAT_nsel		},
	{ "nel",		format_special, 			FORMAT_nel		},
#endif

// add your formats here

// This is always the last line
	{ NULL,			NULL,                       NULL			}
};

// For automatic output format generation in case of custom aggregation
#define AggrPrependFmt	"%ts %td "
#define AggrAppendFmt	"%pkt %byt %bps %bpp %fl"

// compare at most 16 chars
#define MAXMODELEN	16	

typedef struct {
	int aggregate; 
	int aggregate_mask;
	int	print_stat; 
	int syntax_only; 
	int date_sorted; 
	int do_tag; 
	int compress;
	int modify_compress;
	int flow_stat;
	int element_stat;
	int topN;
	int limit_flows;
	int sort_flows;
	time_t t_start;
	time_t t_end;
	char *aggr_fmt;
	char *rfile;
	char *Rfile;
	char *wfile;
    char *Mdirs; 
	char *ffile;
	char *print_order;
	char *print_format;
} options_t;

static void free_options(options_t *options) {
	if (options == NULL)
		return;
	free(options->aggr_fmt);
	free(options->rfile);
	free(options->Rfile);
	free(options->wfile);
	free(options->Mdirs);
	free(options->ffile);
	free(options->print_order);
	free(options->print_format);
	free(options);
};

/* Function Prototypes */
static void usage(char *name);

static void PrintSummary(stat_record_t *stat_record, int plain_numbers, int csv_output);

static stat_record_t process_block(data_block_header_t *block, options_t *options, printer_t print_record);
static stat_record_t process_data(options_t *options, printer_t print_record);


/* Functions */

#include "nfdump_inline.c"
#include "nffile_inline.c"

static void usage(char *name) {
		printf("usage %s [options] [\"filter\"]\n"
					"-h\t\tthis text you see right here\n"
					"-V\t\tPrint version and exit.\n"
					"-a\t\tAggregate netflow data.\n"
					"-A <expr>[/net]\tHow to aggregate: ',' sep list of tags see nfdump(1)\n"
					"\t\tor subnet aggregation: srcip4/24, srcip6/64.\n"
					"-b\t\tAggregate netflow records as bidirectional flows.\n"
					"-B\t\tAggregate netflow records as bidirectional flows - Guess direction.\n"
					"-r <file>\tread input from file\n"
					"-w <file>\twrite output to file\n"
					"-f\t\tread netflow filter from file\n"
					"-n\t\tDefine number of top N for stat or sorted output.\n"
					"-c\t\tLimit number of records to read from source(es)\n"
					"-D <dns>\tUse nameserver <dns> for host lookup.\n"
					"-N\t\tPrint plain numbers\n"
					"-s <expr>[/<order>]\tGenerate statistics for <expr> any valid record element.\n"
					"\t\tand ordered by <order>: packets, bytes, flows, bps pps and bpp.\n"
					"-q\t\tQuiet: Do not print the header and bottom stat lines.\n"
					"-i <ident>\tChange Ident to <ident> in file given by -r.\n"
					"-J <num>\tModify file compression: 0: uncompressed, 1: LZO, 2: BZ2, 3: LZ4, 4: LZMA compressed.\n"
					"-z\t\tLZO compress flows in output file. Used in combination with -w.\n"
					"-y\t\tLZ4 compress flows in output file. Used in combination with -w.\n"
					"-j\t\tBZ2 compress flows in output file. Used in combination with -w.\n"
					"-l <expr>\tSet limit on packets for line and packed output format.\n"
					"\t\tkey: 32 character string or 64 digit hex string starting with 0x.\n"
					"-L <expr>\tSet limit on bytes for line and packed output format.\n"
					"-I \t\tPrint netflow summary statistics info from file, specified by -r.\n"
					"-M <expr>\tRead input from multiple directories.\n"
					"\t\t/dir/dir1:dir2:dir3 Read the same files from '/dir/dir1' '/dir/dir2' and '/dir/dir3'.\n"
					"\t\trequests either -r filename or -R firstfile:lastfile without pathnames\n"
					"-m\t\tdeprecated\n"
					"-O <order> Sort order for aggregated flows - tstart, tend, flows, packets bps pps bbp etc.\n"
					"-R <expr>\tRead input from sequence of files.\n"
					"\t\t/any/dir  Read all files in that directory.\n"
					"\t\t/dir/file Read all files beginning with 'file'.\n"
					"\t\t/dir/file1:file2: Read all files from 'file1' to file2.\n"
					"-o <mode>\tUse <mode> to print out netflow records:\n"
					"\t\t raw      Raw record dump.\n"
					"\t\t line     Standard output line format.\n"
					"\t\t long     Standard output line format with additional fields.\n"
					"\t\t extended Even more information.\n"
					"\t\t csv      ',' separated, machine parseable output format.\n"
					"\t\t pipe     '|' separated legacy machine parseable output format.\n"
					"\t\t\tmode may be extended by '6' for full IPv6 listing. e.g.long6, extended6.\n"
					"-E <file>\tPrint exporter ans sampling info for collected flows.\n"
					"-v <file>\tverify netflow data file. Print version and blocks.\n"
					"-x <file>\tverify extension records in netflow data file.\n"
					"-X\t\tDump Filtertable and exit (debug option).\n"
					"-Z\t\tCheck filter syntax and exit.\n"
					"-t <time>\ttime window for filtering packets\n"
					"\t\tyyyy/MM/dd.hh:mm:ss[-yyyy/MM/dd.hh:mm:ss]\n", name);
} /* usage */


static void PrintSummary(stat_record_t *stat_record, int plain_numbers, int csv_output) {
static double	duration;
uint64_t	bps, pps, bpp;
char 		byte_str[NUMBER_STRING_SIZE], packet_str[NUMBER_STRING_SIZE];
char 		bps_str[NUMBER_STRING_SIZE], pps_str[NUMBER_STRING_SIZE], bpp_str[NUMBER_STRING_SIZE];

	bps = pps = bpp = 0;
	if ( stat_record->last_seen ) {
		duration = stat_record->last_seen - stat_record->first_seen;
		duration += ((double)stat_record->msec_last - (double)stat_record->msec_first) / 1000.0;
	} else {
		// no flows to report
		duration = 0;
	}
	if ( duration > 0 && stat_record->last_seen > 0 ) {
		bps = ( stat_record->numbytes << 3 ) / duration;	// bits per second. ( >> 3 ) -> * 8 to convert octets into bits
		pps = stat_record->numpackets / duration;			// packets per second
		bpp = stat_record->numpackets ? stat_record->numbytes / stat_record->numpackets : 0;    // Bytes per Packet
	}
	if ( csv_output ) {
		printf("Summary\n");
		printf("flows,bytes,packets,avg_bps,avg_pps,avg_bpp\n");
		printf("%llu,%llu,%llu,%llu,%llu,%llu\n",
			(long long unsigned)stat_record->numflows, (long long unsigned)stat_record->numbytes, 
			(long long unsigned)stat_record->numpackets, (long long unsigned)bps, 
			(long long unsigned)pps, (long long unsigned)bpp );
	} else if ( plain_numbers ) {
		printf("Summary: total flows: %llu, total bytes: %llu, total packets: %llu, avg bps: %llu, avg pps: %llu, avg bpp: %llu\n",
			(long long unsigned)stat_record->numflows, (long long unsigned)stat_record->numbytes, 
			(long long unsigned)stat_record->numpackets, (long long unsigned)bps, 
			(long long unsigned)pps, (long long unsigned)bpp );
	} else {
		format_number(stat_record->numbytes, byte_str, DONT_SCALE_NUMBER, VAR_LENGTH);
		format_number(stat_record->numpackets, packet_str, DONT_SCALE_NUMBER, VAR_LENGTH);
		format_number(bps, bps_str, DONT_SCALE_NUMBER, VAR_LENGTH);
		format_number(pps, pps_str, DONT_SCALE_NUMBER, VAR_LENGTH);
		format_number(bpp, bpp_str, DONT_SCALE_NUMBER, VAR_LENGTH);
		printf("Summary: total flows: %llu, total bytes: %s, total packets: %s, avg bps: %s, avg pps: %s, avg bpp: %s\n",
		(unsigned long long)stat_record->numflows, byte_str, packet_str, bps_str, pps_str, bpp_str );
	}

} // End of PrintSummary

stat_record_t process_block(data_block_header_t *block, options_t *options, printer_t print_record)
{
stat_record_t 		stat_record;
master_record_t		*master_record;
common_record_t 	*flow_record, *record_ptr;
char *ConvertBuffer = NULL;

	memset((void *)&stat_record, 0, sizeof(stat_record_t));

#ifdef COMPAT15
	if ( block->id == DATA_BLOCK_TYPE_1 ) {
		common_record_v1_t *v1_record = (common_record_v1_t *)nffile_r->buff_ptr;
		// create an extension map for v1 blocks
		if ( v1_map_done == 0 ) {
			extension_map_t *map = malloc(sizeof(extension_map_t) + 2 * sizeof(uint16_t) );
			if ( ! map ) {
				LogError("malloc() allocation error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
				exit(255);
			}
			map->type 	= ExtensionMapType;
			map->size 	= sizeof(extension_map_t) + 2 * sizeof(uint16_t);
			if (( map->size & 0x3 ) != 0 ) {
				map->size += 4 - ( map->size & 0x3 );
			}

			map->map_id = INIT_ID;

			map->ex_id[0]  = EX_IO_SNMP_2;
			map->ex_id[1]  = EX_AS_2;
			map->ex_id[2]  = 0;
			
			map->extension_size  = 0;
			map->extension_size += extension_descriptor[EX_IO_SNMP_2].size;
			map->extension_size += extension_descriptor[EX_AS_2].size;

			if ( Insert_Extension_Map(extension_map_list,map) && write_file ) {
				// flush new map
				AppendToBuffer(nffile_w, (void *)map, map->size);
			} // else map already known and flushed

			v1_map_done = 1;
		}

		// convert the records to v2
		for ( i=0; i < nffile_r->block_header->NumRecords; i++ ) {
			common_record_t *v2_record = (common_record_t *)v1_record;
			Convert_v1_to_v2((void *)v1_record);
			// now we have a v2 record -> use size of v2_record->size
			v1_record = (common_record_v1_t *)((pointer_addr_t)v1_record + v2_record->size);
		}
		nffile_r->block_header->id = DATA_BLOCK_TYPE_2;
	}
#endif

	if ( block->id == Large_BLOCK_Type ) {
		// skip
		printf("Xstat block skipped ...\n");
		return stat_record;
	}

	if ( block->id != DATA_BLOCK_TYPE_2 ) {
		if ( block->id == DATA_BLOCK_TYPE_1 ) {
			LogError("Can't process nfdump 1.5.x block type 1. Add --enable-compat15 to compile compatibility code. Skip block.\n");
		} else {
			LogError("Can't process block type %u. Skip block.\n", block->id);
		}
		skipped_blocks++;
		return stat_record;
	}

	record_ptr = (common_record_t*)block + sizeof(data_block_header_t);
	for ( int i=0; i < block->NumRecords; i++ ) {
		flow_record = record_ptr;
		switch ( record_ptr->type ) {
			case CommonRecordV0Type: 
				// convert common record v0
				if ( !ConvertBuffer ) {
					ConvertBuffer = malloc(65536);
					if ( !ConvertBuffer ) {
						LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
						exit(255);
					}
				}
				ConvertCommonV0((void *)record_ptr, (common_record_t *)ConvertBuffer);
				flow_record = (common_record_t *)ConvertBuffer;
				dbg_printf("Converted type %u to %u record\n", CommonRecordV0Type, CommonRecordType);
			case CommonRecordType: {
				int match;
				uint32_t map_id;
				generic_exporter_t *exp_info;

				// valid flow_record converted if needed
				map_id = flow_record->ext_map;
				exp_info = exporter_list[flow_record->exporter_sysid];

				if ( map_id >= MAX_EXTENSION_MAPS ) {
					LogError("Corrupt data file. Extension map id %u too big.\n", flow_record->ext_map);
					exit(255);
				}
				if ( extension_map_list->slot[map_id] == NULL ) {
					LogError("Corrupt data file. Missing extension map %u. Skip record.\n", flow_record->ext_map);
					record_ptr = (common_record_t *)((pointer_addr_t)record_ptr + record_ptr->size);	
					continue;
				} 

				total_flows++;
				master_record = &(extension_map_list->slot[map_id]->master_record);
				Engine->nfrecord = (uint64_t *)master_record;
				ExpandRecord_v2( flow_record, extension_map_list->slot[map_id], 
					exp_info ? &(exp_info->info) : NULL, master_record);

				// Time based filter
				// if no time filter is given, the result is always true
				match  = options->t_start && (master_record->first < options->t_start || master_record->last > options->t_end) ? 0 : 1;
				match &= options->limit_flows ? stat_record.numflows < options->limit_flows : 1;

				// filter netflow record with user supplied filter
				if ( match ) 
					match = (*Engine->FilterEngine)(Engine);

				if ( match == 0 ) { // record failed to pass all filters
					// increment pointer by number of bytes for netflow record
					record_ptr = (common_record_t *)((pointer_addr_t)record_ptr + record_ptr->size);	
					// go to next record
					continue;
				}

				// Records passed filter -> continue record processing
				// Update statistics
				UpdateStat(&stat_record, master_record);

				// update number of flows matching a given map
				extension_map_list->slot[map_id]->ref_count++;

				if ( options->flow_stat ) {
					AddFlow(flow_record, master_record, extension_map_list->slot[map_id]);
					if ( options->element_stat ) {
						AddStat(flow_record, master_record);
					} 
				} else if ( options->element_stat ) {
					AddStat(flow_record, master_record);
				} else if ( options->sort_flows ) {
					InsertFlow(flow_record, master_record, extension_map_list->slot[map_id]);
				} else {
					//if ( write_file ) {
					//	AppendToBuffer(nffile_w, (void *)flow_record, flow_record->size);
					//} else 
					if ( print_record ) {
						char *string;
						// if we need to print out this record
						print_record(master_record, &string, options->do_tag);
						if ( string ) {
							if ( options->limit_flows ) {
								if ( (stat_record.numflows <= options->limit_flows) )
									printf("%s\n", string);
							} else 
								printf("%s\n", string);
						}
					} else { 
						// mutually exclusive conditions should prevent executing this code
						// this is buggy!
						printf("Bug! - this code should never get executed in file %s line %d\n", __FILE__, __LINE__);
					}
				} // sort_flows - else
				}
				break; 
			case ExtensionMapType: {
				//extension_map_t *map = (extension_map_t *)record_ptr;

				//if ( Insert_Extension_Map(extension_map_list, map) && write_file ) {
					// flush new map
			//		AppendToBuffer(nffile_w, (void *)map, map->size);
				//} // else map already known and flushed
				} break;
			case ExporterRecordType:
			case SamplerRecordype:
					// Silently skip exporter records
				break;
			case ExporterInfoRecordType: {
				int ret = AddExporterInfo((exporter_info_record_t *)record_ptr);
				if ( ret != 0 ) {
					//	if ( write_file && ret == 1 ) 
					//		AppendToBuffer(nffile_w, (void *)record_ptr, record_ptr->size);
					//} else {
				//		LogError("Failed to add Exporter Record\n");
				//	}
					} 
				}
				break;
			case ExporterStatRecordType:
				AddExporterStat((exporter_stats_record_t *)record_ptr);
				break;
			case SamplerInfoRecordype: {
				int ret = AddSamplerInfo((sampler_info_record_t *)record_ptr);
				if ( ret != 0 ) {
					///	if ( write_file && ret == 1 ) 
				//			AppendToBuffer(nffile_w, (void *)flow_record, flow_record->size);
				//	} else {
				//		LogError("Failed to add Sampler Record\n");
				}
				} break;
			default: {
				LogError("Skip unknown record type %i\n", record_ptr->type);
			}
		}

		// Advance pointer by number of bytes for netflow record
		record_ptr = (common_record_t *)((pointer_addr_t)record_ptr + record_ptr->size);	


	} // for all records
	free(ConvertBuffer);
	return stat_record;
}

stat_record_t process_data(options_t *options, printer_t print_record) {
nffile_t			*nffile_w, *nffile_r;
stat_record_t 		stat_record;
int 				done, write_file;

#ifdef COMPAT15
int	v1_map_done = 0;
#endif
	
	// time window of all matched flows
	memset((void *)&stat_record, 0, sizeof(stat_record_t));
	stat_record.first_seen = 0x7fffffff;
	stat_record.msec_first = 999;

	// Do the logic first

	// do not print flows when doing any stats are sorting
	if ( options->sort_flows || options->flow_stat || options->element_stat ) {
		print_record = NULL;
		// do not write flows to file, when doing any stats
		write_file = 0;
	} else {
		// -w may apply for flow_stats later
		write_file = options->wfile != NULL;
	}

	nffile_r = NULL;
	nffile_w = NULL;

	// Get the first file handle
	nffile_r = GetNextFile(NULL, options->t_start, options->t_end);
	if ( !nffile_r ) {
		LogError("GetNextFile() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
		return stat_record;
	}
	if ( nffile_r == EMPTY_LIST ) {
		LogError("Empty file list. No files to process\n");
		return stat_record;
	}

	// preset time window of all processed flows to the stat record in first flow file
	t_first_flow = nffile_r->stat_record->first_seen;
	t_last_flow  = nffile_r->stat_record->last_seen;

	// store infos away for later use
	// although multiple files may be processed, it is assumed that all 
	// have the same settings
	is_anonymized = IP_ANONYMIZED(nffile_r);
	strncpy(Ident, nffile_r->file_header->ident, IDENTLEN);
	Ident[IDENTLEN-1] = '\0';

	// prepare output file if requested
	if ( write_file ) {
		nffile_w = OpenNewFile(options->wfile, NULL, options->compress, IP_ANONYMIZED(nffile_r), NULL );
		if ( !nffile_w ) {
			if ( nffile_r ) {
				CloseFile(nffile_r);
				DisposeFile(nffile_r);
			}
			return stat_record;
		}
	}

	// setup Filter Engine to point to master_record, as any record read from file
	// is expanded into this record
	// Engine->nfrecord = (uint64_t *)master_record;

	done = 0;
	while ( !done ) {
	int ret;

		// get next data block from file
		ret = ReadBlock(nffile_r);

		switch (ret) {
			case NF_CORRUPT:
			case NF_ERROR:
				if ( ret == NF_CORRUPT ) 
					LogError("Skip corrupt data file '%s'\n",GetCurrentFilename());
				else 
					LogError("Read error in file '%s': %s\n",GetCurrentFilename(), strerror(errno) );
				// fall through - get next file in chain
			case NF_EOF: {
				nffile_t *next = GetNextFile(nffile_r, options->t_start, options->t_end);
				if ( next == EMPTY_LIST ) {
					done = 1;
				} else if ( next == NULL ) {
					done = 1;
					LogError("Unexpected end of file list\n");
				} else {
					// Update global time span window
					if ( next->stat_record->first_seen < t_first_flow )
						t_first_flow = next->stat_record->first_seen;
					if ( next->stat_record->last_seen > t_last_flow ) 
						t_last_flow = next->stat_record->last_seen;
				}
				}
				// Continue with next file
				continue;
			default:
				// successfully read block
				total_bytes += ret;
		}

		process_block(
				nffile_r->block_header, 
				options,
				print_record
		);

		// check if we are done, due to -c option 
		if ( options->limit_flows ) {
			done = stat_record.numflows >= options->limit_flows;
		}

	} // while

	CloseFile(nffile_r);

	// flush output file
	if ( write_file ) {
		// flush current buffer to disc
		if ( nffile_w->block_header->NumRecords ) {
			if ( WriteBlock(nffile_w) <= 0 ) {
				LogError("Failed to write output buffer to disk: '%s'" , strerror(errno));
			} 
		}

		/* Stat info */
		if ( write_file ) {
			/* Copy stat info and close file */
			memcpy((void *)nffile_w->stat_record, (void *)&stat_record, sizeof(stat_record_t));
			CloseUpdateFile(nffile_w, nffile_r->file_header->ident );
			nffile_w = DisposeFile(nffile_w);
		} // else stdout
	}	 

	PackExtensionMapList(extension_map_list);

	DisposeFile(nffile_r);
	return stat_record;

} // End of process_data


int main( int argc, char **argv ) {
struct stat stat_buff;
stat_record_t	sum_stat;
printer_t 	print_record;
nfprof_t 	profile_data;
char 		 *filter, *tstring, *stat_type;
char		*byte_limit_string, *packet_limit_string, *record_header;
char		*query_file, *nameserver;
int 		c, ffd, ret, fdump;
int 		i, user_format, quiet, bidir;
int			plain_numbers, GuessDir, pipe_output, csv_output;
char 		Ident[IDENTLEN];
options_t   *options = calloc(1, sizeof(options_t));

	filter = tstring = stat_type = NULL;
	byte_limit_string = packet_limit_string = NULL;
	fdump = 0;
	bidir			= 0;
	options->topN   = -1;
	options->modify_compress = -1;
	total_bytes		= 0;
	total_flows		= 0;
	skipped_blocks	= 0;
	quiet			= 0;
	user_format		= 0;
	plain_numbers   = 0;
	pipe_output		= 0;
	csv_output		= 0;
	is_anonymized	= 0;
	GuessDir		= 0;
	nameserver		= NULL;

	print_record  	= NULL;
	query_file		= NULL;
	record_header 	= NULL;

	Ident[0] = '\0';

	while ((c = getopt(argc, argv, "6aA:Bbc:D:E:s:hn:i:jf:qyzr:v:w:J:K:M:NImO:R:XZt:TVv:x:l:L:o:")) != EOF) {
		switch (c) {
			case 'h':
				usage(argv[0]);
				exit(0);
				break;
			case 'a':
				options->aggregate = 1;
				break;
			case 'A':
				if ( !ParseAggregateMask(optarg, &options->aggr_fmt ) ) {
					exit(255);
				}
				options->aggregate_mask = 1;
				break;
			case 'B':
				GuessDir = 1;
			case 'b':
				if ( !SetBidirAggregation() ) {
					exit(255);
				}
				bidir	  = 1;
				// implies
				options->aggregate = 1;
				break;
			case 'D':
				nameserver = optarg;
				if ( !set_nameserver(nameserver) ) {
					exit(255);
				}
				break;
			case 'E':
				query_file = optarg;
				if ( !InitExporterList() ) {
					exit(255);
				}
				PrintExporters(query_file);
				exit(0);
				break;
			case 'X':
				fdump = 1;
				break;
			case 'Z':
				options->syntax_only = 1;
				break;
			case 'q':
				quiet = 1;
				break;
			case 'j':
				if ( options->compress ) {
					LogError("Use one compression: -z for LZO, -j for BZ2 or -y for LZ4 compression\n");
					exit(255);
				}
				options->compress = BZ2_COMPRESSED;
				break;
			case 'y':
				if ( options->compress ) {
					LogError("Use one compression: -z for LZO, -j for BZ2 or -y for LZ4 compression\n");
					exit(255);
				}
				options->compress = LZ4_COMPRESSED;
				break;
			case 'z':
				if ( options->compress ) {
					LogError("Use one compression: -z for LZO, -j for BZ2 or -y for LZ4 compression\n");
					exit(255);
				}
				options->compress = LZO_COMPRESSED;
				break;
			case 'c':	
				options->limit_flows = atoi(optarg);
				if ( !options->limit_flows ) {
					LogError("Option -c needs a number > 0\n");
					exit(255);
				}
				break;
			case 's':
				stat_type = optarg;
                if ( !SetStat(stat_type, &options->element_stat, &options->flow_stat) ) {
                    exit(255);
                } 
				break;
			case 'V': {
				char *e1, *e2;
				e1 = "";
				e2 = "";
#ifdef NSEL
				e1 = "NSEL-NEL";
#endif
				printf("%s: Version: %s%s%s\n",argv[0], e1, e2, nfdump_version);
				exit(0);
				} break;
			case 'l':
				packet_limit_string = optarg;
				break;
			case 'K':
				LogError("*** Anonymisation moved! Use nfanon to anonymise flows!\n");
				exit(255);
				break;
			case 'L':
				byte_limit_string = optarg;
				break;
			case 'N':
				plain_numbers = 1;
				break;
			case 'f':
				options->ffile = strdup(optarg);
				break;
			case 't':
				tstring = optarg;
				break;
			case 'r':
				options->rfile = strdup(optarg);
				if ( strcmp(options->rfile, "-") == 0 )
					options->rfile = NULL;
				break;
			case 'm':
				free(options->print_order);
				options->print_order = strdup("tstart");
				Parse_PrintOrder(options->print_order);
				options->date_sorted = 1;
				LogError("Option -m deprecated. Use '-O tstart' instead\n");
				break;
			case 'M':
				options->Mdirs = optarg;
				break;
			case 'I':
				options->print_stat++;
				break;
			case 'o':	// output mode
				options->print_format = strdup(optarg);
				break;
			case 'O': {	// stat order by
				int ret;
				free(options->print_order);
				options->print_order = strdup(optarg);
				ret = Parse_PrintOrder(options->print_order);
				if ( ret < 0 ) {
					LogError("Unknown print order '%s'\n", options->print_order);
					exit(255);
				}
				options->date_sorted = ret == 6;		// index into order_mode
				} break;
			case 'R':
				options->Rfile = strdup(optarg);
				break;
			case 'w':
				options->wfile = strdup(optarg);
				break;
			case 'n':
				options->topN = atoi(optarg);
				if ( options->topN < 0 ) {
					LogError("TopnN number %i out of range\n", options->topN);
					exit(255);
				}
				break;
			case 'T':
				options->do_tag = 1;
				break;
			case 'i':
				strncpy(Ident, optarg, IDENT_SIZE);
				Ident[IDENT_SIZE - 1] = 0;
				if ( strchr(Ident, ' ') ) {
					LogError("Ident must not contain spaces\n");
					exit(255);
				}
				break;
			case 'J':
				options->modify_compress = atoi(optarg);
				if ( (options->modify_compress < NOT_COMPRESSED) || (options->modify_compress > LZMA_COMPRESSED) ) {
					LogError("Expected -J <num>, 0: uncompressed, 1: LZO, 2: BZ2, 3: LZ4, 4: LZMA compressed.\n");
					exit(255);
				}
				break;
			case 'x':
				query_file = optarg;
				InitExtensionMaps(NO_EXTENSION_LIST);
				DumpExMaps(query_file);
				exit(0);
				break;
			case 'v':
				query_file = optarg;
				QueryFile(query_file);
				exit(0);
				break;
			case '6':	// print long IPv6 addr
				Setv6Mode(1);
				break;
			default:
				usage(argv[0]);
				exit(0);
		}
	}
	if (argc - optind > 1) {
		usage(argv[0]);
		exit(255);
	} else {
		/* user specified a pcap filter */
		filter = argv[optind];
		FilterFilename = NULL;
	}
	
	// Modify compression
	if ( options->modify_compress >= 0 ) {
		if ( !options->rfile && !options->Rfile ) {
			LogError("Expected -r <file> or -R <dir> to change compression\n");
			exit(255);
		}
		exit(ModifyCompressFile(options->rfile, options->Rfile, options->modify_compress));
	}

	// Change Ident only
	if ( options->rfile && strlen(Ident) > 0 ) {
		exit(ChangeIdent(options->rfile, Ident));
	}

	if ( (options->element_stat || options->flow_stat) && (options->topN == -1)  ) 
		options->topN = 10;

	if ( options->topN < 0 )
		options->topN = 0;

	if ( (options->element_stat && !options->flow_stat) && options->aggregate_mask ) {
		LogError("Warning: Aggregation ignored for element statistics\n");
		options->aggregate_mask = 0;
	}

	if ( !options->flow_stat && options->aggregate_mask ) {
		options->aggregate = 1;
	}

	if ( options->rfile && options->Rfile ) {
		LogError("-r and -R are mutually exclusive. Please specify either -r or -R\n");
		exit(255);
	}
	if ( options->Mdirs && !(options->rfile || options->Rfile) ) {
		LogError("-M needs either -r or -R to specify the file or file list. Add '-R .' for all files in the directories.\n");
		exit(255);
	}

	extension_map_list = InitExtensionMaps(NEEDS_EXTENSION_LIST);
	if ( !InitExporterList() ) {
		exit(255);
	}

	SetupInputFileSequence(options->Mdirs, options->rfile, options->Rfile);

	if ( options->print_stat ) {
		nffile_t *nffile;
		if ( !options->rfile && !options->Rfile && !options->Mdirs) {
			LogError("Expect data file(s).\n");
			exit(255);
		}

		memset((void *)&sum_stat, 0, sizeof(stat_record_t));
		sum_stat.first_seen = 0x7fffffff;
		sum_stat.msec_first = 999;
		nffile = GetNextFile(NULL, 0, 0);
		if ( !nffile ) {
			LogError("Error open file: %s\n", strerror(errno));
			exit(250);
		}
		while ( nffile && nffile != EMPTY_LIST ) {
			SumStatRecords(&sum_stat, nffile->stat_record);
			nffile = GetNextFile(nffile, 0, 0);
		}
		PrintStat(&sum_stat);
		exit(0);
	}

	// handle print mode
	if ( !options->print_format ) {
		// automatically select an appropriate output format for custom aggregation
		// aggr_fmt is compiled by ParseAggregateMask
		if ( options->aggr_fmt ) {
			int len = strlen(AggrPrependFmt) + strlen(options->aggr_fmt) + strlen(AggrAppendFmt) + 7;	// +7 for 'fmt:', 2 spaces and '\0'
			options->print_format = malloc(len);
			if ( !options->print_format ) {
				LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
				exit(255);
			}
			snprintf(options->print_format, len, "fmt:%s %s %s",AggrPrependFmt, options->aggr_fmt, AggrAppendFmt );
			options->print_format[len-1] = '\0';
		} else if ( bidir ) {
			options->print_format = strdup("biline");
		} else
			options->print_format = strdup(DefaultMode);
	}

	if ( strncasecmp(options->print_format, "fmt:", 4) == 0 ) {
		// special user defined output format
		char *format = &options->print_format[4];
		if ( strlen(format) ) {
			if ( !ParseOutputFormat(format, plain_numbers, printmap) )
				exit(255);
			print_record  = format_special;
			record_header = get_record_header();
			user_format	  = 1;
		} else {
			LogError("Missing format description for user defined output format!\n");
			exit(255);
		}
	} else {
		// predefined output format

		// Check for long_v6 mode
		i = strlen(options->print_format);
		if ( i > 2 ) {
			if ( options->print_format[i-1] == '6' ) {
				Setv6Mode(1);
				options->print_format[i-1] = '\0';
			} else 
				Setv6Mode(0);
		}

		i = 0;
		while ( printmap[i].printmode ) {
			if ( strncasecmp(options->print_format, printmap[i].printmode, MAXMODELEN) == 0 ) {
				if ( printmap[i].Format ) {
					if ( !ParseOutputFormat(printmap[i].Format, plain_numbers, printmap) )
						exit(255);
					// predefined custom format
					print_record  = printmap[i].func;
					record_header = get_record_header();
					user_format	  = 1;
				} else {
					// To support the pipe output format for element stats - check for pipe, and remember this
					if ( strncasecmp(options->print_format, "pipe", MAXMODELEN) == 0 ) {
						pipe_output = 1;
					}
					if ( strncasecmp(options->print_format, "csv", MAXMODELEN) == 0 ) {
						csv_output = 1;
						set_record_header();
						record_header = get_record_header();
					}
					// predefined static format
					print_record  = printmap[i].func;
					user_format	  = 0;
				}
				break;
			}
			i++;
		}
	}

	if ( !print_record ) {
		LogError("Unknown output mode '%s'\n", options->print_format);
		exit(255);
	}

	if ( options->aggregate && (options->flow_stat || options->element_stat) ) {
		options->aggregate = 0;
		LogError("Command line switch -s overrides -a\n");
	}

	if ( !filter && options->ffile ) {
		if ( stat(options->ffile, &stat_buff) ) {
			LogError("Can't stat filter file '%s': %s\n", options->ffile, strerror(errno));
			exit(255);
		}
		filter = (char *)malloc(stat_buff.st_size+1);
		if ( !filter ) {
			LogError("malloc() error in %s line %d: %s\n", __FILE__, __LINE__, strerror(errno) );
			exit(255);
		}
		ffd = open(options->ffile, O_RDONLY);
		if ( ffd < 0 ) {
			LogError("Can't open filter file '%s': %s\n", options->ffile, strerror(errno));
			exit(255);
		}
		ret = read(ffd, (void *)filter, stat_buff.st_size);
		if ( ret < 0   ) {
			perror("Error reading filter file");
			close(ffd);
			exit(255);
		}
		total_bytes += ret;
		filter[stat_buff.st_size] = 0;
		close(ffd);

		FilterFilename = options->ffile;
	}

	// if no filter is given, set the default ip filter which passes through every flow
	if ( !filter  || strlen(filter) == 0 ) 
		filter = "any";

	Engine = CompileFilter(filter);
	if ( !Engine ) 
		exit(254);

	if ( fdump ) {
		printf("StartNode: %i Engine: %s\n", Engine->StartNode, Engine->Extended ? "Extended" : "Fast");
		DumpList(Engine);
		exit(0);
	}

	if ( options->syntax_only )
		exit(0);

	if ( options->print_order && options->flow_stat ) {
		printf("-s record and -O (-m) are mutually exclusive options\n");
		exit(255);
	}

	if ((options->aggregate || options->flow_stat || options->print_order)  && !Init_FlowTable() )
			exit(250);

	if (options->element_stat && !Init_StatTable(HashBits, NumPrealloc) )
			exit(250);

	SetLimits(options->element_stat || options->aggregate || options->flow_stat, packet_limit_string, byte_limit_string);

	if ( tstring ) {
		if ( !ScanTimeFrame(tstring, &options->t_start, &options->t_end) )
			exit(255);
	}


	if ( !(options->flow_stat || options->element_stat || options->wfile || quiet ) && record_header ) {
		if ( user_format ) {
			printf("%s\n", record_header);
		} else {
			// static format - no static format with header any more, but keep code anyway
			if ( Getv6Mode() ) {
				printf("%s\n", record_header);
			} else
				printf("%s\n", record_header);
		}
	}

	nfprof_start(&profile_data);
	sum_stat = process_data(options, print_record);
	nfprof_end(&profile_data, total_flows);

	if ( total_bytes == 0 ) {
		printf("No matched flows\n");
		exit(0);
	}

	if (options->aggregate || options->print_order) {
		if ( options->wfile ) {
			nffile_t *nffile = OpenNewFile(options->wfile, NULL, options->compress, is_anonymized, NULL);
			if ( !nffile ) 
				exit(255);
			if ( ExportFlowTable(nffile, options->aggregate, bidir, options->date_sorted, extension_map_list) ) {
				CloseUpdateFile(nffile, Ident );	
			} else {
				CloseFile(nffile);
				unlink(options->wfile);
			}
			DisposeFile(nffile);
		} else {
			PrintFlowTable(print_record, options->topN, options->do_tag, GuessDir, extension_map_list);
		}
	}

	if (options->flow_stat) {
		PrintFlowStat(record_header, print_record, options->topN, options->do_tag, quiet, csv_output, extension_map_list);
#ifdef DEVEL
		printf("Loopcnt: %u\n", loopcnt);
#endif
	} 

	if (options->element_stat) {
		PrintElementStat(&sum_stat, plain_numbers, record_header, print_record, options->topN, options->do_tag, quiet, pipe_output, csv_output);
	} 

	if ( !quiet ) {
		if ( csv_output ) {
			PrintSummary(&sum_stat, plain_numbers, csv_output);
		} else if ( !options->wfile ) {
			if (is_anonymized)
				printf("IP addresses anonymised\n");
			PrintSummary(&sum_stat, plain_numbers, csv_output);
			if ( t_last_flow == 0 ) {
				// in case of a pre 1.6.6 collected and empty flow file
 				printf("Time window: <unknown>\n");
			} else {
 				printf("Time window: %s\n", TimeString(t_first_flow, t_last_flow));
			}
			printf("Total flows processed: %u, Blocks skipped: %u, Bytes read: %llu\n", 
				total_flows, skipped_blocks, (unsigned long long)total_bytes);
			nfprof_print(&profile_data, stdout);
		}
	}

	free_options(options);
	Dispose_FlowTable();
	Dispose_StatTable();
	FreeExtensionMaps(extension_map_list);

#ifdef DEVEL
	if ( hash_hit || hash_miss )
		printf("Hash hit: %i, miss: %i, skip: %i, ratio: %5.3f\n", hash_hit, hash_miss, hash_skip, (float)hash_hit/((float)(hash_hit+hash_miss)));
#endif

	return 0;
}
