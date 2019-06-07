#include "ff.h"			/* Declarations of FatFs API */

#include "FreeRTOS.h"	// O/S definitions */
#include "semphr.h"	// O/S definitions */

#if FF_DEFINED != 86604	/* Revision ID */
#error Wrong include file (ff.h).
#endif

#if FF_FS_REENTRANT
/*------------------------------------------------------------------------*/
/* Create a Synchronization Object										  */
/*------------------------------------------------------------------------*/
/* This function is called in f_mount() function to create a new
/  synchronization object, such as semaphore and mutex. When a 0 is returned,
/  the f_mount() function fails with FR_INT_ERR.
*/

int ff_cre_syncobj (	/* !=0:Function succeeded, ==0:Could not create due to any error */
	BYTE vol,			/* Corresponding logical drive being processed */
	FF_SYNC_t *sobj		/* Pointer to return the created sync object */
)
{
    configASSERT(vol == 0);
	int ret;

	*sobj = xSemaphoreCreateMutex();	/* FreeRTOS */
	ret = (int)(*sobj != NULL);

	return ret;
}



/*------------------------------------------------------------------------*/
/* Delete a Synchronization Object                                        */
/*------------------------------------------------------------------------*/
/* This function is called in f_mount() function to delete a synchronization
/  object that created with ff_cre_syncobj function. When a 0 is returned,
/  the f_mount() function fails with FR_INT_ERR.
*/

int ff_del_syncobj (	/* !=0:Function succeeded, ==0:Could not delete due to any error */
	FF_SYNC_t sobj		/* Sync object tied to the logical drive to be deleted */
)
{
	int ret;

    vSemaphoreDelete(sobj);		/* FreeRTOS */
	ret = 1;

	return ret;
}



/*------------------------------------------------------------------------*/
/* Request Grant to Access the Volume                                     */
/*------------------------------------------------------------------------*/
/* This function is called on entering file functions to lock the volume.
/  When a 0 is returned, the file function fails with FR_TIMEOUT.
*/

int ff_req_grant (	/* 1:Got a grant to access the volume, 0:Could not get a grant */
	FF_SYNC_t sobj	/* Sync object to wait */
)
{
	int ret;

	ret = (int)(xSemaphoreTake(sobj, pdMS_TO_TICKS(FF_FS_TIMEOUT)) == pdTRUE);	/* FreeRTOS */

	return ret;
}



/*------------------------------------------------------------------------*/
/* Release Grant to Access the Volume                                     */
/*------------------------------------------------------------------------*/
/* This function is called on leaving file functions to unlock the volume.
*/

void ff_rel_grant (
	FF_SYNC_t sobj	/* Sync object to be signaled */
)
{
	xSemaphoreGive(sobj);	/* FreeRTOS */
}

#endif




#if FF_USE_LFN == 3	/* LFN with a working buffer on the heap */
/*------------------------------------------------------------------------*/
/* Allocate a memory block                                                */
/*------------------------------------------------------------------------*/
/* If a NULL is returned, the file function fails with FR_NOT_ENOUGH_CORE.
*/
void* ff_memalloc (	/* Returns pointer to the allocated memory block */
	UINT msize		/* Number of bytes to allocate */
)
{
	return pvPortMalloc(msize);	/* Allocate a new memory block with POSIX API */
}


/*------------------------------------------------------------------------*/
/* Free a memory block                                                    */
/*------------------------------------------------------------------------*/

void ff_memfree (
	void* mblock	/* Pointer to the memory block to free */
)
{
	vPortFree(mblock);	/* Discard the memory block with POSIX API */
}

#endif



/* RTC function */
#if !FF_FS_READONLY && !FF_FS_NORTC
DWORD get_fattime (void)
{
	return (DWORD)xTaskGetTickCount();
}
#endif