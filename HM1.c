#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define sizeQueue 100
#define sizeName 15
#define sizeLastName 25
#define sizeSocialSec 10

typedef struct objectMessage{
    char name[sizeName];
    char lastname[sizeLastName];
    char socialSecurity[sizeSocialSec];
} objectMessage;

struct objectMessage messageQueue[sizeQueue];
int auxQueue = -1;



/*@   
    requires 0<=n1 && \valid(s1+(0..n1-1));
    requires 0<=n2 && \valid(s2+(0..n2-1));
    assigns \nothing;	
*/


void copy(char s1[], int n1, char s2[], int n2){
    if (n1>n2){

	  /*@ loop assigns i,s1;
        loop invariant s1[0..n2-1] == s2[0..n2-1];
        loop invariant 0<=i<=n2;
	  loop invariant s1[i-1]==s2[i-1];
	  
        
        */
	  

        for (int i=0; i<n2; i++) {
        s1[i] = s2[i];
        }
        
    }else{
	  /*@ loop assigns i, s1;
        loop invariant s1[0..n1-1] == s2[0..n1-1];
        loop invariant 0<=i<=n1;
        loop invariant s1[i-1]==s2[i-1];
        */

        for (int i=0; i<n1; i++) {
        s1[i] = s2[i];
        }
    }
    
}





/*@
	  requires 0<=n1<=15 && \valid(first_name+(0..n1-1));
        requires 0<=n2<=25 && \valid(last_name+(0..n2-1));
        requires 0<=n3<=10 && \valid(social_security_number+(0..n3-1));

    behavior complete:

        assumes auxQueue >= 100; 
	  ensures  \result == -1;
    
    behavior empty :
        assumes auxQueue < 100;
        ensures  \result == 1;
	 

*/

int leave_message(char first_name[], int n1, char last_name[], int n2, char social_security_number[], int n3){
    if (auxQueue>=sizeQueue){


        return -1;
    }else{
        auxQueue++;
        objectMessage auxMessage;
		
 	
        copy(auxMessage.name,sizeName,first_name,n1);
        copy(auxMessage.lastname,sizeLastName,last_name,n2);
        copy(auxMessage.socialSecurity,sizeSocialSec,social_security_number,n3);
        
        messageQueue[auxQueue]=auxMessage;
       
        return 1;
        
    }
}

