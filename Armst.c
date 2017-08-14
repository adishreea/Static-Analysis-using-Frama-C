#include <stdio.h>

void main()

{

	long int n1, n2;	/* intervals */

	long int i, temp, num, rem;

	printf("%d", 6/0);

  	printf("Enter two intervals: ");

	scanf("%ld %ld", &n1, &n2);

  	printf("Armstrong numbers between %ld and %ld are: \n", n1, n2);
/*@ ensures n1 > 0;
    ensures n2 > 0;

*/

/*@ loop invariant n1 <= i <= n2;

*/
 	
	for(i=n1; i<=n2; ++i)

  		{

/*@ assigns temp, num;

*/

      		temp=i;

      		num=0;

    		while(temp!=0)

      		{

/*@ assigns rem, num, temp;

*/

          		rem=(temp%10);

          		num+=rem*rem*rem;

        		temp/=10;

      		}

      		if(i==num)

          		printf("%ld\t ",i);

  	}

	printf("\n");	

}