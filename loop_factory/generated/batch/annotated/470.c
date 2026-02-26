int main1(int a,int n){
  int b, c, j;

  b=(n%21)+4;
  c=0;
  j=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == (n % 21) + 4;
  loop invariant j >= 0;
  loop invariant (j % 2) == 0;
  loop invariant b == (\at(n, Pre) % 21) + 4;
  loop invariant j % 2 == 0;
  loop invariant b == ((\at(n,Pre) % 21) + 4);

  loop assigns j;
*/
while (1) {
      j = j+2;
      if (j+1<b) {
          j = j+j;
      }
  }

}
