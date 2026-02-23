int main1(int b,int n){
  int c, j, v;

  c=b+23;
  j=c;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(b, Pre) + 23;
  loop invariant j <= c;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant c == b + 23;

  loop invariant j <= \at(b, Pre) + 23;
  loop invariant (c >= 0 ==> 0 <= j && j <= c) &&
                   (c < 0  ==> c <= j && j <= 0);

  loop assigns j;
*/
while (j>0) {
      j = j/2;
  }

}
