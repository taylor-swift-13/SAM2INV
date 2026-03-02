int main1(int b,int n){
  int y, i, p;

  y=13;
  i=1;
  p=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 13;
  loop invariant (p - \at(n,Pre)) % 2 == 0;
  loop invariant n == \at(n,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant (p - n) % 2 == 0;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);

  loop invariant (p - n) % 2 == 0 && b == \at(b, Pre) && n == \at(n, Pre);
  loop assigns p;
*/
while (1) {
      p = p+2;
      p = p%2;
  }

}
