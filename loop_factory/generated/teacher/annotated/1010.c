int main1(int b,int n){
  int y, i, p;

  y=13;
  i=1;
  p=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 13;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == b || p == \at(n, Pre);
  loop invariant p == \at(n, Pre) || p == b;
  loop invariant p == \at(n, Pre) || p == \at(b, Pre);
  loop invariant (p == \at(b, Pre) || p == \at(n, Pre));
  loop assigns p;
*/
while (1) {
      p = p+2;
      p = b;
  }

}
