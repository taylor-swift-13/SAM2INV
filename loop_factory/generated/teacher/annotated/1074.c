int main1(int b,int n){
  int x, a, p;

  x=20;
  a=0;
  p=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 0 && x == 20 && n == \at(n, Pre) && b == \at(b, Pre);

  loop invariant n == \at(n, Pre) && b == \at(b, Pre);
  loop invariant p >= 0;

  loop invariant a == 0;
  loop invariant x == 20;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant a == 0 && x == 20;

  loop invariant x == 20 && n == \at(n, Pre) && b == \at(b, Pre);
  loop assigns p;
*/
while (1) {
      p = p+4;
      if (a+4<=n+x) {
          p = p*p;
      }
  }

}
