int main1(int b,int p){
  int n, t, u;

  n=(b%8)+9;
  t=0;
  u=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == (b%8) + 9;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u % 2 == 0;
  loop invariant u >= 0;
  loop invariant 2 <= n;
  loop invariant n <= 16;
  loop invariant n == (\at(b,Pre) % 8) + 9;
  loop assigns u;
*/
while (n>=n) {
      u = u+2;
  }

}
