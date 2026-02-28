int main1(int a,int m,int p){
  int n, e, l, c, g, t;

  n=a+9;
  e=0;
  l=m;
  c=6;
  g=-1;
  t=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l >= m;
  loop invariant (l - m) % 6 == 0;
  loop invariant g == -1;
  loop invariant n == \at(a,Pre) + 9;
  loop invariant a == \at(a,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant n == a + 9;
  loop invariant (c == 6) || (c == -1);
  loop invariant g <= c;
  loop invariant (l - \at(m, Pre)) % 6 == 0;
  loop assigns c, l;
*/
while (1) {
      if (l>=n) {
          break;
      }
      if (g<=c) {
          c = g;
      }
      l = l+1;
      l = l+5;
  }

}
