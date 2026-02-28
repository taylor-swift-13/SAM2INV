int main1(int b,int m){
  int p, c, a, v, s, n;

  p=b-10;
  c=0;
  a=-8;
  v=c;
  s=b;
  n=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == -8;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == b - 10;
  loop invariant v <= 0;
  loop invariant v % 8 == 0;
  loop invariant p == \at(b, Pre) - 10;
  loop assigns v;
*/
while (1) {
      v = v+a;
  }

}
