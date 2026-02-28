int main1(int b,int m,int n,int q){
  int g, l, j, f, s, o, v;

  g=70;
  l=g;
  j=0;
  f=1;
  s=6;
  o=0;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 6 + 4*o && (o == 0 ==> f == 1) && (o > 0 ==> f == 2*o) && 0 <= o <= g + 1;
  loop invariant j % 3 == 0;
  loop invariant s == 6 + 4*o;
  loop invariant q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant g == 70;
  loop invariant f >= 1;
  loop invariant o <= g + 1;
  loop invariant o == 0 ==> f == 1;
  loop invariant o >= 0;
  loop invariant s >= 6;
  loop invariant s <= 6 + 4*(g + 1);
  loop invariant f >= 0;
  loop invariant f <= s;
  loop assigns o, j, f, s;
*/
while (o<=g) {
      o = o+1;
      j = j+f;
      f = f+s;
      s = s+4;
      j = j*3;
      f = f/3;
  }

}
