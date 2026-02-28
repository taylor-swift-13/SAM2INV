int main1(int b,int m){
  int o, n, v, j, a;

  o=b+20;
  n=o;
  v=-4;
  j=0;
  a=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -4 + (o - n);
  loop invariant j == (o - n) * (-4) + (o - n) * ((o - n) + 1) / 2;
  loop invariant o - n >= 0;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant o == b + 20;
  loop invariant n == o - v - 4;
  loop invariant j == (v + 4) * (v - 3) / 2;
  loop invariant v >= -4;
  loop invariant v == o - n - 4;
  loop invariant j == ((o - n) * (o - n - 7)) / 2;
  loop invariant n <= o;
  loop invariant v + n == \at(b, Pre) + 16;
  loop invariant 2*j == (\at(b, Pre) + 20 - n) * (\at(b, Pre) + 13 - n);

  loop invariant j == (o - n) * (o - n - 7) / 2;

  loop assigns v, j, n;
*/
while (n>0) {
      v = v+1;
      j = j+v;
      n = n-1;
  }

}
