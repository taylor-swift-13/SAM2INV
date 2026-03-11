int main1(int b,int m){
  int q, j, v, g, l, t;

  q=40;
  j=0;
  v=b;
  g=-6;
  l=3;
  t=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(b, Pre);
  loop invariant l == 3 + j * v;
  loop invariant 2 * g + 12 == 6 * j + v * j * (j - 1);
  loop invariant 0 <= j && j <= q;
  loop invariant 2*(g + 6 - 3*j) == v * j * (j - 1);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant g == -6 + 3*j + v * ((j*(j-1))/2);
  loop invariant v == b;
  loop invariant g == -6 + 3*j + v*(j*(j-1)/2);
  loop invariant j <= q;
  loop invariant j >= 0;
  loop invariant l == 3 + v * j;
  loop assigns g, l, j;
*/
while (j<q) {
      g = g+l;
      l = l+v;
      j = j+1;
  }

}
