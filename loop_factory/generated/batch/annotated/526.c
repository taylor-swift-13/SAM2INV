int main1(int b,int m){
  int s, q, f, g;

  s=69;
  q=0;
  f=s;
  g=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 69;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q >= 0;
  loop invariant g <= m;
  loop invariant f <= q + 69;
  loop invariant ((q == 0 && f == 69) || f == q - 1);
  loop invariant g + q == \at(m, Pre);
  loop invariant g == m - q;
  loop invariant f == 69 || f == q - 1;
  loop invariant 0 <= q;
  loop invariant 0 <= f;
  loop invariant g + q == m;
  loop invariant f >= 0;
  loop assigns f, g, q;
*/
while (1) {
      f = f+1;
      g = g-1;
      f = q;
      q = q+1;
  }

}
