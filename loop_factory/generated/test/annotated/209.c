int main1(int n){
  int fn6, l2g, m, l, yw;
  fn6=50;
  l2g=0;
  m=-1;
  l=0;
  yw=fn6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yw == l + fn6 + m + 1;
  loop invariant l == (m*m - m - 2)/2;
  loop invariant m <= fn6;
  loop invariant yw == fn6 + m*(m+1)/2;
  loop invariant yw - l - m == 51;
  loop assigns l, m, yw;
*/
while (m<=fn6-1) {
      l = l + m;
      m++;
      yw = yw + m;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m - yw * l2g == fn6;
  loop invariant l2g <= yw;
  loop invariant l + l2g <= yw + 1;
  loop invariant m >= 50;
  loop invariant m % yw == 50;
  loop invariant m == 50 + yw * l2g;
  loop assigns l, l2g, m;
*/
while (l2g<yw) {
      l = yw-l2g;
      l2g = l2g + 1;
      m += yw;
  }
}