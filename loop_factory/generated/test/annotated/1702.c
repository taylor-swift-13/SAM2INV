int main1(int n){
  int v, c, bb, g;
  v=n;
  c=0;
  bb=0;
  g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bb == 3 * c;
  loop invariant g == (c % 3);
  loop invariant v == \at(n, Pre);
  loop invariant n == v + c*(c+1)/2;
  loop invariant c >= 0;
  loop assigns bb, c, g, n;
*/
while (c < v) {
      g = (g + 1) % 3;
      bb = bb + 3;
      c = c + 1;
      n = n + c;
  }
}