int main1(int k){
  int n, g, i;

  n=10;
  g=n;
  i=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(k, Pre) + (n - g);
  loop invariant g >= 0;
  loop invariant g <= n;
  loop invariant k == \at(k, Pre);
  loop invariant i + g == k + 10;
  loop invariant i >= k;
  loop invariant i + g == \at(k, Pre) + 10;
  loop invariant i <= \at(k, Pre) + 10;
  loop invariant i + g == \at(k, Pre) + n;
  loop invariant 0 <= g;
  loop invariant \at(k, Pre) <= i;
  loop invariant i <= \at(k, Pre) + n;
  loop invariant n == 10;
  loop invariant g <= 10;
  loop invariant i - k >= 0;
  loop invariant i - k <= 10;
  loop assigns i, g;
*/
while (g>0) {
      i = i+1;
      g = g-1;
  }

}
