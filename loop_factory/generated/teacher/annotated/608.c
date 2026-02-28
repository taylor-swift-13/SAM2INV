int main1(int k,int n){
  int c, m, g, i;

  c=8;
  m=1;
  g=-3;
  i=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 8;
  loop invariant m == 1;
  loop invariant g >= -3;
  loop invariant i >= n;
  loop invariant m <= c - 3;
  loop invariant i - n == ((g + 3) / 2) * (((g + 3) / 2) - 1);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant m >= 1;
  loop invariant i == n + ((g + 3) * (g + 1)) / 4;
  loop invariant 4*(i - n) == (g+3)*(g+1);
  loop assigns g, i;
*/
while (m<=c-3) {
      g = g+1;
      i = i+1;
      g = g+1;
      i = i+g;
  }

}
