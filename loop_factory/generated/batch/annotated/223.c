int main1(int n,int q){
  int s, i, g, v;

  s=14;
  i=0;
  g=n;
  v=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 14;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i <= s - 1;

  loop invariant i == 0;
  loop invariant s == 14 && i >= 0 && i <= s - 1 && ((g <= s) || (g <= n));
  loop invariant (g == s) || ((g - n) % 5 == 0);
  loop invariant i <= s;
  loop invariant g == \at(n, Pre) || g <= s;
  loop invariant (n <= s) ==> (g >= n);
  loop invariant (n > s) ==> (g >= s);
  loop assigns g;
*/
while (i+1<=s) {
      if (g+5<=s) {
          g = g+5;
      }
      else {
          g = s;
      }
  }

}
