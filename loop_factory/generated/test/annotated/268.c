int main1(int f,int g){
  int f6, k86, g1j, t;
  f6=f+17;
  k86=0;
  g1j=3;
  t=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= k86;
  loop invariant 3 <= g1j <= 8;
  loop invariant (t == 1) || (t == -1);
  loop invariant f6 == \at(f, Pre) + 17;
  loop assigns k86, g1j, t;
*/
while (k86<=f6-1) {
      if (g1j>=8) {
          t = -1;
      }
      if (g1j<=3) {
          t = 1;
      }
      k86++;
      g1j += t;
  }
}