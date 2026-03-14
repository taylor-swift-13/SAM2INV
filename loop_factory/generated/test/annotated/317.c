int main1(){
  int v, j, u, i3o;
  v=1+8;
  j=0;
  u=5;
  i3o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i3o <= v;
  loop invariant (u == i3o + 5);
  loop invariant i3o >= 0;
  loop assigns u, i3o;
*/
while (1) {
      if (!(i3o<v)) {
          break;
      }
      u = u + 1;
      i3o = i3o + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u - j == 14;
  loop invariant (j <= i3o);
  loop invariant u == 5 + i3o + j;
  loop invariant j >= 0;
  loop assigns u, j;
*/
while (1) {
      if (!(j<=i3o-1)) {
          break;
      }
      j++;
      u = u + 1;
  }
}