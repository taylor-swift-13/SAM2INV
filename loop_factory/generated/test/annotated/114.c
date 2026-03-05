int main1(int w){
  int u, wu, n8;
  u=54;
  wu=0;
  n8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= wu;
  loop invariant wu <= u;
  loop invariant w == \at(w, Pre);
  loop invariant (wu == 0 ==> n8 == 0) && (wu >= 1 ==> n8 == 1);
  loop invariant u == 54;
  loop assigns wu, n8;
*/
for (; wu<u; wu += 1) {
      n8++;
      if (n8>=2) {
          n8 -= 2;
          n8++;
      }
  }
}