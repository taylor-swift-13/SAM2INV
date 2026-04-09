int main1(){
  int m, dmyt, l, czc, iy;
  m=1+21;
  dmyt=0;
  l=dmyt;
  czc=m;
  iy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dmyt >= 0;
  loop invariant dmyt <= m;
  loop invariant iy == dmyt;
  loop invariant l == dmyt;
  loop invariant czc == m + dmyt;
  loop assigns dmyt, czc, iy, l;
*/
while (dmyt < m) {
      dmyt += 1;
      czc += 1;
      iy++;
      l = l + 1;
  }
}