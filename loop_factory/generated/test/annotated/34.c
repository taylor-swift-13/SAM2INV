int main1(int t,int g,int x){
  int aw, ep, zx;
  aw=t-5;
  ep=0;
  zx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ep >= 0;
  loop invariant zx == 4*ep;
  loop invariant t == \at(t,Pre) + ep;
  loop invariant g == \at(g,Pre) + aw*ep;
  loop invariant x == \at(x,Pre);
  loop invariant aw == \at(t,Pre) - 5;
  loop invariant 0 <= ep;
  loop invariant aw == \at(t, Pre) - 5 && 0 <= ep && (ep <= aw || aw < 0);
  loop assigns ep, zx, g, t;
*/
while (ep<aw) {
      zx += 4;
      ep = ep + 1;
      g += aw;
      t += 1;
  }
}