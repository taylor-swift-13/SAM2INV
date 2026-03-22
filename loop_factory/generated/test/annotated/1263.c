int main1(int k){
  int w, nm, vr, hqz, g9;
  w=60;
  nm=2;
  vr=-5;
  hqz=1;
  g9=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2 <= nm <= w + 1;
  loop invariant g9 == w * (nm - 1);
  loop invariant hqz > 0;
  loop invariant g9 == 60 + w * (nm - 2);
  loop invariant vr <= -5;
  loop assigns vr, hqz, g9, nm;
*/
while (nm<=w) {
      vr = vr*nm;
      if (nm<w) {
          hqz = hqz*nm;
      }
      g9 = g9 + w;
      nm = nm + 1;
  }
}