int main1(int s,int l){
  int z, pl, xzu, thr;
  z=l+22;
  pl=0;
  xzu=0;
  thr=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s, Pre) + xzu*(xzu+1)/2;
  loop invariant thr == l + 3*xzu;
  loop invariant pl == xzu % 7;
  loop invariant 0 <= xzu && (z < 0 || xzu <= z);
  loop invariant z == \at(l, Pre) + 22;
  loop invariant z == l + 22;
  loop assigns s, thr, pl, xzu;
*/
while (1) {
      if (!(xzu<=z-1)) {
          break;
      }
      thr = thr + 3;
      pl = (pl+1)%7;
      xzu += 1;
      s = s + xzu;
  }
}