int main1(){
  int hr, r, f, hwf, i3v, v;
  hr=10;
  r=0;
  f=1;
  hwf=0;
  i3v=0;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == f * r;
  loop invariant i3v == 2 * r;
  loop invariant 0 <= r <= hr;
  loop invariant 0 <= hwf <= hr;
  loop invariant v == r;
  loop invariant f == 1;
  loop invariant hwf <= hr - r;
  loop assigns v, i3v, r, hwf;
*/
while (1) {
      if (!(r < hr)) {
          break;
      }
      v = (f)+(v);
      i3v += 2;
      r = r + 1;
      hwf = hr - r;
  }
}