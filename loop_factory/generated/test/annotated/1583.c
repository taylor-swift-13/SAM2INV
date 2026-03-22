int main1(int b,int f){
  int zu, hs, dzb, dj, q, i, vp, nvv;
  zu=f*2;
  hs=0;
  dzb=b;
  dj=11;
  q=-6;
  i=zu;
  vp=-1;
  nvv=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dj - 11 == i - zu;
  loop invariant (hs == 0) || (hs == zu);
  loop invariant zu == 2 * \at(f, Pre);
  loop invariant (i == zu) || (i == zu + 1);
  loop invariant (hs == 0) || (nvv == i + vp + q);
  loop invariant vp >= -1;
  loop invariant f >= \at(f, Pre);
  loop invariant b >= \at(b, Pre);
  loop invariant (hs <= zu-1) ==> dj == 11;
  loop invariant dzb - \at(b, Pre) == dj - 11;
  loop assigns dj, dzb, f, vp, b, i, nvv, hs;
*/
while (hs<=zu-1) {
      dj += 1;
      dzb += 1;
      if (dj<b+4) {
          f += 4;
      }
      if ((hs%7)==0) {
          f = f + hs;
      }
      vp += dj;
      b += dj;
      i = i + 1;
      nvv = (i+vp)+(q);
      hs = zu;
      if (hs+5<=q+zu) {
          f = f + 1;
      }
  }
}