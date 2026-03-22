int main1(){
  int qrs, ys, p3, iqy, epg;
  qrs=1;
  ys=qrs;
  p3=0;
  iqy=0;
  epg=qrs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iqy == p3;
  loop invariant qrs == 1;
  loop invariant ys == 1;
  loop invariant epg == 1 + (iqy*(iqy + 3))/2;
  loop invariant iqy <= qrs;
  loop assigns iqy, p3, epg;
*/
while (1) {
      if (!(iqy<qrs)) {
          break;
      }
      iqy = iqy + 1;
      p3++;
      epg = epg + p3;
      epg += ys;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant epg > 0;
  loop invariant ys >= 1;
  loop assigns qrs, iqy, ys, p3;
*/
while (1) {
      if (!(epg*4<=p3)) {
          break;
      }
      qrs += epg;
      iqy = iqy+ys*epg;
      ys = ys*3;
      p3 = (epg*4)-1;
  }
}