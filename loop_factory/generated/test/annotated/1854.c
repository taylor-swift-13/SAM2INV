int main1(int z,int s){
  int uvz, f, p4, ys8, h, w6w, qq, ps;
  uvz=s;
  f=0;
  p4=0;
  ys8=0;
  h=0;
  w6w=0;
  qq=0;
  ps=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qq == 2*ys8 + 3*h + p4;
  loop invariant f >= 0;
  loop invariant ps >= 0;
  loop invariant w6w >= 0;
  loop invariant ys8 >= 0;
  loop invariant h >= 0;
  loop invariant p4 >= 0;
  loop invariant uvz == \at(s, Pre);
  loop invariant qq == 2*ys8 + 3*h + 4*w6w + p4;
  loop invariant qq >= f;
  loop invariant ps <= 5 * f;
  loop invariant (uvz >= 0) ==> (0 <= f && f <= uvz);
  loop invariant qq <= 4*f;
  loop invariant h <= f;
  loop invariant w6w <= f;
  loop invariant p4 <= f;
  loop assigns f, ps, s, p4, qq, h, w6w, ys8;
*/
while (f<=uvz-1) {
      if (!(!(f%8==0))) {
          if (f%6==0) {
              ys8++;
              qq += 2;
          }
          else {
              if (f%4==0) {
                  h += 1;
                  qq = qq + 3;
              }
              else {
                  if (1) {
                      w6w++;
                      qq += 4;
                  }
              }
          }
      }
      else {
          p4 += 1;
          qq++;
      }
      f = f + 1;
      ps = ps+f%6;
      s = s + uvz;
      s = s + s;
  }
}