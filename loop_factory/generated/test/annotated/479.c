int main1(){
  int i, e1r, y, od, oy, kt;
  i=(1%39)+10;
  e1r=0;
  y=0;
  od=i;
  oy=0;
  kt=e1r;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oy == 2*y;
  loop invariant 0 <= od;
  loop invariant od <= i;
  loop invariant 0 <= y <= i;
  loop assigns od, y, oy;
*/
while (1) {
      if (!(y+1<=i)) {
          break;
      }
      if (oy<i) {
          od = y;
      }
      y++;
      oy += 2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kt == i * (oy - 2*i);
  loop invariant kt % i == 0;
  loop invariant oy >= 4;
  loop assigns kt, oy;
*/
while (oy-4>=0) {
      kt = kt + i;
      oy++;
  }
}