int main1(){
  int oc, z, dy, hd, ty, dxl5, c61;
  oc=102;
  z=oc;
  dy=-5;
  hd=oc;
  ty=z;
  dxl5=(1%35)+8;
  c61=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ty == 387 - (dxl5*(dxl5+1)*(2*dxl5+1))/6;
  loop invariant ty == hd;
  loop invariant dy >= -5;
  loop invariant 0 <= dxl5 <= (1%35 + 8);
  loop invariant c61 >= 102;
  loop assigns c61, dy, hd, ty, dxl5;
*/
while (1) {
      if (!(dxl5>0)) {
          break;
      }
      ty = ty+dxl5*dxl5;
      dy = dy+hd*hd;
      hd = (dxl5*dxl5)+(hd);
      c61 = c61 + ty;
      dxl5--;
  }
}