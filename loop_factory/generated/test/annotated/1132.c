int main1(){
  int wp, jx, h9g, cb, hl, jb, vgd;
  wp=1+15;
  jx=0;
  h9g=1;
  cb=1;
  hl=0;
  jb=7;
  vgd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vgd == jx;
  loop invariant 0 <= jx <= wp;
  loop invariant 0 <= h9g <= jb;
  loop invariant 1 <= cb <= wp + 1;
  loop invariant 0 <= hl <= wp;
  loop invariant cb <= jx + 1;
  loop invariant h9g + hl == cb;
  loop assigns h9g, hl, cb, jx, vgd;
*/
while (jx<wp) {
      if (!(!(jx%3==0))) {
          if (h9g>0) {
              h9g--;
              hl += 1;
          }
      }
      else {
          if (h9g<jb) {
              h9g = h9g + 1;
              cb += 1;
          }
      }
      jx++;
      vgd = vgd + 1;
  }
}