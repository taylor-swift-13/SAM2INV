int main1(){
  int wp, jx, h9g, cb, hl, jb, vgd;

  wp=1+15;
  jx=0;
  h9g=1;
  cb=1;
  hl=0;
  jb=7;
  vgd=0;

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
