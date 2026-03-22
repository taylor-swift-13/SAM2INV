int main1(){
  int oc, z, dy, hd, ty, dxl5, c61;

  oc=102;
  z=oc;
  dy=-5;
  hd=oc;
  ty=z;
  dxl5=(1%35)+8;
  c61=z;

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
