int main1(){
  int w, xs, sb, h26, wlm, r, mcu, s4;

  w=148;
  xs=0;
  sb=-4;
  h26=-4;
  wlm=-2;
  r=6;
  mcu=0;
  s4=0;

  while (1) {
      if (!(xs < w)) {
          break;
      }
      xs++;
      if ((xs < w / 3)) {
          sb = sb + 1;
      }
      if ((xs < (2*w)/3)) {
          h26 += 2;
      }
      else {
          s4 = sb;
      }
      mcu++;
      wlm = wlm + sb;
      r += h26;
      wlm = wlm+r+mcu;
      wlm = wlm + 1;
  }

}
