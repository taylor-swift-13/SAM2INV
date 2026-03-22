int main1(){
  int l36, wm, lv, fs, h, z;

  l36=1;
  wm=0;
  lv=0;
  fs=0;
  h=l36;
  z=l36;

  while (1) {
      if (!(fs<l36)) {
          break;
      }
      lv++;
      fs++;
      h = h*h+h;
      z = z + fs;
  }

  while (fs<h) {
      fs++;
      wm = wm + 1;
      lv = lv + fs;
  }

}
