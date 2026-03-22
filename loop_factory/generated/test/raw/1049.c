int main1(){
  int kt, bg, iq, h3, wss, f3b;

  kt=1;
  bg=kt;
  iq=0;
  h3=0;
  wss=11;
  f3b=bg;

  while (1) {
      if (!(h3<=kt-1)) {
          break;
      }
      wss = wss + bg;
      iq += 1;
      h3 += 1;
      f3b = f3b + wss;
  }

  while (1) {
      if (!(h3<bg)) {
          break;
      }
      f3b += 1;
      kt += iq;
      h3 += 1;
  }

}
