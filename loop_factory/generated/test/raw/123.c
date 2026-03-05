int main1(){
  int g, vxjm, f;

  g=1-2;
  vxjm=g;
  f=1;

  while (vxjm<g) {
      if (f>=6) {
          f = -1;
      }
      if (f<=0) {
          f = 1;
      }
      f += f;
      vxjm = vxjm + 1;
      f += f;
  }

}
