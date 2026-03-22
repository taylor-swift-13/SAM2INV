int main1(int h){
  int yuf8, iz, zue, o9f, xf;

  yuf8=18;
  iz=0;
  zue=h;
  o9f=iz;
  xf=iz;

  while (1) {
      if (!(iz<yuf8)) {
          break;
      }
      zue = zue*3;
      o9f = o9f/3;
      xf = xf*2+(o9f%6)+2;
      iz = yuf8;
  }

}
