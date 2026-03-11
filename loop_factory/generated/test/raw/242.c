int main1(int z,int f){
  int a, li4, c4q, oam, xp;

  a=(f%38)+16;
  li4=a;
  c4q=3;
  oam=0;
  xp=z;

  while (1) {
      if (!(li4-4>=0)) {
          break;
      }
      oam += c4q;
      z += 2;
      li4++;
  }

  while (xp>4) {
      oam = oam+a*xp;
      z += xp;
      xp = 4;
  }

}
