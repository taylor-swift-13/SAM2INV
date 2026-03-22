int main1(){
  int p, pz, y0, hp, kf;

  p=40;
  pz=p;
  y0=p;
  hp=p;
  kf=p;

  while (1) {
      if (!(pz>=6)) {
          break;
      }
      y0 = y0 + 5;
      hp = hp + 3;
      kf = kf + 5;
      pz -= 6;
  }

}
