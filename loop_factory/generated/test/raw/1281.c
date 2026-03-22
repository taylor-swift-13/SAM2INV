int main1(int b){
  int pf, ul, fu, s, qd, hp;

  pf=b-8;
  ul=pf;
  fu=0;
  s=0;
  qd=0;
  hp=7;

  while (ul<pf) {
      s = ul%5;
      if (!(!(ul>=hp))) {
          qd = (ul-hp)%5;
          fu = fu+s-qd;
      }
      else {
          fu = fu + s;
      }
      ul = ul + 1;
      hp = hp + s;
  }

}
