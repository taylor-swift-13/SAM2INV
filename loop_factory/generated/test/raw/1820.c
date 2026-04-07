int main1(){
  int q, g3, d, igt, ldj, hp1;

  q=(1%21)+7;
  g3=0;
  d=g3;
  igt=0;
  ldj=q;
  hp1=(1%35)+8;

  while (1) {
      if (!(hp1>=1)) {
          break;
      }
      d = d+igt*igt;
      ldj = ldj+hp1*hp1;
      igt = (hp1*hp1)+(igt);
      hp1 -= 1;
      d = d*4;
  }

}
