int main1(){
  int dmb, ac, kkx1, s, la, jt;

  dmb=61;
  ac=0;
  kkx1=0;
  s=0;
  la=0;
  jt=0;

  while (kkx1<dmb) {
      s = s + kkx1;
      la++;
      jt += ac;
      kkx1 += 1;
  }

  while (1) {
      la++;
      kkx1 = kkx1 + s;
      dmb = dmb + la;
      kkx1 += 1;
      jt--;
      ac++;
      if (ac>=s) {
          break;
      }
  }

}
