int main1(){
  int kb0p, li, x, aw, s2, w2;

  kb0p=1;
  li=0;
  x=5;
  aw=li;
  s2=kb0p;
  w2=kb0p;

  while (1) {
      if (!(li<kb0p)) {
          break;
      }
      x = aw+s2+w2;
      li = li + 1;
      s2 = s2 + w2;
      aw += x;
  }

}
