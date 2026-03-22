int main1(int s){
  int i5, lq, re, cv, y, c8, a;

  i5=s-6;
  lq=i5+3;
  re=0;
  cv=(s%28)+10;
  y=0;
  c8=i5;
  a=lq;

  while (cv>re) {
      cv = cv - re;
      re += 1;
      c8 = c8 + lq;
      y++;
      a = a + re;
  }

  while (y>c8) {
      y = y - c8;
      c8 += 1;
      s = s+(y%8);
      s = s*s;
  }

}
