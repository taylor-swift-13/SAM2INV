int main1(int m){
  int h9ev, i38, b, yh, q, o, y, s6, aeo, wzv;

  h9ev=m;
  i38=0;
  b=m;
  yh=h9ev;
  q=h9ev;
  o=i38;
  y=i38;
  s6=-8;
  aeo=m;
  wzv=m;

  while (i38 < h9ev) {
      b = b + ((i38 % 4) == 0);
      yh = yh + ((i38 % 4) == 1);
      o = o + ((i38 % 4) == 3);
      q = q + ((i38 % 4) == 2);
      i38 += 1;
      if ((i38%6)==0) {
          wzv = aeo-wzv;
      }
      if (q<o+1) {
          wzv += 1;
      }
      y++;
      s6 += 2;
      aeo = (3)+(aeo);
      m = m + q;
      aeo += i38;
  }

}
