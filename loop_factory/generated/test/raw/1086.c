int main1(int d,int t){
  int ad, aw0, ro, t5;

  ad=t;
  aw0=0;
  ro=(d%28)+10;
  t5=d;

  while (ro>aw0) {
      ro -= aw0;
      aw0 = aw0 + 1;
      t5++;
      t5 = t5*2+5;
      d += aw0;
  }

  while (t5>ad) {
      t5 = t5 - ad;
      ad += 1;
      t = t+(t5%5);
      d = (ro)+(d);
  }

}
