int main1(){
  int s2o, a63x, gt, c2, kuj;

  s2o=1;
  a63x=0;
  gt=0;
  c2=0;
  kuj=2;

  while (gt<s2o) {
      gt = gt + 1;
      a63x++;
      c2 = c2 + gt;
  }

  while (1) {
      if (!(a63x+1<=gt)) {
          break;
      }
      c2 += kuj;
      kuj = kuj+gt-a63x;
      gt = (a63x+1)-1;
  }

}
