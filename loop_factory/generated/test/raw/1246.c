int main1(int h){
  int u, jxd, nu4, rgh, p4, q;

  u=(h%18)+7;
  jxd=u;
  nu4=2;
  rgh=u;
  p4=-2;
  q=1;

  while (jxd-1>=0) {
      rgh = rgh + 1;
      nu4 = nu4+rgh*rgh*rgh*rgh;
      q = q+(nu4%5);
      p4 = p4*2;
      jxd += 1;
  }

}
