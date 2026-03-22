int main1(int x){
  int lsb, j79, d, rvc, er, o919;

  lsb=x-7;
  j79=0;
  d=0;
  rvc=0;
  er=0;
  o919=5;

  while (1) {
      if (!(j79<lsb)) {
          break;
      }
      rvc = j79%5;
      if (!(!(j79>=o919))) {
          er = (j79-o919)%5;
          d = d+rvc-er;
      }
      else {
          d = d + rvc;
      }
      j79 += 1;
      o919 = o919 + rvc;
  }

}
