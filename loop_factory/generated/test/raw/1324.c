int main1(int g,int x){
  int lxch, d928, ub, w3i, nh, bq;

  lxch=x+16;
  d928=lxch+3;
  ub=0;
  w3i=(g%28)+10;
  nh=g;
  bq=d928;

  while (1) {
      if (!(w3i>ub)) {
          break;
      }
      w3i = w3i - ub;
      bq = bq+(w3i%7);
      nh = (1)+(nh);
      ub += 1;
  }

}
