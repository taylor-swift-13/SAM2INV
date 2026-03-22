int main1(int e){
  int hk, clv, q;

  hk=(e%14)+13;
  clv=0;
  q=hk;

  while (1) {
      if (!(clv<hk)) {
          break;
      }
      q += 1;
      e = e + clv;
      clv = hk;
  }

}
