int main1(int h,int g){
  int b, hx7, v10, aqs, ncn, wt, qp, qg6, uk9, ki3;

  b=h+7;
  hx7=0;
  v10=0;
  aqs=5;
  ncn=0;
  wt=hx7;
  qp=h;
  qg6=g;
  uk9=h+6;
  ki3=hx7;

  while (hx7<b) {
      ncn++;
      aqs++;
      if (aqs>=7) {
          aqs = aqs - 7;
          v10 += 1;
      }
      hx7 = hx7 + 1;
      if (hx7+2<=h+b) {
          g = ncn+11;
      }
      uk9 = uk9 + hx7;
      ki3 = ki3 + v10;
      uk9 = wt+qp+qg6;
      qg6 += 6;
      wt++;
  }

}
