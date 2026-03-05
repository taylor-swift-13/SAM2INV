int main1(int l,int k){
  int c, t, mb, fe1;

  c=68;
  t=0;
  mb=0;
  fe1=1;

  while (t<c) {
      if (mb>=6) {
          fe1 = -1;
      }
      if (mb<=0) {
          fe1 = 1;
      }
      mb += fe1;
      t += 1;
      l += fe1;
  }

}
