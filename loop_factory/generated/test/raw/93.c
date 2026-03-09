int main1(){
  int s7tr, is, seso, y, u, msx2;

  s7tr=1-8;
  is=0;
  seso=1;
  y=0;
  u=is;
  msx2=is;

  while (seso<=s7tr) {
      seso = 2*seso;
      u = u + 1;
      y++;
      msx2 = msx2*3+(seso%2)+0;
  }

}
