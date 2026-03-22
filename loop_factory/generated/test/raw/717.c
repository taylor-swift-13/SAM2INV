int main1(){
  int hlt, ckx, s2, q6;

  hlt=(1%23)+9;
  ckx=(1%40)+2;
  s2=0;
  q6=hlt;

  while (ckx!=s2) {
      s2 = ckx;
      ckx = (ckx+hlt/ckx)/2;
      q6 = q6+ckx-s2;
  }

}
