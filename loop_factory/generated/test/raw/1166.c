int main1(){
  int ct, tx, cvd, djr, la;

  ct=1+3;
  tx=0;
  cvd=(1%28)+10;
  djr=ct;
  la=8;

  while (cvd>tx) {
      cvd -= tx;
      tx += 1;
      la = la + 3;
      djr = djr+(tx%8);
  }

}
