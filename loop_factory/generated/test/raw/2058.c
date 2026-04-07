int main1(){
  int jy, ws, k, o, ru;

  jy=1+25;
  ws=0;
  k=ws;
  o=-1;
  ru=jy;

  while (ws < jy) {
      ru--;
      ws = ws + 1;
      k = k*k+k;
      o = o+(ru%5);
  }

}
