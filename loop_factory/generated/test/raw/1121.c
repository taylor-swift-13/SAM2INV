int main1(int a,int y){
  int o, bsu, j, ts, oc;

  o=9;
  bsu=o;
  j=0;
  ts=0;
  oc=a;

  while (bsu-2>=0) {
      ts += j;
      j += 2;
      bsu = bsu + 1;
  }

  while (bsu<oc) {
      o = o + a;
      bsu = bsu + 1;
      ts += j;
  }

}
