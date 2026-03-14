int main1(int w){
  int b21, i, vj, r, vdu, v;

  b21=w;
  i=0;
  vj=31;
  r=0;
  vdu=1;
  v=0;

  while (vj>0&&i<b21) {
      if (vj<=vdu) {
          v = vj;
      }
      else {
          v = vdu;
      }
      i = i + 1;
      vj -= v;
      vdu += 1;
      r += v;
  }

}
