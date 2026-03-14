int main1(int e,int f){
  int pg, qn2, jq, lx;

  pg=f;
  qn2=2;
  jq=0;
  lx=pg;

  while (jq<=pg-1) {
      qn2 = qn2 + e;
      jq = jq + 1;
      lx = lx + jq;
  }

  while (jq<=pg-1) {
      jq = jq + 1;
      qn2 = qn2 + e;
      e = e+pg-lx;
  }

}
