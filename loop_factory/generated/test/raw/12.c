int main1(int w,int u,int v){
  int j, i, vc, pn;

  j=68;
  i=j;
  vc=5;
  pn=11;

  while (i<j) {
      vc += 6;
      pn += 6;
      i = i + 1;
      u = (u+pn)%6;
  }

}
