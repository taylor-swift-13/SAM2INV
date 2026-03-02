int main1(int m,int p){
  int e, g, v;

  e=(p%15)+14;
  g=0;
  v=p;

  while (1) {
      v = v+2;
      if (v*v<=e+3) {
          v = v*v+v;
      }
      v = v*v+v;
  }

}
