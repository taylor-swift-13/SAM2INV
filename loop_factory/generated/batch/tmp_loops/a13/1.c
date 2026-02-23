int main1(int b,int p){
  int m, s, v, d;

  m=b+22;
  s=0;
  v=m;
  d=4;

  while (s+1<=m) {
      if (v+3<=m) {
          v = v+3;
      }
      else {
          v = m;
      }
      v = v+2;
  }

}
