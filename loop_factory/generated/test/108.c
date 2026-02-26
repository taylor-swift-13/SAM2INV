int main108(int k,int m,int p){
  int r, d, v, s;

  r=k;
  d=r+2;
  v=p;
  s=d;

  while (1) {
      if (d>=r) {
          break;
      }
      v = v+2;
      d = d+1;
  }

  while (v-1>=0) {
      s = s*3+3;
      r = r*s+3;
      s = s*s+s;
  }

  while (v-1>=0) {
      d = d+r;
  }

}
