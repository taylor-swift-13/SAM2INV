int main1(int m,int p){
  int n, y, v, l;

  n=(m%39)+18;
  y=0;
  v=m;
  l=m;

  while (1) {
      if (y>=n) {
          break;
      }
      v = v+3;
      y = y+1;
      v = v+2;
      l = l+3;
      l = v-l;
      v = v+1;
  }

}
